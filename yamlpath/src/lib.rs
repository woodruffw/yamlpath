//! Comment and format-preserving YAML path queries.
//!
//! This is **not** "XPath but for YAML". If you need a generic object
//! query language that **doesn't** capture exact parse spans or comments,
//! then you probably want an implementation of [JSONPath] or something
//! like [jq].
//!
//! [JSONPath]: https://en.wikipedia.org/wiki/JSONPath
//! [jq]: https://jqlang.github.io/jq/

#![deny(rustdoc::broken_intra_doc_links)]
#![deny(missing_docs)]
#![allow(clippy::redundant_field_names)]
#![forbid(unsafe_code)]

use thiserror::Error;
use tree_sitter::{Node, Parser, Tree};

/// Possible errors when performing YAML path queries.
#[derive(Error, Debug)]
pub enum QueryError {
    /// The tree-sitter backend couldn't accept the YAML grammar.
    #[error("malformed or unsupported tree-sitter grammar")]
    InvalidLanguage(#[from] tree_sitter::LanguageError),
    /// The user's input YAML is malformed.
    #[error("input is not valid YAML")]
    InvalidInput,
    /// The query expects a key at a given point, but the input isn't a mapping.
    #[error("expected mapping containing key `{0}`")]
    ExpectedMapping(String),
    /// The query expects a list index at a given point, but the input isn't a list.
    #[error("expected list for index `[{0}]`")]
    ExpectedList(usize),
    /// The query expects the given key in a mapping, but the mapping doesn't have that key.
    #[error("mapping has no key `{0}`")]
    ExhaustedMapping(String),
    /// The query expects the given list index, but the list isn't the right size.
    #[error("index `[{0}]` exceeds list size ({1})")]
    ExhaustedList(usize, usize),
    /// The YAML syntax tree wasn't structured the way we expect.
    #[error("unexpected node: `{0}`")]
    UnexpectedNode(String),
    /// The YAML syntax tree is missing an expected named child node.
    #[error("syntax node `{0}` is missing named child")]
    MissingChild(String),
    /// The YAML syntax tree is missing an expected named child node with
    /// the given field name.
    #[error("syntax node `{0}` is missing child field `{1}`")]
    MissingChildField(String, &'static str),
}

/// A query into some YAML document.
///
/// Internally, a query is one or more "component" selectors, each of which
/// is either a mapping key or list index to descend through.
///
/// For example, with the following YAML document:
///
/// ```yaml
/// foo:
///   bar:
///     baz:
///       - [a, b, c]
///       - [d, e, f]
/// ```
///
/// The sub-list member `e` would be identified via the path
/// `foo`, `bar`, `baz`, `1`, `1`.
pub struct Query {
    /// The individual top-down components of this query.
    route: Vec<Component>,
}

impl Query {
    /// Constructs a new query from the given path components.
    ///
    /// Returns `None` if the component list is empty.
    pub fn new(route: Vec<Component>) -> Option<Self> {
        if route.is_empty() {
            None
        } else {
            Some(Self { route })
        }
    }
}

/// A single `Query` component.
#[derive(Debug, PartialEq)]
pub enum Component {
    /// A YAML key.
    Key(String),

    /// An index into a YAML array.
    Index(usize),
}

/// Represents the concrete location of some YAML syntax.
#[derive(Debug)]
pub struct Location {
    /// The byte span at which the query's result appears.
    pub byte_span: (usize, usize),
    /// The "point" (i.e., line/column) span at which the query's result appears.
    pub point_span: ((usize, usize), (usize, usize)),
}

impl From<Node<'_>> for Location {
    fn from(node: Node<'_>) -> Self {
        let start_point = node.start_position();
        let end_point = node.end_position();

        Self {
            byte_span: (node.start_byte(), node.end_byte()),
            point_span: (
                (start_point.row, start_point.column),
                (end_point.row, end_point.column),
            ),
        }
    }
}

/// Represents the result of a successful query.
#[derive(Debug)]
pub struct Feature {
    /// The exact location of the query result.
    pub location: Location,

    /// The "context" location for the quest result.
    /// This is typically the surrounding mapping or list structure.
    pub context: Option<Location>,
}

/// Represents a queryable YAML document.
pub struct Document<'a> {
    source: &'a str,
    tree: Tree,
    document_id: u16,
    _block_node_id: u16,
    flow_node_id: u16,
    // A "block" sequence, i.e. a YAML-style array (`- foo\n-bar`)
    block_sequence_id: u16,
    // A "flow" sequence, i.e. a JSON-style array (`[foo, bar]`)
    flow_sequence_id: u16,
    // A "block" mapping, i.e. a YAML-style map (`foo: bar`)
    block_mapping_id: u16,
    // A "flow" mapping, i.e. a JSON-style map (`{foo: bar}`)
    flow_mapping_id: u16,
    block_mapping_pair_id: u16,
    _flow_pair_id: u16,
    block_sequence_item_id: u16,
}

impl<'a> Document<'a> {
    /// Construct a new `Document` from the given YAML.
    pub fn new(source: &'a str) -> Result<Self, QueryError> {
        let mut parser = Parser::new();
        let language = tree_sitter_yaml::language();
        parser.set_language(&language)?;

        // NOTE: Infallible, assuming `language` is correctly constructed above.
        let tree = parser.parse(source, None).unwrap();

        if tree.root_node().has_error() {
            return Err(QueryError::InvalidInput);
        }

        Ok(Self {
            source,
            tree,
            document_id: language.id_for_node_kind("document", true),
            _block_node_id: language.id_for_node_kind("block_node", true),
            flow_node_id: language.id_for_node_kind("flow_node", true),
            block_sequence_id: language.id_for_node_kind("block_sequence", true),
            flow_sequence_id: language.id_for_node_kind("flow_sequence", true),
            block_mapping_id: language.id_for_node_kind("block_mapping", true),
            flow_mapping_id: language.id_for_node_kind("flow_mapping", true),
            block_mapping_pair_id: language.id_for_node_kind("block_mapping_pair", true),
            _flow_pair_id: language.id_for_node_kind("flow_pair", true),
            block_sequence_item_id: language.id_for_node_kind("block_sequence_item", true),
        })
    }

    /// Perform a query on the current document, returning a `Feature`
    /// if the query succeeds.
    pub fn query(&self, query: &Query) -> Result<Feature, QueryError> {
        let node = self.query_node(query)?;

        // TODO: Figure out comment extraction. This is made annoying
        // by the fact that comments aren't parented in obvious places on
        // the tree, e.g. `[a, b, [c]] # foo` has a comment adjacent to the
        // top sequence when we may be querying for the `c` in the innermost
        // sequence.

        Ok(Feature {
            location: Location::from(node),
            context: node.parent().map(Location::from),
        })
    }

    /// Returns a slice of the original document corresponding to the given
    /// `Feature`.
    ///
    /// Panics if the feature's span is invalid.
    pub fn extract(&self, feature: &Feature) -> &str {
        &self.source[feature.location.byte_span.0..feature.location.byte_span.1]
    }

    fn query_node(&self, query: &Query) -> Result<Node, QueryError> {
        // All tree-sitter-yaml trees start with a `stream` node.
        let stream = self.tree.root_node();

        // The `document` child is the "body" of the YAML document; it
        // might not be the first node in the `stream` if there are comments.
        let mut cur = stream.walk();
        let document = stream
            .named_children(&mut cur)
            .find(|c| c.kind_id() == self.document_id)
            .ok_or_else(|| QueryError::MissingChild("document".into()))?;

        // From here, we expect a top-level `block_node` or `flow_node`
        // depending on how the top-level value is expressed.
        let top_node = document.child(0).unwrap();
        let mut key_node = top_node;
        for component in &query.route {
            match self.descend(&key_node, component) {
                Ok(next) => key_node = next,
                Err(e) => return Err(e),
            }
        }

        // If we're ending on a key and not an index, we clean up the final
        // node a bit to have it point to the parent `block_mapping_pair`.
        // This results in a (subjectively) more intuitive extracted feature,
        // since `foo: bar` gets extracted for `foo` instead of just `bar`.
        if matches!(query.route.last().unwrap(), Component::Key(_)) {
            key_node = key_node.parent().unwrap()
        }

        Ok(key_node)
    }

    fn descend<'b>(&self, node: &Node<'b>, component: &Component) -> Result<Node<'b>, QueryError> {
        // The cursor is assumed to start on a block_node or flow_node,
        // which has a single child containing the inner scalar/vector
        // type we're descending through.
        let child = node.child(0).unwrap();

        // We expect the child to be a sequence or mapping of either
        // flow or block type.
        if child.kind_id() == self.block_mapping_id || child.kind_id() == self.flow_mapping_id {
            match component {
                Component::Key(key) => self.descend_mapping(&child, key),
                Component::Index(idx) => Err(QueryError::ExpectedList(*idx)),
            }
        } else if child.kind_id() == self.block_sequence_id
            || child.kind_id() == self.flow_sequence_id
        {
            match component {
                Component::Index(idx) => self.descend_sequence(&child, *idx),
                Component::Key(key) => Err(QueryError::ExpectedMapping(key.into())),
            }
        } else {
            Err(QueryError::UnexpectedNode(child.kind().into()))
        }
    }

    fn descend_mapping<'b>(&self, node: &Node<'b>, expected: &str) -> Result<Node<'b>, QueryError> {
        let mut cur = node.walk();
        for child in node.named_children(&mut cur) {
            // Skip over any unexpected children, e.g. comments.
            if child.kind_id() != self.flow_node_id && child.kind_id() != self.block_mapping_pair_id
            {
                continue;
            }

            let key = child
                .child_by_field_name("key")
                .ok_or_else(|| QueryError::MissingChildField(child.kind().into(), "key"))?;
            let key_value = key.utf8_text(self.source.as_bytes()).unwrap();
            if key_value == expected {
                return child
                    .child_by_field_name("value")
                    .ok_or_else(|| QueryError::MissingChildField(child.kind().into(), "value"));
            }
        }

        // None of the keys in the mapping matched.
        Err(QueryError::ExhaustedMapping(expected.into()))
    }

    fn descend_sequence<'b>(&self, node: &Node<'b>, idx: usize) -> Result<Node<'b>, QueryError> {
        let mut cur = node.walk();
        // TODO: Optimize; we shouldn't collect the entire child set just to extract one.
        let children = node.named_children(&mut cur).collect::<Vec<_>>();
        let Some(child) = children.get(idx) else {
            return Err(QueryError::ExhaustedList(idx, children.len()));
        };

        // If we're in a block_sequence, there's an intervening `block_sequence_item`
        // getting in the way of our `flow_node`.
        if child.kind_id() == self.block_sequence_item_id {
            return child
                .named_child(0)
                .ok_or_else(|| QueryError::MissingChild(child.kind().into()));
        }

        Ok(*child)
    }
}

#[cfg(test)]
mod tests {
    use crate::{Component, Document, Query};

    #[test]
    fn test_basic() {
        let doc = r#"
foo: bar
baz:
  sub:
    keys:
      abc:
        - 123
        - 456
        - [a, b, c, {d: e}]
        "#;

        let doc = Document::new(doc).unwrap();
        let query = Query {
            route: vec![
                Component::Key("baz".into()),
                Component::Key("sub".into()),
                Component::Key("keys".into()),
                Component::Key("abc".into()),
                Component::Index(2),
                Component::Index(3),
            ],
        };

        assert_eq!(doc.extract(&doc.query(&query).unwrap()), "{d: e}");
    }
}
