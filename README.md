# yamlpath


[![CI](https://github.com/zizmorcore/yamlpath/actions/workflows/ci.yml/badge.svg)](https://github.com/zizmorcore/yamlpath/actions/workflows/ci.yml)
[![Crates.io](https://img.shields.io/crates/v/yamlpath)](https://crates.io/crates/yamlpath)
[![docs.rs](https://img.shields.io/docsrs/yamlpath)](https://docs.rs/yamlpath)

Format-preserving YAML feature extraction.

You can use this library (or [`yp`](#the-yp-cli), its associated CLI) to perform
basic queries over YAML documents, returning exact line- and byte-span
results with comments and formatting preserved exactly as they appear
in the original source.

`yamlpath` uses [`tree-sitter`] and [`tree-sitter-yaml`] under the hood.

[`tree-sitter`]: https://github.com/tree-sitter/tree-sitter

[`tree-sitter-yaml`]: https://github.com/tree-sitter-grammars/tree-sitter-yaml

> [!IMPORTANT]
>
> This is not a substitute for full-fledged query languages or tools
> like JSONPath or `jq`.

## Why?

YAML is an extremely popular configuration format, with an interior
data model that closely resembles JSON.

It's common to need to analyze YAML files, e.g. for a security tool that
needs to interpret the contents of a configuration file.

The normal way to do this is to parse the YAML into a document and interpret
that document. However, that parsing operation is *destructive*: in producing
a document model, it *erases* the comments and exact formatting of the YAML
input.

This can make it difficult to present intelligible actions to uses,
since users think in terms of changes needed on lines and columns and not
changes needed to a specific sub-object within a document's hierarchy.

`yamlpath` bridges the gap between these two views: it allows a program
to operate on the (optimal) document view, and then *translate* back to
a human's understanding of the YAML input.

## The `yp` CLI

`yamlpath` is developed primarily as a library, but the `yp` CLI exists
to demonstrate what it can do.

To get started with it, you can either build it from ths repository:

```bash
cargo build -p yp
```

...and then use it:

```bash
yp --help
yp 'foo.bar.[1].baz' some-input.yml
```

Note: the format of `yp`'s output is not stable or intended for programmatic
consumption. Similarly, the query language used by `yp` is not stable or
intended for non-experimental use.

## License

MIT License.
