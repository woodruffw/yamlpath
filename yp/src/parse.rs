//! Hacky DSL for path queries.

use nom::{
    branch::alt,
    bytes::complete::{tag, take_till1},
    character::complete::{char, i32},
    combinator::{all_consuming, not},
    multi::separated_list1,
    sequence::{delimited, tuple},
    IResult,
};
use yamlpath::{Component, Query};

fn index(input: &str) -> IResult<&str, Component> {
    let (input, index) = delimited(char('['), i32, char(']'))(input)?;

    Ok((input, Component::Index(index as usize)))
}

fn key(input: &str) -> IResult<&str, Component> {
    // TODO: quoted variant.
    // TODO: This is a mess -- we need negative match on `[ ... ]` to
    // avoid accidentally consuming the empty `[]` case as a valid key
    // rather than an invalid index.
    let (input, (_, k, _)) =
        tuple((not(tag("[")), take_till1(|c| c == '.'), not(tag("]"))))(input)?;

    Ok((input, Component::Key(k.into())))
}

fn query(input: &str) -> IResult<&str, Vec<Component>> {
    separated_list1(tag("."), alt((index, key)))(input)
}

pub(crate) fn parse(input: &str) -> Result<Query, nom::Err<nom::error::Error<String>>> {
    let (_, route) =
        all_consuming(query)(input).map_err(|e: nom::Err<nom::error::Error<&str>>| {
            e.map_input(|input| input.to_string())
        })?;

    // Infallible: we always parse at least one component above.
    Ok(Query::new(route).unwrap())
}

#[cfg(test)]
mod tests {
    use yamlpath::Component;

    use crate::parse::query;

    #[test]
    fn test_parse_errors() {
        // Empty query is invalid.
        assert!(query("").is_err());
        assert!(query(".").is_err());
        assert!(query("..").is_err());
        // Invalid indices.
        assert!(query("[]").is_err());
        assert!(query("[abc]").is_err());
    }

    #[test]
    fn test_basic() {
        let q = "foo.bar.baz.has_underscore.[1]";
        let (_, components) = query(q).unwrap();
        assert_eq!(
            components,
            [
                Component::Key("foo".into()),
                Component::Key("bar".into()),
                Component::Key("baz".into()),
                Component::Key("has_underscore".into()),
                Component::Index(1),
            ]
        )
    }
}
