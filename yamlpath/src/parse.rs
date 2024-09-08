use nom::{
    branch::alt,
    bytes::complete::tag,
    character::complete::{alpha1, char, i32},
    combinator::all_consuming,
    multi::separated_list1,
    sequence::delimited,
    IResult,
};

use crate::{Component, Query};

fn index(input: &str) -> IResult<&str, Component> {
    let (input, index) = delimited(char('['), i32, char(']'))(input)?;

    Ok((input, Component::Index(index as usize)))
}

fn key(input: &str) -> IResult<&str, Component> {
    // TODO: quoted variant.
    let (input, k) = alpha1(input)?;

    Ok((input, Component::Key(k.into())))
}

fn query(input: &str) -> IResult<&str, Vec<Component>> {
    separated_list1(tag("."), alt((index, key)))(input)
}

pub(crate) fn parse(input: &str) -> Result<Query, nom::Err<nom::error::Error<&str>>> {
    let (_, route) = all_consuming(query)(input)?;

    Ok(Query { route })
}

#[cfg(test)]
mod tests {
    use crate::{parse::query, Component};

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
        let q = "foo.bar.baz.[1]";
        let (_, components) = query(q).unwrap();
        assert_eq!(
            components,
            [
                Component::Key("foo".into()),
                Component::Key("bar".into()),
                Component::Key("baz".into()),
                Component::Index(1),
            ]
        )
    }
}
