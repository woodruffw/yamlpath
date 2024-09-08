use std::io::stdin;

use anyhow::Result;
use clap::Parser;

/// Extracts features from YAML documents.
#[derive(Parser, Debug)]
#[command(version, about, long_about = None)]
struct Args {
    /// The path to query for.
    query: String,
    /// The input to query. Defaults to `stdin`.
    input: Option<String>,
}

fn main() -> Result<()> {
    let args = Args::parse();

    let query = yamlpath::Query::new(&args.query)?;
    let input = match args.input.as_deref() {
        Some("-") | None => std::io::read_to_string(stdin())?,
        Some(path) => std::fs::read_to_string(path)?,
    };

    let doc = yamlpath::Document::new(&input)?;

    let finding = doc.query(&query)?;

    dbg!(finding);

    Ok(())
}
