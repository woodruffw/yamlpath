use std::io::stdin;

use anyhow::Result;
use clap::Parser;

mod parse;

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

    let query = parse::parse(&args.query)?;
    let input = match args.input.as_deref() {
        Some("-") | None => std::io::read_to_string(stdin())?,
        Some(path) => std::fs::read_to_string(path)?,
    };

    let doc = yamlpath::Document::new(&input)?;

    let finding = doc.query(&query)?;

    println!("Finding: {finding:?}");
    println!("Extracted:\n\n{}", doc.extract(&finding));

    Ok(())
}
