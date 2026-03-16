use std::path::PathBuf;

use comfy_table::{
    Attribute, Cell, Color, ContentArrangement, Table, presets::UTF8_FULL_CONDENSED,
};
use itertools::Itertools;
use owo_colors::{OwoColorize, colors::css::Gray};
use rustyline::{DefaultEditor, error::ReadlineError};
use tempest_core::fio::UringFileSystem;
use tempest_engine::{
    Engine, EngineError, catalog::CatalogState, config::EngineConfig, query::QueryResult,
};
use tempest_tql::ParseError;

fn explain_command(name: &str, description: &str) {
    println!("{} {}", name.bright_green(), description.fg::<Gray>())
}

#[rustfmt::skip]
const REPL_INTRODUCTION: &str = 
r"This is the Tempest REPL: Read, Evaluate, Print, Loop.
You can type in some special commands, starting with a dot,
or you can enter in valid TQL statements!";

fn show_help() {
    println!("{}", "List of available commands:".bright_green());
    explain_command(".help | .h", "show this menu");
    explain_command(".quit | .q", "terminate the REPL session");
    explain_command(".databases | .dbs", "list all databases");
    explain_command(
        ".tables <database>",
        "list all tables, optionally scoped to a database",
    );
    explain_command(
        ".types <database>",
        "list all types, optionally scoped to a database",
    );
}

fn create_comfy_table() -> Table {
    let mut table = Table::new();
    table
        .load_preset(UTF8_FULL_CONDENSED)
        .set_content_arrangement(ContentArrangement::Dynamic)
        .set_width(80);
    table
}

fn list_databases(catalog: &CatalogState) {
    let mut table = create_comfy_table();
    table.set_header(vec![
        Cell::new("database")
            .add_attribute(Attribute::Bold)
            .fg(Color::Green),
        Cell::new("tables")
            .add_attribute(Attribute::Bold)
            .fg(Color::Green),
    ]);
    for db in catalog.databases.values() {
        table.add_row(vec![Cell::new(&db.name), Cell::new(db.tables.len())]);
    }
    println!("{table}");
}

fn list_tables(catalog: &CatalogState, database: Option<&str>) {
    let mut table = create_comfy_table();
    table.set_header(vec![
        Cell::new("database")
            .add_attribute(Attribute::Bold)
            .fg(Color::Green),
        Cell::new("table")
            .add_attribute(Attribute::Bold)
            .fg(Color::Green),
        Cell::new("columns")
            .add_attribute(Attribute::Bold)
            .fg(Color::Green),
        Cell::new("primary key")
            .add_attribute(Attribute::Bold)
            .fg(Color::Green),
    ]);
    let tables: Vec<_> = if let Some(database) = database {
        catalog.tables_in_database(database).collect()
    } else {
        catalog
            .tables
            .iter()
            .map(|(tid, schema)| (*tid, schema))
            .collect()
    };

    for (_, table_schema) in tables {
        let database = &catalog.databases[&table_schema.database_id].name;
        let fields = &catalog.types[&table_schema.type_id].fields;
        let columns = fields.len();
        table.add_row(vec![
            Cell::new(database),
            Cell::new(&table_schema.name),
            Cell::new(columns),
            Cell::new(
                table_schema
                    .primary_key
                    .iter()
                    .map(|fid| &fields[fid].name)
                    .join(", "),
            ),
        ]);
    }

    println!("{table}");
}

fn list_types(catalog: &CatalogState, database: Option<&str>) {
    let mut table = create_comfy_table();
    table.set_header(vec![
        Cell::new("database")
            .add_attribute(Attribute::Bold)
            .fg(Color::Green),
        Cell::new("type")
            .add_attribute(Attribute::Bold)
            .fg(Color::Green),
        Cell::new("fields")
            .add_attribute(Attribute::Bold)
            .fg(Color::Green),
    ]);
    let types: Vec<_> = if let Some(database) = database {
        catalog.types_in_database(database).collect()
    } else {
        catalog
            .types
            .iter()
            .map(|(tid, schema)| (*tid, schema))
            .collect()
    };

    for (_, type_schema) in types {
        let database = &catalog.databases[&type_schema.database_id].name;
        table.add_row(vec![
            Cell::new(database),
            Cell::new(&type_schema.name),
            Cell::new(
                type_schema
                    .fields
                    .iter()
                    .map(|(_, def)| &def.name)
                    .join(", "),
            ),
        ]);
    }

    println!("{table}");
}

fn print_query_results(results: Vec<QueryResult>) {
    for res in results {
        match res {
            QueryResult::Rows { columns, rows } => {
                let mut table = create_comfy_table();
                table
                    .set_header(columns.iter().map(|col| {
                        Cell::new(col)
                            .add_attribute(Attribute::Bold)
                            .fg(Color::Green)
                    }))
                    .add_rows(rows.iter().map(|row| row.iter().map(|v| format!("{}", v))));
                println!("{table}");
            }
            QueryResult::Empty => {}
        }
    }
}

fn print_parse_errors(source: &str, errors: &[ParseError]) {
    use ariadne::{Color, Label, Report, ReportKind, Source};

    for error in errors {
        Report::build(ReportKind::Error, error.span.clone())
            .with_message("parse error")
            .with_label(
                Label::new(error.span.clone())
                    .with_message(format!("{}", error.kind))
                    .with_color(Color::Red),
            )
            .finish()
            .print(Source::from(source))
            .unwrap();
    }
}

const TEMPEST_HISTORY_FILENAME: &str = ".tempest_history";

#[instrument(level = "debug")]
pub(crate) fn repl(data_dir: PathBuf) -> anyhow::Result<()> {
    debug!("starting repl shell");

    tokio_uring::start(async {
        let fs = UringFileSystem;
        let config = EngineConfig::default();
        let mut engine = Engine::open(fs.clone(), data_dir, config).await.unwrap();

        let history_path = dirs::home_dir().map(|h| h.join(TEMPEST_HISTORY_FILENAME));

        let mut rl = DefaultEditor::new()?;

        if let Some(path) = history_path.as_ref() {
            let _ = rl.load_history(path);
        }

        println!("{}", "-- Tempest REPL --".bright_cyan().bold());
        println!("{}", REPL_INTRODUCTION.bright_cyan());
        show_help();

        loop {
            match rl.readline(">> ") {
                Ok(cmd) => {
                    let cmd = cmd.trim();
                    rl.add_history_entry(cmd)?;
                    if cmd.starts_with(".") {
                        let args: Vec<_> = cmd.split_whitespace().collect();
                        match args[0] {
                            ".help" | ".h" => show_help(),
                            ".quit" | ".q" => break,
                            ".databases" | ".dbs" => list_databases(engine.catalog()),
                            ".tables" => list_tables(engine.catalog(), args.get(1).copied()),
                            ".types" => list_types(engine.catalog(), args.get(1).copied()),
                            _ => {
                                println!("{} `{}`", "unknown command:".bright_red(), cmd);
                                println!(
                                    "{}",
                                    "type .help to show available commands"
                                        .bright_green()
                                        .italic()
                                );
                            }
                        }
                    } else {
                        match engine.execute(cmd).await {
                            Ok(results) => print_query_results(results),
                            Err(err) => {
                                eprintln!("{}", "Failed to execute query:".bright_red().bold());
                                match err {
                                    EngineError::ParseError(parse_errors) => {
                                        print_parse_errors(cmd, &parse_errors);
                                    }
                                    _ => eprintln!("{}", format!("{}", err).bright_red()),
                                }
                            }
                        }
                    }
                }
                Err(ReadlineError::Eof | ReadlineError::Interrupted) => break,
                Err(err) => return Err(err.into()),
            }
        }

        engine.shutdown().await?;

        if let Some(path) = history_path.as_ref() {
            let _ = rl.save_history(path);
        }

        Ok(())
    })
}
