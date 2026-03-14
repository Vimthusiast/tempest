pub(crate) mod plan;
pub(crate) mod exec;
pub(crate) mod resolve;
pub(crate) mod eval;

#[derive(Debug)]
pub enum QueryResult {
    /// DDL queries, such as `create database`, do not return any values.
    Empty,
}
