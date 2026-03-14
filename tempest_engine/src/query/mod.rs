pub(crate) mod plan;
pub(crate) mod exec;

#[derive(Debug)]
pub enum QueryResult {
    /// DDL queries, such as `create database`, do not return any values.
    Empty,
}
