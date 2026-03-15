use std::borrow::Cow;

use tempest_tql::ast::{Expr, ExprKind};

use crate::types::TempestValue;

pub(crate) fn eval(expr: &Expr<'_>) -> TempestValue<'static> {
    match &expr.kind {
        ExprKind::IntegerLiteral(lit) => {
            // TODO: safely handle this error (i.e. for integer overflow, etc.)
            TempestValue::Int64(lit.parse().unwrap())
        }
        ExprKind::StringLiteral(s) => TempestValue::String(Cow::Owned(s.clone().into_owned())),
        ExprKind::Bool(b) => TempestValue::Bool(*b),
    }
}
