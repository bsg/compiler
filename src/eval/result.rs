use std::{cell::RefCell, collections::HashMap, rc::Rc};

use crate::ast::{FnExpression, NodeRef};

use super::{env::EnvRef, error::Error};

#[derive(Debug, PartialEq, Eq, Clone, Hash)]
pub enum MapKey {
    Str(Rc<str>),
    Int(i64),
    Bool(bool),
}

pub type BuiltInFn = fn(&mut [Value]) -> EvalResult;

#[derive(Debug, PartialEq, Clone)]
pub enum Value {
    Nil,
    Int(i64),
    Bool(bool),
    Str(Rc<str>),
    Fn(FnExpression, NodeRef, EnvRef),
    BuiltIn(BuiltInFn),
    Array(Rc<RefCell<Vec<Value>>>),
    Pair(MapKey, Rc<Value>),
    Map(Rc<RefCell<HashMap<MapKey, Value>>>),
    Range(i64, i64),
}

impl From<MapKey> for Value {
    fn from(key: MapKey) -> Self {
        match key {
            MapKey::Str(s) => Value::Str(s),
            MapKey::Int(i) => Value::Int(i),
            MapKey::Bool(b) => Value::Bool(b),
        }
    }
}

impl From<&MapKey> for Value {
    fn from(key: &MapKey) -> Self {
        match key {
            MapKey::Str(s) => Value::Str(s.clone()),
            MapKey::Int(i) => Value::Int(*i),
            MapKey::Bool(b) => Value::Bool(*b),
        }
    }
}

impl Value {
    pub fn type_str(&self) -> &str {
        match self {
            Value::Nil => "Nil",
            Value::Int(_) => "Int",
            Value::Bool(_) => "Bool",
            Value::Str(_) => "Str",
            Value::Fn(..) => "Fn",
            Value::BuiltIn(..) => "Fn",
            Value::Array(_) => "Array",
            Value::Map(_) => "Map",
            Value::Pair(_, _) => "Pair",
            Value::Range(_, _) => "Range",
        }
    }
}

impl std::fmt::Display for Value {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Value::Nil => f.write_str("nil"),
            Value::Int(val) => f.write_fmt(format_args!("{}", val)),
            Value::Bool(val) => f.write_fmt(format_args!("{}", val)),
            Value::Str(val) => f.write_fmt(format_args!("{}", val)),
            Value::Fn(..) => f.write_str("fn"),
            Value::BuiltIn(..) => f.write_str("builtin"),
            Value::Array(arr) => f.write_fmt(format_args!("Array{:?}", arr)),
            Value::Map(map) => f.write_fmt(format_args!("Map{:?}", map)),
            Value::Pair(key, value) => f.write_fmt(format_args!("Pair({:?}, {:?})", key, value)),
            Value::Range(lower, upper) => {
                f.write_fmt(format_args!("Range({:?}, {:?})", lower, upper))
            }
        }
    }
}

#[derive(Debug, PartialEq, Clone)]
pub enum EvalResult {
    Val(Value),
    Return(Value),
    Err(Error),
}

impl std::fmt::Display for EvalResult {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Val(val) | Self::Return(val) => f.write_fmt(format_args!("{}", val)),
            Self::Err(err) => f.write_fmt(format_args!("error: {}", err)),
        }
    }
}
