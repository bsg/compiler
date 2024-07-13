use std::{collections::HashSet, rc::Rc};

use crate::ast::{Node, NodeRef, Op};

pub struct TypeCollector {
    ast: Rc<Vec<NodeRef>>,
    types: HashSet<String>,
}

impl TypeCollector {
    pub fn new(ast: Rc<Vec<NodeRef>>) -> Self {
        Self {
            ast,
            types: HashSet::new(),
        }
    }

    fn collect_recursively(&mut self, node: NodeRef) {
        match &*node {
            Node::Ident { .. } => (
                    // TODO
                ),
            Node::UnOp { rhs, .. } => self.collect_recursively(rhs.clone()),
            Node::BinOp { op, lhs, rhs } => {
                if let Op::ScopeRes = op {
                    if let Node::Ident { name } = &**lhs {
                        self.types.insert((&**name).into());
                    }
                    self.collect_recursively(rhs.clone());
                }
            }
            Node::Let { ty, rhs, .. } => {
                self.types.insert((&**ty).into());
                if let Some(rhs) = rhs {
                    self.collect_recursively(rhs.clone());
                }
            }
            Node::Const { ty, rhs, .. } => {
                self.types.insert((&**ty).into());
                if let Some(rhs) = rhs {
                    self.collect_recursively(rhs.clone());
                }
            }
            Node::Return { expr } => match expr {
                Some(expr) => {
                    self.collect_recursively(expr.clone());
                }
                _ => (),
            },
            Node::If {
                condition,
                then_block,
                else_block,
            } => {
                self.collect_recursively(condition.clone());
                self.collect_recursively(then_block.clone());
                if let Some(else_block) = else_block {
                    self.collect_recursively(else_block.clone())
                }
            }
            Node::While { condition, body } => {
                self.collect_recursively(condition.clone());
                self.collect_recursively(body.clone());
            }
            Node::Block { statements } => {
                for stmt in statements.iter() {
                    self.collect_recursively(stmt.clone());
                }
            }
            Node::Fn {
                args, ret_ty, body, ..
            } => {
                self.types.insert((&**ret_ty).into());
                for arg in args.iter() {
                    self.types.insert((&*arg.ty()).into());
                }
                if let Some(body) = body {
                    self.collect_recursively(body.clone());
                }
            }
            Node::Call { args, .. } => {
                for arg in args.iter() {
                    self.collect_recursively(arg.clone());
                }
            }
            Node::Struct { ident, fields, .. } => {
                if !ident.contains("<>") {
                    self.types.insert((&**ident).into());
                }
                for field in fields.iter() {
                    self.types.insert((&*field.ty).into());
                }
            }
            Node::Impl { methods, .. } => {
                for method in methods.iter() {
                    self.collect_recursively(method.clone());
                }
            }
            Node::Array { elems } => {
                for elem in elems.iter() {
                    self.collect_recursively(elem.clone());
                }
            }
            _ => (),
        }
    }

    pub fn collect(&mut self) -> &Self {
        for node in &*self.ast.clone() {
            self.collect_recursively(node.clone())
        }
        self
    }

    pub fn for_each(&self, f: impl FnMut(&String)) {
        self.types.iter().for_each(f)
    }
}
