use std::{collections::HashSet, rc::Rc};

use crate::ast::{NodeKind, NodeRef, Op};

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
        match &node.kind {
            NodeKind::Ident { .. } => (
                    // TODO
                ),
            NodeKind::UnOp { rhs, .. } => self.collect_recursively(rhs.clone()),
            NodeKind::BinOp { op, lhs, rhs } => {
                if let Op::ScopeRes = op {
                    if let NodeKind::Ident { name } = &lhs.kind {
                        self.types.insert((&**name).into());
                    }
                    self.collect_recursively(rhs.clone());
                }
            }
            NodeKind::Let { ty, rhs, .. } => {
                if let Some(ty) = ty {
                    self.types.insert((&**ty).into());
                }
                if let Some(rhs) = rhs {
                    self.collect_recursively(rhs.clone());
                }
            }
            NodeKind::Const { ty, rhs, .. } => {
                if let Some(ty) = ty {
                    self.types.insert((&**ty).into());
                }
                if let Some(rhs) = rhs {
                    self.collect_recursively(rhs.clone());
                }
            }
            NodeKind::Return { expr: Some(expr) } => {
                self.collect_recursively(expr.clone());
            }
            NodeKind::If {
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
            NodeKind::While { condition, body } => {
                self.collect_recursively(condition.clone());
                self.collect_recursively(body.clone());
            }
            NodeKind::Block { statements } => {
                for stmt in statements.iter() {
                    self.collect_recursively(stmt.clone());
                }
            }
            NodeKind::Fn {
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
            NodeKind::Call { args, .. } => {
                for arg in args.iter() {
                    self.collect_recursively(arg.clone());
                }
            }
            NodeKind::Struct {
                ident,
                fields,
                generics,
                ..
            } => {
                if generics.is_empty() {
                    self.types.insert((&**ident).into());
                    for field in fields.iter() {
                        self.types.insert((&*field.ty).into());
                    }
                }
            }
            NodeKind::Impl { methods, .. } => {
                for method in methods.iter() {
                    self.collect_recursively(method.clone());
                }
            }
            NodeKind::Array { elems } => {
                for elem in elems.iter() {
                    self.collect_recursively(elem.clone());
                }
            }
            NodeKind::StructLiteral { ident, fields } => {
                self.types.insert(ident.to_string());
                for field in fields.iter() {
                    self.collect_recursively(field.clone().val);
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
