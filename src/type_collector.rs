use std::{collections::HashSet, rc::Rc};

use crate::ast::{NodeKind, NodeRef, Op, PathSegment};

pub struct TypeCollector {
    ast: Rc<Vec<NodeRef>>,
    types: HashSet<String>,
    fn_instances: HashSet<PathSegment>,
}

impl TypeCollector {
    pub fn new(ast: Rc<Vec<NodeRef>>) -> Self {
        Self {
            ast,
            types: HashSet::new(),
            fn_instances: HashSet::new(),
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
                }
                self.collect_recursively(lhs.clone());
                self.collect_recursively(rhs.clone());
            }
            NodeKind::Let { ty, rhs, .. } => {
                self.types.insert(ty.to_string());

                if let Some(rhs) = rhs {
                    self.collect_recursively(rhs.clone());
                }
            }
            NodeKind::Const { ty, rhs, .. } => {
                self.types.insert(ty.to_string());
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
                params: args,
                ret_ty,
                body,
                ..
            } => {
                self.types.insert(ret_ty.to_string());
                for arg in args.iter() {
                    self.types.insert(arg.ty().to_string());
                }
                if let Some(body) = body {
                    self.collect_recursively(body.clone());
                }
            }
            NodeKind::Call { path, args } => {
                self.fn_instances.insert(path.clone());
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
                        self.types.insert(field.ty.to_string());
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
            NodeKind::StructLiteral { path, fields } => {
                self.types.insert(path.to_string());
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

    pub fn for_each_ty(&self, f: impl FnMut(&String)) -> &Self {
        self.types.iter().for_each(f);
        self
    }

    pub fn for_each_fn_instance(&self, f: impl FnMut(&PathSegment)) -> &Self {
        self.fn_instances.iter().for_each(f);
        self
    }
}
