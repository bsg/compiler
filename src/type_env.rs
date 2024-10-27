use std::{cell::UnsafeCell, collections::HashMap, rc::Rc};

use crate::ast::TypeAnnotation;

// TODO attach id and llvm type to the variants
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Type {
    Void,
    Bool,
    Int {
        /// width in bits
        width: usize,
        signed: bool,
    },
    Ptr {
        pointee_type: Rc<TypeAnnotation>,
    },
    Ref {
        referent_type: Rc<TypeAnnotation>,
    },
    Struct {
        name: Rc<String>,
        field_indices: HashMap<String, usize>,
        field_types: Vec<Rc<TypeAnnotation>>,
        type_params: Rc<[Rc<TypeAnnotation>]>,
        attributes: Option<Rc<[Rc<str>]>>,
    },
    Array {
        elem_type: Rc<TypeAnnotation>,
        len: usize,
    },
    Fn {
        params: Vec<Rc<TypeAnnotation>>,
        ret_type: Rc<TypeAnnotation>,
    },
}

impl Type {
    pub fn name(&self) -> String {
        match self {
            Type::Void => "void".to_string(),
            Type::Bool => "bool".to_string(),
            Type::Int { width, signed } => {
                format!("{}{}", if *signed { "i" } else { "u" }, width)
            }
            Type::Ptr { pointee_type } => format!("*{}", pointee_type),
            Type::Ref { referent_type } => format!("&{}", referent_type),
            Type::Struct { name, .. } => name.to_string(),
            Type::Array { elem_type, len } => format!("[{}; {}]", elem_type, len),
            Type::Fn {
                params: param_types,
                ret_type,
            } => format!(
                "fn({}) -> {}",
                param_types
                    .iter()
                    .map(|ty| ty.to_string())
                    .collect::<Vec<String>>()
                    .join(","),
                ret_type
            ),
        }
    }
}

pub struct TypeEnv {
    parent: Option<Rc<TypeEnv>>,
    types: UnsafeCell<HashMap<Rc<TypeAnnotation>, Type>>,
}

impl TypeEnv {
    pub fn new() -> Self {
        TypeEnv {
            parent: None,
            types: UnsafeCell::new(HashMap::new()),
        }
    }

    pub fn make_child(parent: Rc<Self>) -> Self {
        TypeEnv {
            parent: Some(parent.clone()),
            types: UnsafeCell::new(HashMap::new()),
        }
    }

    pub fn insert(&self, type_annotation: Rc<TypeAnnotation>, ty: Type) {
        if let Some(parent) = &self.parent {
            parent.insert(type_annotation, ty);
        } else {
            (unsafe { &mut *self.types.get() }).insert(type_annotation, ty);
        }
    }

    pub fn insert_local(&self, type_annotation: Rc<TypeAnnotation>, ty: Type) {
        (unsafe { &mut *self.types.get() }).insert(type_annotation, ty);
    }

    pub fn get(&self, type_annotation: &TypeAnnotation) -> Option<&Type> {
        match (unsafe { &*self.types.get() }).get(type_annotation) {
            ty @ Some(_) => ty,
            None => {
                if let Some(parent) = &self.parent {
                    parent.get(type_annotation)
                } else if type_annotation.is_generic() {
                    println!("attempting type monomorphization for {}", type_annotation);
                    if let Some(ty) = self.get(&type_annotation.strip_generics()) {
                        match ty {
                            Type::Struct {
                                field_indices,
                                field_types,
                                type_params,
                                attributes,
                                ..
                            } => {
                                let type_substitutions: Vec<(
                                    Rc<TypeAnnotation>,
                                    Rc<TypeAnnotation>,
                                )> = type_params
                                    .iter()
                                    .zip(type_annotation.type_args().iter())
                                    .map(|(param, arg)| (param.clone(), arg.clone()))
                                    .collect();

                                self.insert(
                                    type_annotation.clone().into(),
                                    Type::Struct {
                                        name: type_annotation.to_string().into(),
                                        field_indices: field_indices.clone(),
                                        field_types: field_types
                                            .iter()
                                            .map(|ty_param| {
                                                ty_param.substitute(&type_substitutions)
                                            })
                                            .collect(),
                                        type_params: [].into(),
                                        attributes: attributes.clone(),
                                    },
                                );

                                match self.get(type_annotation) {
                                    ty @ Some(_) => ty,
                                    None => {
                                        panic!(
                                            "failed to retrieve type after specialization {}",
                                            type_annotation
                                        );
                                    }
                                }
                            }
                            _ => todo!(),
                        }
                    } else {
                        None
                    }
                } else {
                    match type_annotation {
                        TypeAnnotation::Ref { referent_type } => {
                            self.insert(
                                type_annotation.clone().into(),
                                Type::Ref {
                                    referent_type: referent_type.clone(),
                                },
                            );

                            return self.get(type_annotation);
                        }
                        TypeAnnotation::Ptr { pointee_type } => {
                            self.insert(
                                type_annotation.clone().into(),
                                Type::Ptr {
                                    pointee_type: pointee_type.clone(),
                                },
                            );

                            return self.get(type_annotation);
                        }
                        _ => return None,
                    }
                }
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn register_and_lookup() {
        let env = TypeEnv::new();

        let type_param = Rc::new(TypeAnnotation::Simple {
            ident: "T".into(),
            type_args: [].into(),
        });

        env.insert(
            TypeAnnotation::Simple {
                ident: "Foo".into(),
                type_args: [type_param.clone()].into(),
            }
            .into(),
            Type::Bool,
        );

        assert_eq!(
            env.get(&TypeAnnotation::Simple {
                ident: "Foo".into(),
                type_args: [type_param.clone()].into()
            })
            .unwrap()
            .name()
            .to_string(),
            "bool"
        );
    }

    #[test]
    fn lookup_ref() {
        let env = TypeEnv::new();

        env.insert(
            TypeAnnotation::Simple {
                ident: "bool".into(),
                type_args: [].into(),
            }
            .into(),
            Type::Bool,
        );

        assert_eq!(
            env.get(&TypeAnnotation::Ref {
                referent_type: TypeAnnotation::simple_from_name("bool")
            })
            .unwrap()
            .name()
            .to_string(),
            "&bool"
        );
    }

    #[test]
    fn monomorphization_1() {
        let env = TypeEnv::new();

        let type_param = Rc::new(TypeAnnotation::Simple {
            ident: "T".into(),
            type_args: [].into(),
        });

        env.insert(
            TypeAnnotation::Simple {
                ident: "Foo".into(),
                type_args: [].into(),
            }
            .into(),
            Type::Struct {
                name: "Foo".to_string().into(),
                field_indices: [("inner".to_string(), 0usize)].iter().cloned().collect(),
                field_types: [type_param.clone()].into(),
                type_params: [type_param].into(),
                attributes: None,
            },
        );

        let type_arg = Rc::new(TypeAnnotation::Simple {
            ident: "u32".into(),
            type_args: [].into(),
        });

        let monomorph = env
            .get(&TypeAnnotation::Simple {
                ident: "Foo".into(),
                type_args: [type_arg.clone()].into(),
            })
            .unwrap();
        assert_eq!(monomorph.name().to_string(), "Foo<u32>");
        match monomorph {
            Type::Struct { field_types, .. } => {
                assert_eq!(field_types.first().unwrap().to_string(), "u32")
            }
            _ => panic!(),
        }
    }

    #[test]
    fn monomorphization_2() {
        let env = TypeEnv::new();

        let type_param = Rc::new(TypeAnnotation::Simple {
            ident: "T".into(),
            type_args: [].into(),
        });

        let field_type = Rc::new(TypeAnnotation::Simple {
            ident: "Bar".into(),
            type_args: [type_param.clone()].into(),
        });

        env.insert(
            TypeAnnotation::Simple {
                ident: "Foo".into(),
                type_args: [].into(),
            }
            .into(),
            Type::Struct {
                name: "Foo".to_string().into(),
                field_indices: [("inner".to_string(), 0usize)].iter().cloned().collect(),
                field_types: [field_type.clone()].into(),
                type_params: [type_param].into(),
                attributes: None,
            },
        );

        let type_arg = Rc::new(TypeAnnotation::Simple {
            ident: "u32".into(),
            type_args: [].into(),
        });

        let monomorph = env
            .get(&TypeAnnotation::Simple {
                ident: "Foo".into(),
                type_args: [type_arg.clone()].into(),
            })
            .unwrap();
        assert_eq!(monomorph.name().to_string(), "Foo<u32>");
        match monomorph {
            Type::Struct { field_types, .. } => {
                assert_eq!(field_types.first().unwrap().to_string(), "Bar<u32>")
            }
            _ => panic!(),
        }
    }

    #[test]
    fn monomorphization_3() {
        let env = TypeEnv::new();

        let type_param = Rc::new(TypeAnnotation::Simple {
            ident: "T".into(),
            type_args: [].into(),
        });

        let field_type = Rc::new(TypeAnnotation::Ptr {
            pointee_type: Rc::new(TypeAnnotation::Simple {
                ident: "Bar".into(),
                type_args: [type_param.clone()].into(),
            }),
        });

        env.insert(
            TypeAnnotation::Simple {
                ident: "Foo".into(),
                type_args: [].into(),
            }
            .into(),
            Type::Struct {
                name: "Foo".to_string().into(),
                field_indices: [("inner".to_string(), 0usize)].iter().cloned().collect(),
                field_types: [field_type.clone()].into(),
                type_params: [type_param].into(),
                attributes: None,
            },
        );

        let type_arg = Rc::new(TypeAnnotation::Simple {
            ident: "u32".into(),
            type_args: [].into(),
        });

        let env = TypeEnv::make_child(env.into());

        let monomorph = env
            .get(&TypeAnnotation::Simple {
                ident: "Foo".into(),
                type_args: [type_arg.clone()].into(),
            })
            .unwrap();
        assert_eq!(monomorph.name().to_string(), "Foo<u32>");
        match monomorph {
            Type::Struct { field_types, .. } => {
                assert_eq!(field_types.first().unwrap().to_string(), "*Bar<u32>")
            }
            _ => panic!(),
        }
    }
}
