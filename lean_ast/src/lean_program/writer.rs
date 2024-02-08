// Copyright Kani Contributors
// SPDX-License-Identifier: Apache-2.0 OR MIT

//! A writer for Lean programs.
//! Generates a text Lean program TODO: write example format in comments as in Boogie
//! Namespace and Import declarations
//! namespace <namespace1>
//! //! namespace <namespace2> ...
//! import <module1>
//! //! import <module2> ...
//! Definition of functions
//! def <function-name> <input-params>: <type> := <body>
//! theorem <theorem-name> <input-params>: <type> := <body>
//use std::assert_matches::debug_assert_matches;
use crate::lean_program::*;

use std::io::Write;

/// A writer for Lean programs
struct Writer<'a, T:Write> {
    writer: &'a mut T,
    indentation: usize,
}

impl<'a, T:Write> Writer<'a, T>{
    fn new(writer: &'a mut T) -> Self {
        Self {writer, indentation: 0}
    }

    fn newline(&mut self) -> std::io::Result<()> {
        writeln!(self.writer)
    }

    fn increase_indent(&mut self) {
        self.indentation += 2;
    }

    fn decrease_indent(&mut self) {
        self.indentation -= 2;
    }

    fn indent(&mut self) -> std::io::Result<()> {
        write!(self.writer, "{:width$}", "", width = self.indentation)
    }
}

impl<'a, T: Write> Write for Writer<'a, T> {
    /// TODO: I do not understand this implementation
    fn write(&mut self, buf: &[u8]) -> std::io::Result<usize> {
        self.writer.write(buf)
    }

    fn flush(&mut self) -> std::io::Result<()> {
        self.writer.flush()
    }
}


impl LeanProgram {
    pub fn write_to<T: Write>(&self, writer: &mut T) -> std::io::Result<()> {
        let mut writer = Writer::new(writer);
        if !self.functions.is_empty() {
            writeln!(writer, "-- Functions definition:")?;
            for f in &self.functions{
                f.write_to(&mut writer)?;
            }
        }
     Ok(())
    }
}


impl Function {
    fn write_to<T: Write>(&self, writer: &mut Writer<T>) -> std::io::Result<()> {
        // signature
        write!(writer, "def ")?;
        write!(writer, "{}", self.name)?;
        // parameters
        for (_i, param) in self.parameters.iter().enumerate() {
            write!(writer, " (")?;
            write!(writer, "{}: ", param.name)?;
            param.typ.write_to(writer)?;
            write!(writer, ") ")?;
        }
        //todo: fix hardcoding the return type depending on the text in assertions
        write!(writer, " : Except String Unit")?;
        if let Some (return_typ) = &self.return_type{
            return_typ.write_to(writer)?;
        } else {
            writeln!(writer, "")?;
        }

        write!(writer, " := ")?;
        // if let Some(body) = &self.body {
        write!(writer, "Id.run do")?;
        writeln!(writer)?;
        writer.indent()?;
        writer.increase_indent();
        for stmt in self.body.iter().clone(){
            stmt.write_to(writer)?;
        }
        writeln!(writer)?;
        writer.increase_indent();
        Ok(())
    }
}

impl Stmt {
    fn write_to<T: Write>(&self, writer: &mut Writer<T>) -> std::io::Result<()> {
        //! Assignment statements in Lean are different from imperative language : HARD!
        //! We might want to higher order functions or lambda functions
        //! for instance what if we have the following in rust:
        //! let mut x = 0;
        //! x = x + 1;
        //! x = x * 2;
        //!
        //!
        //! Lean translation:
        //! let applyFunctions := fun f1 f2 x => f2 (f1 x)
        //! let op1 := fun x : Int => x + 1
        //! let op2 := fun x : Int => x * 2
        //!
        //! let x := 0
        //! let x' := applyFunctions op1 op2 x
        //!
        //! https://lean-lang.org/functional_programming_in_lean/monad-transformers/do.html?highlight=mutable#mutable-variables
        match self {
            //TODO: if we are using state Monad for assignments, we should definitely take care of importing IO...
            Stmt::Assignment {variable, value } => {
                writer.indent()?;
                write!(writer, "let {} := ", variable)?;
                //todo: What are assignments when we update
                // write!(writer, "let mut {} := ", variable)?;
                value.write_to(writer)?;
                writeln!(writer,"")?;
            }
            // If every statement is an expression, do i need to have this?
            // I can just have `let`, "return" (just var/literal/expression)
            Stmt::Declaration {name, typ, expr} => {
                writer.indent()?;
                write!(writer, "let {} ", name)?;
                match typ {
                    Some(typ) => {
                        write!(writer, ": ")?;
                        typ.write_to(writer)?;
                        write!(writer, " := ")?;
                    },
                    None => write!(writer, ":= ")?,
                }
                expr.write_to(writer)?;
                writeln!(writer,"")?;
            }
            Stmt::Block {statements} => {
                for s in statements {
                    s.write_to(writer)?;
                }
            }
            Stmt::FunctionCall {name, arguments} => {
                writer.indent()?;
                write!(writer, "{} ", name)?;
                for (i, a) in arguments.iter().enumerate() {
                    if i>0 {
                        write!(writer, " ")?;
                    }
                    a.write_to(writer)?;
                }
                writeln!(writer,"")?;
            }


            //todo: fix this -- remove pass
            //Stmt::Skip => {writeln!(writer, "pass ")?;}
            Stmt::Skip => { }
            Stmt::IfThenElse {cond, then_branch, else_branch} => {
                writer.indent()?;
                write!(writer, "if ")?;
                cond.write_to(writer)?;
                writeln!(writer, " then")?;
                writer.increase_indent();
                then_branch.write_to(writer)?;
                writer.decrease_indent();
                if let Some(else_branch) = else_branch {
                    writer.indent()?;
                    writeln!(writer, "else")?;
                    writer.increase_indent();
                    else_branch.write_to(writer)?;
                    writer.decrease_indent();
                }
            }
            Stmt::Return {expr} => {
                writer.indent()?;
                write!(writer, "return ",)?;
                expr.write_to(writer)?;
            }

            _ => {
                todo!()
            }
        }
        Ok(())
    }
}


impl Expr {
    fn write_to<T: Write>(&self, writer: &mut Writer<T>) -> std::io::Result<()> {
        match self {
            Expr::Literal(value) => {
                value.write_to(writer)?
            }
            Expr::Variable {name} => {
                write!(writer, "{}", name)?
            }
            Expr::UnaryOp {op,operand} => {
                op.write_to(writer)?;
                write!(writer, "(")?;
                operand.write_to(writer)?;
                write!(writer, ")")?;
            }
            Expr::BinaryOp {op,left, right} => {
                left.write_to(writer)?;
                write!(writer, " ")?;
                op.write_to(writer)?;
                write!(writer, " ")?;
                right.write_to(writer)?;
            }
            // Expr::FunctionCall {name, arguments} => {
            //     write!(writer, "{}", name)?;
            //     for (i, a) in arguments.iter().enumerate() {
            //         if i>0 {
            //             write!(writer, " ")?;
            //         }
            //         a.write_to(writer)?;
            //     }
            // }
            Expr::Field { base, field } => {
                base.write_to(writer)?;
                // write!(writer, "TODOField {field}")?;
                write!(writer, "{field}")?;
            }
            Expr::Select { base, key } => {
                base.write_to(writer)?;
                // write!(writer, "TODOselectOpen")?;
                //todo: only updates are for setting value of an array index handled now
                // cover all the cases
                // write!(writer, " set ")?;
                key.write_to(writer)?;
                // write!(writer, "TODOselectClose")?;
            }
            Expr::ExceptOk => {
                writeln!(writer, "Except.ok ()")?;
            }
            Expr::ExceptError => {
                writeln!(writer, "Except.error \"assertion did not pass\"")?;
            }

            //todo: Expr::MatchExpr {ExprToMatch, Cases}
            // Cases could be Vec<Expr, Result>
            // def fact : Nat -> Nat
            //   | 0   => 1
            //   | succ n => succ n * fact n
        }
        Ok(())
    }
}



impl Type {
    fn write_to<T: Write>(&self, writer: &mut Writer<T>) -> std::io::Result<()> {
        match self {
            Type::Bool => write!(writer, "Bool")?,
            Type::Int => write!(writer, "Int")?,
            Type::Nat => write!(writer, "Nat")?,
            Type::Unit => write!(writer, "()")?,
            Type::ParameterType {name} => write!(writer, "{}", name)?,
            Type::UserDefined { name, type_arguments } => {
                write!(writer, "{name}")?;
                for arg in type_arguments {
                    write!(writer, " ")?;
                    arg.write_to(writer)?;
                }
            }


            // Type::Function {key, value} => {
            //     // can be a variable or a function
            //     write!(writer, " (")?;
            //     key.write_to(writer)?;
            //     write!(writer, " : ")?;
            //     // this is could be recursive
            //     value.write_to(writer)?;
            //     write!(writer, ")")?;
            // },

            // Function type
            // example def twice (f : Nat -> Nat) (x : Nat)
            // (Int \times Int) or generic types -- f T1 T2 T3 :=
            // type of functions that are input to another functions
            Type::FunctionType {key, value} => {
                // can be a variable, a function, or a product
                key.write_to(writer)?;
                write!(writer, " -> ")?;
                value.write_to(writer)?;
            },
            // (l: (Nat * Nat))
            Type::Product {typ1, typ2} => {
                typ1.write_to(writer)?;
                write!(writer, " \\times ")?;
                typ2.write_to(writer)?;
            }
        }
        Ok(())
    }
}


impl Literal {
    /// For unbounded integers we can use Nat
    /// if we want restrict the size we can make use bounded unsigned Integers (e.g. U32Int)
    /// https://github.com/leanprover/lean4/blob/d4f10bc07e575de14edd08ccbcda55e6dd3fa823/src/Init/Data/UInt/Basic.lean
    /// TODO: we need to make sure that we bound depending on the rust program
    /// Integers are an instance of Nat in
    /// just integer makes the integer unbounded in Lean,
    /// If need bounded negative Integers, we might need to define by ourselves
    /// TODO: we need to make sure that we bound and have negative ints depending on the rust program
    /// https://github.com/leanprover/lean4/blob/d4f10bc07e575de14edd08ccbcda55e6dd3fa823/src/Init/Data/Int/Basic.lean
    fn write_to<T: Write>(&self, writer: &mut Writer<T>) -> std::io::Result<()> {
        match self {
            Literal::Bool(value) => {
                write!(writer, "{}", value)?;
            }
            Literal::Nat(value) => {
                write!(writer, "{}", value)?;
            }
            Literal::Int(value) => {
                write!(writer, "{}", value)?;
            }
            // Literal::BitVec(value) => {
            //    write!(writer, "{}", )?;
            // }
        }
        Ok(())
    }
}

impl UnaryOp {
    fn write_to<T: Write> (&self, writer: &mut Writer<T>) -> std::io:: Result<()> {
        match self {
            // Logical negation
            UnaryOp::Not => write!(writer, "!"),

            // Arithmetic negation
            UnaryOp::Neg => write!(writer, "-"),
        }
    }
}


impl BinaryOp {
    fn write_to<T: Write> (&self, writer: &mut Writer<T>) -> std::io:: Result<()> {
        match self {
            // Logical And
            BinaryOp::And => write!(writer, "/\\"),

            // Logical Or
            BinaryOp::Or => write!(writer, "\\/"),

            // Arithmetic Addition (+)
            BinaryOp::Add => write!(writer, "+"),

            // Arithmetic Subtraction (-)
            BinaryOp::Sub => write!(writer, "-"),

            // Arithmetic multiplication (*)
            BinaryOp::Mul => write!(writer, "*"),

            // Arithmetic division (/)
            BinaryOp::Div => write!(writer, "/"),

            // Equality TODO: decidable_eq?
            BinaryOp::Eq => write!(writer, "="),

            // Inequality
            BinaryOp::Neq => write!(writer, "=/="),

            // Less than
            BinaryOp::Lt => write!(writer, "<"),

            // Greater than
            BinaryOp::Gt => write!(writer, ">"),

            // Less than or equal
            BinaryOp::Lte => write!(writer, "<="),

            // Greater than or equal
            BinaryOp::Gte => write!(writer, ">="),
        }
    }
}


pub fn write_expr(e: &Expr) -> String {
    let mut buf = Vec::new();
    let mut writer = writer::Writer::new(&mut buf);
    e.write_to(&mut writer).unwrap();
    String::from_utf8(buf).unwrap()
}

#[cfg(test)]
mod tests {
    use crate::lean_program::Stmt::Assignment;
    use super::*;

    #[test]
    fn sample_program() {
        let program = LeanProgram {
            constants: Vec::new(),
            variables: Vec::new(),
            functions: vec![Function {
                name: "main".to_string(),
                parameters: Vec::new(),
                //Todo: how to have multiple hypothesis -- Option/Vec?
                // One way could be to always have `true` as a hypothesis (to have vec)
                hypothesis: None,
                return_type: Some(Type::Int),
                body: vec![
                        Stmt::Assignment {
                            variable: "x".to_string(),
                            value: Expr::Literal(Literal::Int(1.into())),
                        },
                        Stmt::Assignment {
                            variable: "y".to_string(),
                            value: Expr::Literal(Literal::Int(2.into())),
                        },
                        Stmt::IfThenElse {
                            cond: Expr::BinaryOp {
                                op: BinaryOp::Eq,
                                left: Box::new(Expr::Variable { name: "x".to_string() }),
                                right: Box::new(Expr::Literal(Literal::Int(1.into()))),
                            },
                            then_branch: Box::new(Stmt::Assignment {
                                variable: "y".to_string(),
                                value: Expr::Literal(Literal::Int(5.into())),
                            }),
                            // else_branch: None,
                            else_branch: Some(Box::new(Stmt::Assignment {
                                variable: "y".to_string(),
                                value: Expr::Literal(Literal::Int(10.into())),
                            })),
                        },
                        Stmt::IfThenElse {
                            cond: Expr::UnaryOp {op: UnaryOp::Not, operand: Box::from(Expr::BinaryOp {
                                op: BinaryOp::Eq,
                                left: Box::new(Expr::Variable { name: "y".to_string() }),
                                right: Box::new(Expr::Literal(Literal::Int(5.into()))),
                            })
                            },
                            then_branch: Box::new(Stmt::Return {expr: Expr::ExceptError},
                            ),
                            else_branch: None,
                        },
                        Stmt::Return {expr: Expr::Variable { name: "y".to_string() }},
                        // Stmt::Assert {
                        //     condition: Expr::BinaryOp {
                        //         op: BinaryOp::Eq,
                        //         left: Box::new(Expr::Variable { name: "y".to_string() }),
                        //         right: Box::new(Expr::Literal(Literal::Int(2.into()))),
                        //     },
                        // },
                        // Stmt::If {
                        //     condition: Expr::BinaryOp {
                        //         op: BinaryOp::Lt,
                        //         left: Box::new(Expr::Variable { name: "x".to_string() }),
                        //         right: Box::new(Expr::Variable { name: "y".to_string() }),
                        //     },
                        //     body: Box::new(Stmt::Assignment {
                        //         variable: "z".to_string(),
                        //         value: Expr::Literal(Literal::Bool(true)),
                        //     }),
                        //     else_body: Some(Box::new(Stmt::Assignment {
                        //         variable: "z".to_string(),
                        //         value: Expr::Literal(Literal::Bool(false)),
                        //     })),
                        // },
                    ],
            }],
            theorems: Vec::new(),
        };

        let mut v = Vec::new();
        program.write_to(&mut v).unwrap();
        let program_text = String::from_utf8(v).unwrap().to_string();

        // todo: issue with indentation
        let expected = String::from(
            "\
-- Functions definition:
def main : Int := Id.run do
  x := 1
  y := 2
  if x = 1 then
    y := 5
  else
    y := 10
  if !(y = 5) then
    return Except.error
  return y
",
        );
        assert_eq!(program_text, expected);
    }
}

/*
def fun (x: Int) := Id.run do
    x:= 1
return x

// for every function return resust

theorem x_equals_1 : fun x = 1:= by
*/