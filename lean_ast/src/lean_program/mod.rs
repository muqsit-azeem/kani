// Copyright Kani Contributors
// SPDX-License-Identifier: Apache-2.0 OR MIT

//! A module that defines the AST of a Lean program and provides methods for
//! creating nodes of the AST.
//!

mod writer;
use num_bigint::BigInt;
use num_bigint::BigUint;

/// Lean types
pub enum Type {
    /// Boolean
    Bool, //  true or false

    /// Naturals (TODO: Do we need this?)  -- two possibilities -- 1) BV for lean (being developed within AWS) 2)
    Nat,
    // unsinged -> nats
    // signed -> integers; i8 in rust is bv

    /// Integer
    Int,

    // TODO: Inductive data types -- Enums

    /// Generic type, for instance: `T`
    ParameterType { name: String},

    /// Function type
    FunctionType {key: Box<Type>, value: Box<Type>},


    Product {typ1: Box<Type>, typ2: Box<Type>}
    // InputFunction {key: Box<Type>, value: Box<Type>},

    // (inductive:)
    // Struct would be Struct
}


/// Lean literals
pub enum Literal {
    ///Boolean values: `true` or `false`
    Bool(bool),

    /// Naturals
    Nat(BigUint),

    /// Integers
    Int(BigInt),
}

/// Lean parameters
pub struct Parameter {
    name: String,
    typ: Type,
}

impl Parameter {
    pub fn new(name: String, typ: Type) -> Self {
        Self { name, typ }
    }
}


pub struct  Hypothesis {
    name: String,
    pred : Expr,
}


impl Hypothesis {
    pub fn new(name: String, pred: Expr) -> Self {
        Self {name, pred}
    }
}

/// Unary Operators
pub enum UnaryOp {
    /// Logical negation (`~` or `\lnot`)
    Not,

    /// Arithmetic negative
    Neg,

   // TODO:Where does the quantifiers (\forall and \exits) go?
}


/// Binary Operators

pub enum BinaryOp {
    /// Logical AND (`/\` or `\land`)
    And,

    /// Logical OR (`\/` or `\lor`)
    Or,

    /// Arithmetic Addition (+)
    Add,

    /// Arithmetic Subtraction (-)
    Sub,

    /// Arithmetic multiplication (*)
    Mul,

    /// Arithmetic multiplication (/)
    Div,

    /// Equality
    Eq,

    /// Inequality
    Neq,

    /// Less than
    Lt,

    /// Greater than
    Gt,

    /// Less than or equal
    Lte,

    /// Greater than or equal
    Gte,
}


pub enum Expr {
    /// Literal (constant) expression
    Literal(Literal),

    /// Variable
    Variable { name: String },

    /// Unary operation
    UnaryOp { op: UnaryOp, operand:Box<Expr> },

    /// Binary operation
    BinaryOp { op: BinaryOp, left: Box<Expr>, right: Box<Expr> },

    /// Function call
    /// In Lean, functions are first class citizens meaning that
    /// they are used and manipulated just like any other data, e.g. Ints, Strings.
    /// Key points: Can be assigned to variables, passed as args, and
    /// can be return value of a function
    /// Functions are pure -- `without` side effects -- map input to output deterministically
    FunctionCall { name: String, arguments: Vec<Expr> },

    ExceptOk,

    ExceptError,
}

/// Lean Statement
pub enum Stmt {
    /// Expression statement
    /// Expr(Expr),

    /// Assignment statement
    Assignment { variable: String, value: Expr },

    /// Declaration statement
    /// constant b : ℕ
    /// https://lean-lang.org/reference/declarations.html
    /// constant c : α : declares a constant named c of type α, where c is a declaration name.
    /// axiom c : α : alternative syntax for constant
    /// def c : α := t : defines c to denote t, which should have type α.
    /// theorem c : p := t : similar to def, but intended to be used when p is a proposition.
    /// lemma c : p := t : alternative syntax for theorem
    Declaration { name: String, typ: Option<Type>, expr: Expr},

    /// Statement block: `{ statements }`
    Block { statements: Vec<Stmt> },

    //todo: for now assuming that `else` will always be there
    // which is not true -- make `else` optional
    IfThenElse {cond: Expr, then_branch: Box<Stmt>, else_branch: Option<Box<Stmt>>},

    Return { expr: Expr},

    /// Lemmata are statements
    Lem(Lemma),

    /// Theorem are statements
    Thm(Theorem),

    /// Axioms are statements
    Axm(Axiom),

    //TODO: We decided to go Monadic route -- Expr ARE NOT Statments

    // /// If statement: `if (condition) { body } else { else_body }`
    // If { condition: Expr, body: Box<Stmt>, else_body: Option<Box<Stmt>> },
    //
    // /// While statement: `while (condition) { body }`
    // While { condition: Expr, body: Box<Stmt> },
}

impl Expr {
    pub fn literal(l: Literal) -> Self {
        Expr::Literal(l)
    }

    pub fn function_call(name: String, arguments: Vec<Expr>) -> Self {
        Expr::FunctionCall { name, arguments }
    }

}


/// Lean function definition
pub struct Function {
    name: String,
    parameters: Vec<Parameter>, // (a: Type)
    hypothesis:Option<Hypothesis>, // (h: Expr)
    return_type: Option<Type>, // : Type
    /// allowing side effect means that we have statements in body
    /// TODO: Always use MONADS --> Id.run do
    body: Vec<Stmt>, // Vec<statements>
}


/// Function definition
impl Function {
    pub fn new(
        name: String,
        parameters: Vec<Parameter>,
        hypothesis: Option<Hypothesis>,
        return_type: Option<Type>,
        body: Vec<Stmt>,
    ) -> Self {
        Function { name, parameters, hypothesis, return_type, body }
    }
}

/// Lean Variables
pub struct Variable {}

/// Lean Constants
pub struct Constant {}

/// Lean Axiom structure
pub struct Axiom {}

/// Lean Lemma structure
pub struct Lemma {}

/// Lean theorem structure
pub struct Theorem {}



/// A Lean program
pub struct LeanProgram {
    // TODO: do we need namespace?

    variables: Vec<Variable>,
    constants: Vec<Constant>,
    functions: Vec<Function>,

    // Apparently, axioms, lemmata and theorems are all statements in Lean
    // TODO: replace all with statements? -- We decided to keep these separate
    // TODO: what is the corresponding construct of axiom in rust?
    // axioms: Vec<Axiom>,

    /// an assert can be translated to either a lemma or theorem,
    /// depending on whether, it's universal truth or
    /// particular to the program states
    //lemmata: Vec<Lemma>,
    theorems: Vec<Theorem>,
}

impl LeanProgram {
    pub fn new() -> Self{
        LeanProgram{
            // global variables
            variables: Vec::new(),

            // global constants
            constants: Vec::new(),

            functions: Vec::new(),

            // TODO -- ASSUMES? -- Are these preconditions? - AS HYPOTHESIS in Lean
            // ingone axioms for now
            // axioms: Vec::new(),

            // // sometimes lemmata are also written as theorem but I have also seen lemma in lean
            //TODO:"why?" --> can we remove lemma altogether however, practically, they seem
            // to have similar meaning as theorem

            // lemmata: Vec::new(),

            // theorems have objects, assumptions, and goal
            // (e.g., objects - x,y: \nat, assumption (denoted h) - h: x = y+2, goal: 2*x = 2*y + 4)
            theorems: Vec::new(),
        }
    }
    pub fn add_function(&mut self, function: Function) {
        self.functions.push(function);
    }
}