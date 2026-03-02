use pest::iterators::Pair;

use crate::Rule;

/// The root of lobotomy's abstract syntax tree.
#[derive(Debug)]
pub struct Program {
    pub statements: Vec<Statement>,
}
impl Program {
    pub fn from_pair(p: Pair<'_, Rule>) -> Self {
        if p.as_rule() != Rule::program {
            panic!("wrong rule type for program: {:?}", p.as_rule());
        }

        let mut statements: Vec<Statement> = Vec::new();

        for pair in p.into_inner() {
            statements.push(Statement::from_pair(pair));
        }

        Self { statements }
    }
}

#[derive(Debug)]
pub enum Statement {
    Assignment(Assignment),
    While(While),
    If(If),
    Read(Read),
    Print(Print),
}
impl Statement {
    pub fn from_pair(p: Pair<'_, Rule>) -> Self {
        if p.as_rule() != Rule::statement {
            panic!("wrong rule type for statement: {:?}", p.as_rule());
        }

        let inner_pair = p.into_inner().nth(0).unwrap();
        let rule = inner_pair.as_rule();

        match rule {
            Rule::assignment => Self::Assignment(Assignment::from_pair(inner_pair)),
            Rule::r#while => Self::While(While::from_pair(inner_pair)),
            Rule::r#if => Self::If(If::from_pair(inner_pair)),
            Rule::read => Self::Read(Read::from_pair(inner_pair)),
            Rule::print => Self::Print(Print::from_pair(inner_pair)),
            _ => panic!("wrong inner rule type for statement: {:?}", rule),
        }
    }
}

#[derive(Debug)]
pub struct Assignment {
    pub dest: Iden,
    pub src: BExpr,
}
impl Assignment {
    pub fn from_pair(p: Pair<'_, Rule>) -> Self {
        if p.as_rule() != Rule::assignment {
            panic!("wrong rule type for assignment: {:?}", p.as_rule());
        }

        let mut inner_pairs = p.into_inner();

        let dest = Iden::from_pair(inner_pairs.next().unwrap());
        let src = BExpr::from_pair(inner_pairs.next().unwrap());

        Self { dest, src }
    }
}

#[derive(Debug)]
pub struct While {
    pub bexpr: BExpr,
    pub body: Program,
}
impl While {
    pub fn from_pair(p: Pair<'_, Rule>) -> Self {
        if p.as_rule() != Rule::r#while {
            panic!("wrong rule type for while: {:?}", p.as_rule());
        }

        let mut inner_pairs = p.into_inner();

        let bexpr = BExpr::from_pair(inner_pairs.next().unwrap());
        let body = Program::from_pair(inner_pairs.next().unwrap());

        Self { bexpr, body }
    }
}

#[derive(Debug)]
pub struct If {
    pub bexpr: BExpr,
    pub body: Program,
}
impl If {
    pub fn from_pair(p: Pair<'_, Rule>) -> Self {
        if p.as_rule() != Rule::r#if {
            panic!("wrong rule type for if: {:?}", p.as_rule());
        }

        let mut inner_pairs = p.into_inner();

        let bexpr = BExpr::from_pair(inner_pairs.next().unwrap());
        let body = Program::from_pair(inner_pairs.next().unwrap());

        Self { bexpr, body }
    }
}

#[derive(Debug)]
pub struct Read {
    pub iden: Iden,
}
impl Read {
    pub fn from_pair(p: Pair<'_, Rule>) -> Self {
        if p.as_rule() != Rule::read {
            panic!("wrong rule type for read: {:?}", p.as_rule())
        }

        let iden = Iden::from_pair(p.into_inner().nth(0).unwrap());

        Self { iden }
    }
}

#[derive(Debug)]
pub struct Print {
    pub bexpr: BExpr,
}
impl Print {
    pub fn from_pair(p: Pair<'_, Rule>) -> Self {
        if p.as_rule() != Rule::print {
            panic!("wrong rule type for print: {:?}", p.as_rule())
        }

        let bexpr = BExpr::from_pair(p.into_inner().nth(0).unwrap());

        Self { bexpr }
    }
}

#[derive(Debug)]
pub struct Iden {
    pub name: String,
}
impl Iden {
    pub fn from_pair(p: Pair<'_, Rule>) -> Self {
        if p.as_rule() != Rule::iden {
            panic!("wrong rule type for iden: {:?}", p.as_rule());
        }

        Self {
            name: p.as_str().trim().to_owned(),
        }
    }
}

/// Binary expressions (&&, ||)
#[derive(Debug)]
pub struct BExpr {
    pub comp: Comp,
    pub op: Option<(BExprOp, Box<BExpr>)>,
}
impl BExpr {
    pub fn from_pair(p: Pair<'_, Rule>) -> Self {
        if p.as_rule() != Rule::bexpr {
            panic!("wrong rule type for bexpr: {:?}", p.as_rule());
        }

        let mut inner_rules = p.into_inner();
        let comp = Comp::from_pair(inner_rules.next().unwrap());

        let op = if let (Some(a), Some(b)) = (inner_rules.next(), inner_rules.next()) {
            Some((BExprOp::from_pair(a), Box::new(BExpr::from_pair(b))))
        } else {
            None
        };

        Self { comp, op }
    }
}

#[derive(Debug)]
pub enum BExprOp {
    And,
    Or,
}
impl BExprOp {
    pub fn from_pair(p: Pair<'_, Rule>) -> Self {
        if p.as_rule() != Rule::bexpr_op {
            panic!("wrong rule type for bexpr_op: {:?}", p.as_rule());
        }

        match p.as_str() {
            "&&" => Self::And,
            "||" => Self::Or,
            op => panic!("invalid bexpr op: {}", op),
        }
    }
}

/// Comparison expressions such as "#a > 5", "#c == #d", etc.
#[derive(Debug)]
pub struct Comp {
    pub expr: Expr,
    pub op: Option<(CompOp, Box<Comp>)>,
}
impl Comp {
    pub fn from_pair(p: Pair<'_, Rule>) -> Self {
        if p.as_rule() != Rule::comp {
            panic!("wrong rule type for comp: {:?}", p.as_rule());
        }

        let mut inner_rules = p.into_inner();
        let expr = Expr::from_pair(inner_rules.next().unwrap());

        let op = if let (Some(a), Some(b)) = (inner_rules.next(), inner_rules.next()) {
            Some((CompOp::from_pair(a), Box::new(Comp::from_pair(b))))
        } else {
            None
        };

        Self { expr, op }
    }
}

#[derive(Debug)]
pub enum CompOp {
    /// Equals: `==`
    Eq,
    /// Not equals: `!=`
    NotEq,
    /// Greater than: `>`
    Gt,
    /// Less than: `<`
    Lt,
    /// Greater than or equals: `>=`
    Geq,
    /// Less than or equals: `<=`
    Leq,
}
impl CompOp {
    pub fn from_pair(p: Pair<'_, Rule>) -> Self {
        if p.as_rule() != Rule::bexpr_op {
            panic!("wrong rule type for comp_op: {:?}", p.as_rule());
        }

        match p.as_str() {
            "==" => Self::Eq,
            "!-" => Self::NotEq,
            ">" => Self::Gt,
            "<" => Self::Lt,
            ">=" => Self::Geq,
            "<=" => Self::Leq,
            op => panic!("invalid bexpr op: {}", op),
        }
    }
}

#[derive(Debug)]
pub struct Expr {
    pub factor: Factor,
    pub op: Option<(ExprOp, Box<Expr>)>,
}
impl Expr {
    pub fn from_pair(p: Pair<'_, Rule>) -> Self {
        if p.as_rule() != Rule::expr {
            panic!("wrong rule type for expr: {:?}", p.as_rule());
        }

        let mut inner_rules = p.into_inner();
        let factor = Factor::from_pair(inner_rules.next().unwrap());

        let op = if let (Some(a), Some(b)) = (inner_rules.next(), inner_rules.next()) {
            Some((ExprOp::from_pair(a), Box::new(Expr::from_pair(b))))
        } else {
            None
        };

        Self { factor, op }
    }
}

#[derive(Debug)]
pub enum ExprOp {
    Add,
    Subtract,
}
impl ExprOp {
    pub fn from_pair(p: Pair<'_, Rule>) -> Self {
        if p.as_rule() != Rule::expr_op {
            panic!("wrong rule type for expr: {:?}", p.as_rule());
        }

        match p.as_str() {
            "+" => Self::Add,
            "-" => Self::Subtract,
            op => panic!("invalid expr op: {}", op),
        }
    }
}

#[derive(Debug)]
pub struct Factor {
    pub unary: Unary,
    pub op: Option<(FactorOp, Box<Factor>)>,
}
impl Factor {
    pub fn from_pair(p: Pair<'_, Rule>) -> Self {
        if p.as_rule() != Rule::factor {
            panic!("wrong rule type for factor: {:?}", p.as_rule());
        }

        let mut inner_rules = p.into_inner();
        let unary = Unary::from_pair(inner_rules.next().unwrap());

        let op = if let Some(a) = inner_rules.next() {
            // Op is always multiply since that's the only operation supported at
            // this precedence level. Since that's the only supported operation here,
            // there's no grammar rule matching the operator. If support for division
            // is added, that will have to change
            Some((FactorOp::Multiply, Box::new(Factor::from_pair(a))))
        } else {
            None
        };

        Self { unary, op }
    }
}

#[derive(Debug)]
pub enum FactorOp {
    Multiply,
}

#[derive(Debug)]
pub enum Unary {
    Term(Term),
    Unary { op: UnaryOp, unary: Box<Unary> },
}
impl Unary {
    pub fn from_pair(p: Pair<'_, Rule>) -> Self {
        if p.as_rule() != Rule::unary {
            panic!("wrong rule type for unary: {:?}", p.as_rule());
        }

        let mut inner_pairs = p.into_inner();

        let first_inner_pair = inner_pairs.next().unwrap();
        match first_inner_pair.as_rule() {
            Rule::unary_op => Self::Unary {
                // Like with the factor_op rule, there's currently just one
                op: UnaryOp::Not,
                unary: Box::new(Unary::from_pair(inner_pairs.next().unwrap())),
            },
            Rule::term => Self::Term(Term::from_pair(first_inner_pair)),
            rule => panic!("Invalid inner rule for unary: {:?}", rule),
        }
    }
}

#[derive(Debug)]
pub enum UnaryOp {
    /// Boolean not operator. Example: `!#a`
    Not,
}

#[derive(Debug)]
pub enum Term {
    Literal(Literal),
    Iden(Iden),
    Expr(Box<Expr>),
}
impl Term {
    pub fn from_pair(p: Pair<'_, Rule>) -> Self {
        if p.as_rule() != Rule::term {
            panic!("wrong rule type for term: {:?}", p.as_rule());
        }

        let inner_pair = p.into_inner().nth(0).unwrap();
        let rule = inner_pair.as_rule();

        match rule {
            Rule::literal => Self::Literal(Literal::from_pair(inner_pair)),
            Rule::iden => Self::Iden(Iden::from_pair(inner_pair)),
            Rule::expr => Self::Expr(Box::new(Expr::from_pair(inner_pair))),
            _ => panic!("wrong inner rule type for term: {:?}", rule),
        }
    }
}

#[derive(Debug)]
pub struct Literal {
    pub value: u8,
}
impl Literal {
    pub fn from_pair(p: Pair<'_, Rule>) -> Self {
        if p.as_rule() != Rule::literal {
            panic!("wrong rule type for literal: {:?}", p.as_rule());
        }

        let s = p.as_str();

        let value: u8 = if s.starts_with("'") && s.ends_with("'") {
            s.as_bytes()[1]
        } else {
            s.parse().unwrap()
        };

        Self { value }
    }
}
