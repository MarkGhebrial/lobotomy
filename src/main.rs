use std::fs;

use pest::{
    Parser, RuleType,
    iterators::{Pair, Pairs},
};
use pest_derive::Parser;

#[derive(Parser)]
#[grammar = "grammar.pest"] // relative to src
struct MyParser;

/// The root of lobotomy's abstract syntax tree.
#[derive(Debug)]
struct Program {
    statements: Vec<Statement>,
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
enum Statement {
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
struct Assignment {
    dest: Iden,
    src: Expr,
}
impl Assignment {
    pub fn from_pair(p: Pair<'_, Rule>) -> Self {
        if p.as_rule() != Rule::assignment {
            panic!("wrong rule type for assignment: {:?}", p.as_rule());
        }

        let mut inner_pairs = p.into_inner();

        let dest = Iden::from_pair(inner_pairs.next().unwrap());
        let src = Expr::from_pair(inner_pairs.next().unwrap());

        Self { dest, src }
    }
}

#[derive(Debug)]
struct While {
    expr: Expr,
    body: Program,
}
impl While {
    pub fn from_pair(p: Pair<'_, Rule>) -> Self {
        if p.as_rule() != Rule::r#while {
            panic!("wrong rule type for while: {:?}", p.as_rule());
        }

        let mut inner_pairs = p.into_inner();

        let expr = Expr::from_pair(inner_pairs.next().unwrap());
        let body = Program::from_pair(inner_pairs.next().unwrap());

        Self { expr, body }
    }
}

#[derive(Debug)]
struct If {
    expr: Expr,
    body: Program,
}
impl If {
    pub fn from_pair(p: Pair<'_, Rule>) -> Self {
        if p.as_rule() != Rule::r#if {
            panic!("wrong rule type for if: {:?}", p.as_rule());
        }

        let mut inner_pairs = p.into_inner();

        let expr = Expr::from_pair(inner_pairs.next().unwrap());
        let body = Program::from_pair(inner_pairs.next().unwrap());

        Self { expr, body }
    }
}

#[derive(Debug)]
struct Read {
    iden: Iden,
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
struct Print {
    expr: Expr,
}
impl Print {
    pub fn from_pair(p: Pair<'_, Rule>) -> Self {
        if p.as_rule() != Rule::print {
            panic!("wrong rule type for print: {:?}", p.as_rule())
        }

        let expr = Expr::from_pair(p.into_inner().nth(0).unwrap());

        Self { expr }
    }
}

#[derive(Debug)]
struct Iden {
    name: String,
}
impl Iden {
    pub fn from_pair(p: Pair<'_, Rule>) -> Self {
        if p.as_rule() != Rule::iden {
            panic!("wrong rule type for iden: {:?}", p.as_rule());
        }

        Self {
            name: p.as_str().to_owned(),
        }
    }
}

#[derive(Debug)]
struct Expr {
    factor: Factor,
    op: Option<(ExprOp, Box<Expr>)>,
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
enum ExprOp {
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
            _ => panic!("invalid expr op: {}", p.as_str()),
        }
    }
}

#[derive(Debug)]
struct Factor {
    term: Term,
    op: Option<(FactorOp, Box<Factor>)>,
}
impl Factor {
    pub fn from_pair(p: Pair<'_, Rule>) -> Self {
        if p.as_rule() != Rule::factor {
            panic!("wrong rule type for factor: {:?}", p.as_rule());
        }

        let mut inner_rules = p.into_inner();
        let term = Term::from_pair(inner_rules.next().unwrap());

        let op = if let Some(a) = inner_rules.next() {
            // Op is always multiply since that's the only operation supported at
            // this precedence level. Since that's the only supported operation here,
            // there's no grammar rule matching the operator. If support for division
            // is added, that will have to change
            Some((FactorOp::Multiply, Box::new(Factor::from_pair(a))))
        } else {
            None
        };

        Self { term, op }
    }
}

#[derive(Debug)]
enum FactorOp {
    Multiply,
}

#[derive(Debug)]
enum Term {
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
struct Literal {
    value: u8,
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

fn main() {
    println!("Hello, world!");

    let file_contents = &fs::read_to_string("test.lobo").unwrap();
    let mut parse_result = MyParser::parse(Rule::program, file_contents).unwrap();

    let program = Program::from_pair(parse_result.nth(0).unwrap());

    // println!("{:#?}", parse_result);

    println!("{:#?}", program)
}
