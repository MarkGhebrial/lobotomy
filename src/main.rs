use std::fs;

use pest::{
    Parser,
    iterators::Pair,
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
            name: p.as_str().trim().to_owned(),
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

#[derive(Debug)]
enum Instruction {
    /// Move the cell pointer to the given symbol. Symbols are specified as indexes
    /// into the symbol table.
    ///
    /// This translates into Brainf*ck as repeated ">" or "<" instructions. The amount
    /// to move the cell pointer = symbol address - current cell address. This requires
    /// keeping track of the current cell address
    Goto { symbol_index: SymbolIndex },

    /// Increment the current cell. This translates to Brainf*ck as repeated "+"
    /// instructions.
    Incr { n: u8 },
    /// Decrement the current cell. This translates to Brainf*ck as repeated "-"
    /// instructions.
    Decr { n: u8 },

    /// Wrap the contained instructions in "[" and "]"
    Loop { instructions: Vec<Instruction> },

    /// Print the contents of the current cell to stdout. This translates to Brainf*ck
    /// as the "." instruction.
    Print,
    /// Overwrite the contents of the current cell with a byte from stdin. This
    /// translates to Brainf*ck as the "," instruction.
    Read,
}

#[derive(Debug)]
struct SymbolTable {
    table: Vec<SymbolTableEntry>,
}
impl SymbolTable {
    pub fn new() -> Self {
        Self { table: Vec::new() }
    }

    pub fn get(&self, index: SymbolIndex) -> &SymbolTableEntry {
        self.table.get(index).unwrap()
    }

    fn push_symbol(&mut self, sym: SymbolTableEntry) -> SymbolIndex {
        self.table.push(sym);
        self.table.len() - 1
    }

    /// Add a new (unnamed) symbol to the symbol table and return its index.
    pub fn new_internal_symbol(&mut self) -> SymbolIndex {
        self.push_symbol(SymbolTableEntry {
            external_name: None,
            symbol_type: SymbolType::Variable,
        })
    }

    /// Given an identifier
    pub fn get_or_insert_symbol(&mut self, iden: Iden) -> SymbolIndex {
        // If there's a named symbol in the table with the same name as the identifier ...
        for (i, entry) in self.table.iter().enumerate() {
            if let Some(name) = &entry.external_name
                && name == &iden.name
            {
                // ...return the index of that symbol
                return i;
            }
        }
        // ...else, add a new symbol
        self.push_symbol(SymbolTableEntry {
            external_name: Some(iden.name),
            symbol_type: SymbolType::Variable,
        })
    }
}

// type SymbolTable = Vec<SymbolTableEntry>;
type SymbolIndex = usize;

// TODO: Maybe rename this to SymbolMutability.
#[derive(Debug)]
enum SymbolType {
    Variable,
    Constant,
}

#[derive(Debug)]
struct SymbolTableEntry {
    pub external_name: Option<String>,
    pub symbol_type: SymbolType,
}

/// Given an AST node of type Program and a symbol table, generate a list of instructions.
fn transform_program(p: Program, symbol_table: &mut SymbolTable) -> Vec<Instruction> {
    let mut instrs: Vec<Instruction> = Vec::new();

    for statement in p.statements {
        instrs.append(&mut transform_statement(statement, symbol_table));
    }

    instrs
}

fn transform_statement(s: Statement, symbol_table: &mut SymbolTable) -> Vec<Instruction> {
    match s {
        Statement::Assignment(a) => transform_assignment(a, symbol_table),
        Statement::While(w) => transform_while(w, symbol_table),
        Statement::If(i) => transform_if(i, symbol_table),
        Statement::Read(r) => transform_read(r, symbol_table),
        Statement::Print(p) => transform_print(p, symbol_table),
    }
}

/// Transform an assignment node of the AST to instructions.
///
/// Assignment instructions =
fn transform_assignment(a: Assignment, symbol_table: &mut SymbolTable) -> Vec<Instruction> {
    let dest = transform_iden(a.dest, symbol_table);
    let (expr_result, mut expr_instrs) = transform_expr(a.src, symbol_table);

    // Copy the expression result into the destination symbol
    let mut copy_instrs = copy(expr_result, dest, symbol_table);

    expr_instrs.append(&mut copy_instrs);
    expr_instrs
}

/// Take an Iden node of the AST and insert it into the symbol table, returning the index of the new symbol.
fn transform_iden(i: Iden, symbol_table: &mut SymbolTable) -> SymbolIndex {
    symbol_table.get_or_insert_symbol(i)
}

fn transform_expr(e: Expr, symbol_table: &mut SymbolTable) -> (SymbolIndex, Vec<Instruction>) {
    // Evaluate the left hand side of the expression
    let (lhs_symbol, mut instrs) = transform_factor(e.factor, symbol_table);

    let mut output_symbol = lhs_symbol;

    use Instruction::*;
    // Does the expression have a rhs?
    if let Some((op, rhs_expr)) = e.op {
        // If so, compute that expression
        let (left_expr_result, mut left_expr_instrs) = transform_expr(*rhs_expr, symbol_table);
        instrs.append(&mut left_expr_instrs);

        // Copy the result of the expression into a temporary variable
        let temp = symbol_table.new_internal_symbol();
        instrs.append(&mut copy(left_expr_result, temp, symbol_table));

        // Create a new symbol to store the result 
        output_symbol = symbol_table.new_internal_symbol();
        instrs.append(&mut copy(lhs_symbol, output_symbol, symbol_table));

        // Do the actual operation
        instrs.append(&mut vec![
            // while (temp) { temp -= 1; op_result += 1; }
            Goto { symbol_index: temp },
            Loop {
                instructions: vec![
                    Decr { n: 1 },
                    Goto {
                        symbol_index: output_symbol,
                    },
                    match op {
                        ExprOp::Add => Incr { n: 1 },
                        ExprOp::Subtract => Decr { n: 1 },
                    },
                    Goto { symbol_index: temp },
                ],
            },
        ]);
    }

    (output_symbol, instrs)
}

fn transform_factor(f: Factor, symbol_table: &mut SymbolTable) -> (SymbolIndex, Vec<Instruction>) {
    let (lhs_symbol, instrs) = transform_term(f.term, symbol_table);

    let output_symbol = lhs_symbol;

    if let Some((_op, _factor)) = f.op {
        unimplemented!("multiplication not implemented in the compiler (yet!)");
    }

    (output_symbol, instrs)
}

fn transform_term(t: Term, symbol_table: &mut SymbolTable) -> (SymbolIndex, Vec<Instruction>) {
    match t {
        // For literal terms, we just create a new internal symbol and increment it to its
        // required constant value. This means that *every* literal
        // in the code gets its own symbol, which is potentially wasteful. This does, however,
        // possibly mitigate the need to move the cell pointer large amounts to access far-away
        // literal values.
        Term::Literal(literal) => {
            let symbol = symbol_table.new_internal_symbol();

            use Instruction::*;
            let instrs: Vec<Instruction> = vec![
                Goto { symbol_index: symbol },
                Incr { n: literal.value }
            ];

            (symbol, instrs)
        },
        Term::Iden(iden) => (transform_iden(iden, symbol_table), Vec::new()),
        Term::Expr(expr) => transform_expr(*expr, symbol_table),
    }
}

/// Generate instructions to copy the value of one symbol to another symbol.
fn copy(src: SymbolIndex, dest: SymbolIndex, symbol_table: &mut SymbolTable) -> Vec<Instruction> {
    let mut instrs: Vec<Instruction> = Vec::new();

    let temp = symbol_table.new_internal_symbol();

    use Instruction::*;
    instrs.append(&mut vec![
        // Set the destination to zero
        Goto { symbol_index: dest },
        Loop {
            instructions: vec![Decr { n: 1 }],
        },
        // Equivalent pseudocode: while (src) { src -= 1; dest += 1; temp += 1; }
        Goto { symbol_index: src },
        Loop {
            instructions: vec![
                Decr { n: 1 },
                Goto { symbol_index: dest },
                Incr { n: 1 },
                Goto { symbol_index: temp },
                Incr { n: 1 },
                Goto { symbol_index: src },
            ],
        },
        // while (temp) { temp -= 1; src += 1; }
        Goto { symbol_index: temp },
        Loop {
            instructions: vec![
                Decr { n: 1 },
                Goto { symbol_index: src },
                Incr { n: 1 },
                Goto { symbol_index: temp },
            ],
        },
    ]);

    instrs
}

fn transform_while(w: While, symbol_table: &mut SymbolTable) -> Vec<Instruction> {
    use Instruction::*;

    unimplemented!("while loops are broken!");
    
    // Evaluate the expression
    let (expr_symbol, mut instrs) = transform_expr(w.expr, symbol_table);
    
    let loop_symbol = symbol_table.new_internal_symbol();
    // Copy the expression result to the new loop symbol
    instrs.append(&mut copy(expr_symbol, loop_symbol, symbol_table));
    // Move the cell pointer to the loop symbol
    instrs.push(Goto { symbol_index: loop_symbol });

    // Execute the loop contents, then move the cell pointer back to the expression result
    let mut loop_body = transform_program(w.body, symbol_table);
    // loop_body.append(&mut transform_expr(w.expr, symbol_table));
    loop_body.append(&mut vec![
        Goto { symbol_index: loop_symbol },
    ]);
    
    instrs.push(Loop { instructions: loop_body });

    instrs
}

fn transform_if(i: If, symbol_table: &mut SymbolTable) -> Vec<Instruction> {
    todo!()
}

fn transform_read(r: Read, symbol_table: &mut SymbolTable) -> Vec<Instruction> {
    let symbol = transform_iden(r.iden, symbol_table);
    
    use Instruction::*;
    vec![
        Goto { symbol_index: symbol },
        Read,
    ]
}

fn transform_print(p: Print, symbol_table: &mut SymbolTable) -> Vec<Instruction> {
    let (expr_symbol, mut instrs) = transform_expr(p.expr, symbol_table);

    use Instruction::*;
    instrs.append(&mut vec![
        Goto { symbol_index: expr_symbol },
        Print
    ]);

    instrs
}

fn main() {
    let file_name = std::env::args().nth(1).unwrap();

    let file_contents = &fs::read_to_string(file_name).unwrap();
    let mut parse_result = MyParser::parse(Rule::program, file_contents).unwrap();

    // Convert the parse tree to an AST
    let program = Program::from_pair(parse_result.nth(0).unwrap());
    println!("{:#?}", program);

    // Create the symbol table
    let mut symbol_table: SymbolTable = SymbolTable::new();
    // Transform the AST to a list of Instructions
    let instructions = transform_program(program, &mut symbol_table);

    println!("SYMBOL TABLE");
    println!("{:#?}", symbol_table);

    println!("INSTRUCTIONS");
    println!("{:#?}", instructions);
}
