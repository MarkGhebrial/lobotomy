use std::{
    error::Error,
    fs::{self, File},
    io::Write,
    process::exit,
};

use pest::Parser;
use pest_derive::Parser;

mod ast;
use ast::*;

mod ir;
use ir::*;

mod test;

#[derive(Parser)]
#[grammar = "grammar.pest"] // relative to src
struct MyParser;


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
            // symbol_type: SymbolType::Variable,
        })
    }

    /// Given an identifier
    pub fn get_or_insert_symbol(&mut self, iden: &Iden) -> SymbolIndex {
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
            external_name: Some(iden.name.clone()),
            // symbol_type: SymbolType::Variable,
        })
    }
}

// type SymbolTable = Vec<SymbolTableEntry>;
type SymbolIndex = usize;

// TODO: Maybe rename this to SymbolMutability.
// #[derive(Debug)]
// enum SymbolType {
//     Variable,
//     Constant,
// }

#[derive(Debug)]
struct SymbolTableEntry {
    pub external_name: Option<String>,
}

/// Given an AST node of type Program and a symbol table, generate a list of instructions.
fn transform_program(p: &Program, symbol_table: &mut SymbolTable) -> Vec<Instruction> {
    let mut instrs: Vec<Instruction> = Vec::new();

    for statement in &p.statements {
        instrs.append(&mut transform_statement(statement, symbol_table));
    }

    instrs
}

fn transform_statement(s: &Statement, symbol_table: &mut SymbolTable) -> Vec<Instruction> {
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
fn transform_assignment(a: &Assignment, symbol_table: &mut SymbolTable) -> Vec<Instruction> {
    let dest = transform_iden(&a.dest, symbol_table);

    transform_bexpr(&a.src, dest, symbol_table)
}

/// Take an Iden node of the AST and insert it into the symbol table, returning the index of the new symbol.
fn transform_iden(i: &Iden, symbol_table: &mut SymbolTable) -> SymbolIndex {
    symbol_table.get_or_insert_symbol(i)
}

fn transform_bexpr(
    b: &BExpr,
    target_symbol: SymbolIndex,
    symbol_table: &mut SymbolTable,
) -> Vec<Instruction> {
    todo!()
}

fn transform_expr(
    e: &Expr,
    target_symbol: SymbolIndex,
    symbol_table: &mut SymbolTable,
) -> Vec<Instruction> {
    // Evaluate the left hand side of the expression
    let mut instrs = transform_factor(&e.factor, target_symbol, symbol_table);

    // Does the expression have a rhs?
    if let Some((op, rhs_expr)) = &e.op {
        // If so, compute that expression
        let right_expr_result = symbol_table.new_internal_symbol();
        let mut right_expr_instrs = transform_expr(&rhs_expr, right_expr_result, symbol_table);
        instrs.append(&mut right_expr_instrs);

        // Do the actual operation
        use Instruction::*;
        instrs.append(&mut vec![
            // while (temp) { temp -= 1; op_result += 1; }
            Goto {
                symbol_index: right_expr_result,
            },
            Loop {
                instructions: vec![
                    Decr { n: 1 },
                    Goto {
                        symbol_index: target_symbol,
                    },
                    match op {
                        ExprOp::Add => Incr { n: 1 },
                        ExprOp::Subtract => Decr { n: 1 },
                    },
                    Goto {
                        symbol_index: right_expr_result,
                    },
                ],
            },
        ]);
    }

    instrs
}

fn transform_factor(
    f: &Factor,
    target_symbol: SymbolIndex,
    symbol_table: &mut SymbolTable,
) -> Vec<Instruction> {
    let instrs = transform_unary(&f.unary, target_symbol, symbol_table);

    if let Some((_op, _factor)) = &f.op {
        unimplemented!("multiplication not implemented (yet!)");
    }

    instrs
}

fn transform_unary(
    u: &Unary,
    target_symbol: SymbolIndex,
    symbol_table: &mut SymbolTable,
) -> Vec<Instruction> {
    todo!()
}

fn transform_term(
    t: &Term,
    target_symbol: SymbolIndex,
    symbol_table: &mut SymbolTable,
) -> Vec<Instruction> {
    match t {
        // For literal terms, we just create a new internal symbol and increment it to its
        // required constant value. This means that *every* literal
        // in the code gets its own symbol, which is potentially wasteful. This does, however,
        // possibly mitigate the need to move the cell pointer large amounts to access far-away
        // literal values.
        Term::Literal(literal) => {
            use Instruction::*;
            let instrs: Vec<Instruction> = vec![
                // Move the cell pointer to the address of the target symbol
                Goto {
                    symbol_index: target_symbol,
                },
                // Set the cell to zero
                Loop {
                    instructions: vec![Decr { n: 1 }],
                },
                // Set the value of the cell to the value of the literal
                Incr { n: literal.value },
            ];

            instrs
        }
        Term::Iden(iden) => {
            let symbol = transform_iden(iden, symbol_table);

            copy(symbol, target_symbol, symbol_table)
        }
        Term::Expr(expr) => transform_expr(&expr, target_symbol, symbol_table),
    }
}

/// Generate instructions to copy the value of one symbol to another symbol.
fn copy(src: SymbolIndex, dest: SymbolIndex, symbol_table: &mut SymbolTable) -> Vec<Instruction> {
    let mut instrs: Vec<Instruction> = Vec::new();

    // Copying a symbol to itself does not work.
    if src == dest {
        return instrs;
    }

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

fn transform_while(w: &While, symbol_table: &mut SymbolTable) -> Vec<Instruction> {
    use Instruction::*;

    // Evaluate the loop expression
    let loop_symbol = symbol_table.new_internal_symbol();
    let mut instrs = transform_bexpr(&w.bexpr, loop_symbol, symbol_table);

    // Move the cell pointer to the loop symbol
    instrs.push(Goto {
        symbol_index: loop_symbol,
    });

    // In the loop...
    let mut loop_body = transform_program(&w.body, symbol_table); // ...execute the body of the loop...
    loop_body.append(&mut transform_bexpr(&w.bexpr, loop_symbol, symbol_table)); // ...reevaluate the expression...
    loop_body.push(Goto {
        symbol_index: loop_symbol,
    }); // ...and move the cell pointer back to the expression result.

    instrs.push(Loop {
        instructions: loop_body,
    });

    instrs
}

fn transform_if(i: &If, symbol_table: &mut SymbolTable) -> Vec<Instruction> {
    use Instruction::*;

    let condition_symbol = symbol_table.new_internal_symbol();
    let mut instrs = transform_bexpr(&i.bexpr, condition_symbol, symbol_table);

    let zero_symbol = symbol_table.new_internal_symbol();
    instrs.append(&mut vec![
        Goto {
            symbol_index: zero_symbol,
        },
        Loop {
            instructions: vec![Decr { n: 1 }],
        },
    ]);

    instrs.push(Goto {
        symbol_index: condition_symbol,
    });

    let mut if_body = transform_program(&i.body, symbol_table);
    if_body.push(Goto {
        symbol_index: zero_symbol,
    }); // JMove the cell pointer to the zero symbol so we're guaranteed the loop exits

    instrs.push(Loop {
        instructions: if_body,
    });

    instrs
}

fn transform_read(r: &Read, symbol_table: &mut SymbolTable) -> Vec<Instruction> {
    let symbol = transform_iden(&r.iden, symbol_table);

    use Instruction::*;
    vec![
        Goto {
            symbol_index: symbol,
        },
        Read,
    ]
}

fn transform_print(p: &Print, symbol_table: &mut SymbolTable) -> Vec<Instruction> {
    let expr_result = symbol_table.new_internal_symbol();
    let mut instrs = transform_bexpr(&p.bexpr, expr_result, symbol_table);

    use Instruction::*;
    instrs.append(&mut vec![
        Goto {
            symbol_index: expr_result,
        },
        Print,
    ]);

    instrs
}

pub fn compile(src: &str) -> Result<String, Box<dyn Error>> {
    let mut parse_result = MyParser::parse(Rule::file, src)?;

    // Convert the parse tree to an AST
    let program = Program::from_pair(parse_result.nth(0).unwrap());

    // Create the symbol table
    let mut symbol_table: SymbolTable = SymbolTable::new();
    // Transform the AST to a list of Instructions
    let instructions = transform_program(&program, &mut symbol_table);

    let code = convert_ir(&instructions, &symbol_table);

    // Convert the vector of BFCommands to a string
    Ok(code.into_iter().map(|c| c as u8 as char).collect())
}

fn main() {
    // Parse command line args
    let Some(file_name) = std::env::args().nth(1) else {
        println!("Usage: lobotomy <source_file>");
        exit(0);
    };

    // Read the source file
    let file_contents = &fs::read_to_string(&file_name).unwrap();

    // Compile the code!
    let code = match compile(&file_contents) {
        Ok(c) => c,
        Err(e) => {
            println!("{}", e);
            exit(-1);
        }
    };

    // Write the compiled code to a file called "a.bf"
    let mut output_file = File::create("a.bf").unwrap();
    output_file.write_all(code.as_bytes()).unwrap();
}
