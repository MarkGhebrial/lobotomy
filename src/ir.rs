use crate::{SymbolIndex, SymbolTable};

/// Intermediate representation for lobo code. One step above raw brainf*ck code.
#[derive(Debug)]
pub enum Instruction {
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

/// Enumeration of all the commands in Brainf*ck
#[repr(u8)]
pub enum BFCommand {
    ShiftPointerLeft = b'<',  // <
    ShiftPointerRight = b'>', // >
    IncrementCell = b'+',     // +
    DecrementCell = b'-',     // -
    OutputByte = b'.',        // .
    InputByte = b',',         // ,
    JumpForward = b'[',       // [
    JumpBackward = b']',      // ]
}

/// Convert a vector of IR instructions to brainf*ck code. This is a convenience
/// function around [generate_bf].
pub fn convert_ir(ir: &Vec<Instruction>, symbol_table: &SymbolTable) -> Vec<BFCommand> {
    let mut code: Vec<BFCommand> = Vec::new();
    generate_bf(&mut code, &mut 0, symbol_table, ir);
    code
}

/// Given a symbol table and a vector of [Instruction]s, recursively generate the final Brainf*ck
/// code.
fn generate_bf(
    commands: &mut Vec<BFCommand>,
    cell_pointer: &mut usize,
    symbol_table: &SymbolTable,
    instrs: &Vec<Instruction>,
) {
    use BFCommand::*;

    for instr in instrs {
        match instr {
            Instruction::Goto { symbol_index } => {
                // Move the pointer right if it's to the left of the symbol's address.
                if *symbol_index > *cell_pointer {
                    for _ in 0..(*symbol_index - *cell_pointer) {
                        commands.push(ShiftPointerRight);
                    }
                }
                // Move the pointer left if it's to the right of the symbol's address.
                else if *cell_pointer > *symbol_index {
                    for _ in 0..(*cell_pointer - *symbol_index) {
                        commands.push(ShiftPointerLeft);
                    }
                }

                // Keep track of the cell's new location
                *cell_pointer = *symbol_index;
            }
            Instruction::Incr { n } => {
                for _ in 0..*n {
                    commands.push(IncrementCell);
                }
            }
            Instruction::Decr { n } => {
                for _ in 0..*n {
                    commands.push(DecrementCell);
                }
            }
            Instruction::Loop { instructions } => {
                commands.push(JumpForward);
                generate_bf(commands, cell_pointer, symbol_table, instructions);
                commands.push(JumpBackward);
            }
            Instruction::Print => {
                commands.push(OutputByte);
            }
            Instruction::Read => {
                commands.push(InputByte);
            }
        }
    }
}