//! Intermediate representation.

use crate::SymbolTable;

#[derive(Debug)]
pub enum Instruction {
    /// Move the imaginary stack pointer to the right. This does not directly translate
    /// to Brainf*ck code, but it does affect which absolute cell address "Goto"
    /// instructions cause the cell pointer to move to.
    ///
    /// Do this before a procedure/function call
    StAlloc { bytes: usize },
    /// Move the imaginary stack pointer to the left.
    ///
    /// Do this after a procedure/function call.
    StDealloc { bytes: usize },

    /// Move the cell pointer to the given cell address, relative to the current
    /// stack pointer.
    ///
    /// This translates into Brainf*ck as repeated ">" or "<" instructions.
    Goto { cell: isize },

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

/// Given a symbol table and a vector of [Instruction]s, generate the final Brainf*ck
/// code.
pub fn generate_bf(
    commands: &mut Vec<BFCommand>,
    cell_pointer: &mut isize,
    symbol_table: &SymbolTable,
    instrs: &Vec<Instruction>,
) {
    use BFCommand::*;

    for instr in instrs {
        match instr {
            Instruction::StAlloc { bytes } => {
                for _ in 0..*bytes {
                    commands.push(ShiftPointerLeft); // <
                }

                // The cell pointer is relative to the top of the stack, so when the stack grows, we need to update the current cell pointer
                *cell_pointer -= *bytes as isize;
            },
            Instruction::StDealloc { bytes } => {
                for _ in 0..*bytes {
                    commands.push(ShiftPointerRight); // <
                }

                // The cell pointer is relative to the top of the stack, so when the stack grows, we need to update the current cell pointer
                *cell_pointer -= *bytes as isize;
            },
            Instruction::Goto { cell } => {
                // Move the pointer right if it's to the left of the symbol's address.
                if *cell as isize > *cell_pointer {
                    for _ in 0..(*cell as isize - *cell_pointer) {
                        commands.push(ShiftPointerRight);
                    }
                }
                // Move the pointer left if it's to the right of the symbol's address.
                else if *cell_pointer > *cell as isize {
                    for _ in 0..(*cell_pointer - *cell as isize) {
                        commands.push(ShiftPointerLeft);
                    }
                }

                // Keep track of the cell's new location
                *cell_pointer = *cell as isize;
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
                generate_bf(
                    commands,
                    cell_pointer,
                    symbol_table,
                    instructions,
                );
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
