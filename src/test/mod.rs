#![cfg(test)]

use std::fs::{self, File};

use brain_fudge::BFInterpreter;

use crate::compile;

#[test]
fn run_test_programs() {
    let test_names = vec![
        "src/test/00_assignment",
        // "01_expressions",
        "src/test/02_print_alphabet"
    ];

    for test_name in test_names {
        // Append
        println!("Running {}", test_name);
        let input = File::open(test_name.to_owned() + ".in").unwrap();

        let lobo_code = fs::read_to_string(test_name.to_owned() + ".lobo").unwrap();
        let expected_output: Vec<u8> = fs::read_to_string(test_name.to_owned() + ".out").unwrap().bytes().collect();
        
        // Compile the lobo code
        let bf_code = compile(&lobo_code).unwrap();

        let mut output = Vec::new();
        let mut interpreter = BFInterpreter::from_rw(input, &mut output, false);
        interpreter.execute(&bf_code).unwrap();
        assert_eq!(output, expected_output);
    }
}