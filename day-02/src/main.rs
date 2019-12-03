use std::fs::File;
use std::io::{Read, BufReader, BufRead};
use std::fmt;

#[derive(Debug, PartialEq)]
enum Error {
    /// Opcode is neither 1, 2 or 99. Indicate the faulty opcode position and
    /// its value.
    InvalidOpcode(usize, usize),
    /// A command is not complete. Eg., missing parameters for a given operation
    IncompleteCommand,
    /// Error while trying to access a position (e.g, index does not exist)
    PointerAccessError
}

impl fmt::Display for Error {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Error::InvalidOpcode(v, p) => write!(f, "InvalidOpcode {} at position {})", v, p),
            Error::IncompleteCommand => write!(f, "Incomplete Command"),
            Error::PointerAccessError => write!(f, "Invalid pointer address"),
        }
    }
}

fn main() {
    let input = File::open("day-02/gravity-assist-src.txt").expect("Could not open file");
    let src = read_program(input);

    // Once you have a working computer, the first step is to restore the 
    // gravity assist program (your puzzle input) to the "1202 program alarm" 
    // state it had just before the last computer caught fire. To do this, 
    // before running the program, replace position 1 with the value 12 and 
    // replace position 2 with the value 2. What value is left at position 0 
    // after the program halts?

    println!("Running the `1202 program alarm` with noun=12 and verb=2");
    match run(&src, 12, 2) {
        Ok(result) => println!("Result: {}", result),
        Err(e) => println!("Error while running: {}", e),
    }


    let target = 19690720;
    println!("Brute force to find the verb and noun that will produce: {}", target);
    
    for noun in 0..100 {
        for verb in 0..100 {
            if run(&src, noun, verb) == Ok(target) { 
                println!("--> noun={}, verb={}", noun, verb);
                break;
            }
        }
    }
}

fn read_program<R: Read>(to_read: R) -> Vec<usize> {
    BufReader::new(to_read)
        .split(b',')
        .map(|chars| {
            let chars: Vec<u8> = chars.unwrap();
            let token = std::str::from_utf8(&chars).expect("Invalid file content");
            token.parse::<usize>().expect("Token is not a number")
        })
        .collect()
}

fn run(input: &Vec<usize>, noun: usize, verb: usize) -> Result<usize, Error> {
    let mut data = input.clone();
    data[1] = noun;
    data[2] = verb;
    execute(&mut data)?;

    Ok(data[0])
}


fn execute(input: &mut Vec<usize>) -> Result<(), Error> {
    // Command has the following schema:
    // OPCODE A_POS B_POS RESULT_POS
    for current in (0..input.len()).step_by(4) {
        let opcode = *input.get(current).ok_or_else(|| Error::IncompleteCommand)?;

        if opcode == 99 {
            // returns immediately, there is no need to go any further.
            return Ok(());
        }

        let a_pos = *input.get(current + 1).ok_or_else(|| Error::IncompleteCommand)?;
        let b_pos = *input.get(current + 2).ok_or_else(|| Error::IncompleteCommand)?;
        let res_pos = *input.get(current + 3).ok_or_else(|| Error::IncompleteCommand)?;

        // Fetch the data themselves
        let a = *input.get(a_pos).ok_or_else(|| Error::PointerAccessError)?;
        let b = *input.get(b_pos).ok_or_else(|| Error::PointerAccessError)?;

        let result = match opcode {
            1 => a + b,
            2 => a * b,
            _ => return Err(Error::InvalidOpcode(opcode, current))
        };

        input[res_pos] = result;
    }

    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn output_test() {
        let mut input = vec![1,0,0,0,99];
        let _ = execute(&mut input);
        assert_eq!(input, vec![2,0,0,0,99]);
        
        let mut input = vec![2,3,0,3,99];
        let _ = execute(&mut input);
        assert_eq!(input, vec![2,3,0,6,99]);
        
        let mut input = vec![2,4,4,5,99,0];
        let _ = execute(&mut input);
        assert_eq!(input, vec![2,4,4,5,99,9801]);
        
        let mut input = vec![1,1,1,4,99,5,6,0,99];
        let _ = execute(&mut input);
        assert_eq!(input, vec![30,1,1,4,2,5,6,0,99]);
    }

    #[test]
    fn run_test() {
        let input = File::open("day-02/gravity-assist-src.txt").expect("Could not open file");
        let src = read_program(input);
        assert_eq!(run(&src, 12, 2).unwrap(), 3516593)
    }

    #[test]
    fn read_program_test() {    
        assert_eq!(read_program("".as_bytes()), vec![]);
        assert_eq!(read_program("42".as_bytes()), vec![42]);
        assert_eq!(read_program("1,0,42".as_bytes()), vec![1, 0, 42]);
        // Add test with invalid input
    }
}