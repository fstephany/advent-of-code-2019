use std::fs::File;
use std::io::{Read, BufReader, BufRead};
use std::fmt;

#[derive(Debug)]
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
    let mut src = read_program(input);

    // Once you have a working computer, the first step is to restore the 
    // gravity assist program (your puzzle input) to the "1202 program alarm" 
    // state it had just before the last computer caught fire. To do this, 
    // before running the program, replace position 1 with the value 12 and 
    // replace position 2 with the value 2. What value is left at position 0 
    // after the program halts?

    src[1] = 12;
    src[2] = 2;

    match execute(&src) {
        Ok(output) => {
            println!("Output: {:?}", output);
            println!("Position 0: {}", output[0]);
        }
        Err(e) => println!("An error occured: {}", e)
    }
}

fn read_program<R: Read>(to_read: R) -> Vec<usize> {
    BufReader::new(to_read)
        .split(b',')
        .map(|chars| {
            let chars: Vec<u8> = chars.unwrap();
            let token = std::str::from_utf8(&chars).expect("Invalid file content");
            dbg!(token);
            token.parse::<usize>().expect("Token is not a number")
        })
        .collect()
}

/// We don't modify the input in place but returns a new copy. Not the most
/// efficient but simple enough.
fn execute(input: &Vec<usize>) -> Result<Vec<usize>, Error> {
    let mut data = input.clone();

    // Command has the following schema:
    // OPCODE A_POS B_POS RESULT_POS
    // - Opcode 1: a + b 
    // - Opcode 2: a * b 
    for current in (0..data.len()).step_by(4) {
        let opcode = *data.get(current).ok_or_else(|| Error::IncompleteCommand)?;

        if opcode == 99 {
            // returns immediately, there is no need to go any further.
            return Ok(data);
        }

        let a_pos = *data.get(current + 1).ok_or_else(|| Error::IncompleteCommand)?;
        let b_pos = *data.get(current + 2).ok_or_else(|| Error::IncompleteCommand)?;
        let res_pos = *data.get(current + 3).ok_or_else(|| Error::IncompleteCommand)?;

        // Fetch the data themselves
        let a = *data.get(a_pos).ok_or_else(|| Error::PointerAccessError)?;
        let b = *data.get(b_pos).ok_or_else(|| Error::PointerAccessError)?;

        let result = match opcode {
            1 => a + b,
            2 => a * b,
            _ => return Err(Error::InvalidOpcode(opcode, current))
        };

        data[res_pos] = result;
    }

    Ok(data)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn output_test() {    
        assert_eq!(execute(&vec![1,0,0,0,99]).unwrap(), vec![2,0,0,0,99]);
        assert_eq!(execute(&vec![2,3,0,3,99]).unwrap(), vec![2,3,0,6,99]);
        assert_eq!(execute(&vec![2,4,4,5,99,0]).unwrap(), vec![2,4,4,5,99,9801]);
        assert_eq!(execute(&vec![1,1,1,4,99,5,6,0,99]).unwrap(), vec![30,1,1,4,2,5,6,0,99]);
    }

    #[test]
    fn read_program_test() {    
        assert_eq!(read_program("".as_bytes()), vec![]);
        assert_eq!(read_program("42".as_bytes()), vec![42]);
        assert_eq!(read_program("1,0,42".as_bytes()), vec![1, 0, 42]);
        // Add test with invalid input
    }
}