use std::fmt;
use std::fs::File;
use std::io::{BufRead, BufReader, Read};

#[derive(Debug, PartialEq)]
pub enum Error {
    InvalidSourceCode,
    /// Opcode is an unknown value. 
    /// Indicate the faulty opcode value
    InvalidOpcode(isize),
    /// A ParamMode is invalid. It either a wrong value or an impossible value
    /// (e.g., Immediate mode for a write operation)
    InvalidParamMode(isize),
    /// A command is not complete. Eg., missing parameters for a given operation
    IncompleteCommand,
    /// Error while trying to access a memory address
    PointerAccessError,
}

impl fmt::Display for Error {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Error::InvalidSourceCode => write!(f, "Error while reading source code"),
            Error::InvalidOpcode(v) => write!(f, "InvalidOpcode: {})", v),
            Error::InvalidParamMode(v) => write!(f, "InvalidParamMode. Opcode decl.: {})", v),
            Error::IncompleteCommand => write!(f, "Incomplete Command"),
            Error::PointerAccessError => write!(f, "Invalid pointer address"),
        }
    }
}

#[derive(PartialEq, Debug)]
pub enum Opcode {
    Add = 1,         // OPCODE A B RESULT_POS
    Multiply = 2,    // OPCODE A B RESULT_POS
    StoreInput = 3,  // OPCODE A where A is the location where to store input 
    Output = 4,      // OPCODE A
    Exit = 99,       // OPCODE
}

impl Opcode {
    pub fn parse(value: isize) -> Result<(Opcode, Vec<ParamMode>), Error> {
        let opcode = match value % 100 {
            // we could use the [num_enum](https://crates.io/crates/num_enum) 
            // crate for this. 
            1 => Opcode::Add,
            2 => Opcode::Multiply,
            3 => Opcode::StoreInput,
            4 => Opcode::Output,
            99 => Opcode::Exit,
            _ => return Err(Error::InvalidOpcode(value))
        };

        let mut modes = vec![ParamMode::Position; opcode.size() - 1];
        
        // Get the number of digits of value
        // let digits = (value as f32).log10().floor() as isize + 1;

        for i in 0..modes.len() {
            // Get the i-th digit in the value.
            // In the case of implicit modes (i.e., the mode of some parameters
            // is not specified), we fallback to 0 which is the default mode 
            // anyway. 
            let ten = 10 as isize; 
            let digit = (value % ten.pow(i as u32 + 3)) / ten.pow(i as u32 + 2); 

            modes[i] = match digit {
                0 => ParamMode::Position,
                1 => ParamMode::Immediate,
                _ => return Err(Error::InvalidParamMode(value))
            };
        }

        Ok((opcode, modes))
    }

    /// The total size of the instruction (opcode + parameters)
    pub fn size(&self) -> usize {
        match self {
            Opcode::Add => 4,
            Opcode::Multiply => 4,
            Opcode::StoreInput => 2,
            Opcode::Output => 2,
            Opcode::Exit => 1
        }
    }
}

/// Beware that Parameters that are used to *store* a value are of course always
/// in Position mode
#[derive(PartialEq, Debug, Clone, Copy)]
pub enum ParamMode {
    Position,  // Value is stored at the given address 
    Immediate, // Value is provided by the param itself 
}

pub struct Param {
    value: isize,
    mode: ParamMode
}

pub struct Instruction {
    opcode: Opcode,
    params: Vec<Param>
}

pub struct Program {
    src: Vec<isize>,
}

impl Program {
    pub fn new<R: Read>(src: R) -> Result<Self, Error> {
        let instructions = BufReader::new(src)
            .split(b',')
            .map(|chars| -> Result<isize, Error> {
                let chars: Vec<u8> = chars.unwrap();
                let t = std::str::from_utf8(&chars).map_err(|_| Error::InvalidSourceCode)?;
                t.parse::<isize>().map_err(|_| Error::InvalidSourceCode)
            })
            .collect::<Result<Vec<isize>, _>>()?;

        Ok(Self { src: instructions })
    }

    pub fn run(&self, noun: isize, verb: isize) -> Result<isize, Error> {
        let mut data = self.src.clone();
        data[1] = noun;
        data[2] = verb;

        let mut run = Run { memory: data };
        run.start()
    }
}


/// A Run is separated from the Program because it mutates the memory while
/// runnning. It is useful to keep it separate so we can make multiple
/// independent runs.
/// Memory is a simple Vec 
pub struct Run {
    memory: Vec<isize>,
}

impl Run {
    /// Store the value stored at the given address
    pub fn set_mem(&mut self, address: usize, value: isize) -> Result<(), Error> {
        if address > self.memory.len() {
            Err(Error::PointerAccessError)
        } else  {
            self.memory[address] = value;
            Ok(())
        }
    }

    /// Return the value stored at the given address
    pub fn get_mem(&self, address: usize) -> Result<isize, Error> {
        if address > self.memory.len() {
            Err(Error::PointerAccessError)
        } else  {
            Ok(self.memory[address])
        }
    }


    pub fn start(&mut self) -> Result<isize, Error> {
        // Command has the following schema:
        // 
        for current in (0..self.memory.len()).step_by(4) {
            let opcode = *self
                .memory
                .get(current)
                .ok_or_else(|| Error::IncompleteCommand)?;

            if opcode == 99 {
                // returns immediately, there is no need to go any further.
                return Ok(self.memory[0]);
            }

            let a_pos = self.get_mem(current + 1)?;
            let b_pos = self.get_mem(current + 2)?;
            let res_pos = self.get_mem(current + 3)?;

            // Fetch the data themselves
            let a = self.get_mem(a_pos as usize)?;
            let b = self.get_mem(b_pos as usize)?;

            let result = match opcode {
                1 => a + b,
                2 => a * b,
                _ => return Err(Error::InvalidOpcode(opcode)),
            };

            self.memory[res_pos as usize] = result;
        }

        Ok(self.memory[0])
    }
}

fn main() {
    let input = File::open("day-02/gravity-assist-src.txt").expect("Could not open file");
    let program = Program::new(input).expect("Could not read program");

    println!("Running the `1202 program alarm` with noun=12 and verb=2");
    match program.run(12, 2) {
        Ok(result) => println!("Result: {}", result),
        Err(e) => println!("Error while running: {}", e),
    }

    let target = 19690720;
    println!(
        "Brute force to find the verb and noun that will produce: {}",
        target
    );

    for noun in 0..100 {
        for verb in 0..100 {
            if program.run(noun, verb) == Ok(target) {
                println!("--> noun={}, verb={}", noun, verb);
                break;
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn opcode_parse_test() {
        let (opcode, modes) = Opcode::parse(1002).unwrap();
        let expected_modes = vec![
            ParamMode::Position,   // 0
            ParamMode::Immediate,  // 1
            ParamMode::Position    // This one is implicit
        ];
        assert_eq!(opcode, Opcode::Multiply); // 02
        assert_eq!(modes, expected_modes);

        let (opcode, modes) = Opcode::parse(99).unwrap();
        let expected_modes = Vec::new();
        assert_eq!(opcode, Opcode::Exit);
        assert_eq!(modes, expected_modes);

        let (opcode, modes) = Opcode::parse(01).unwrap();
        let expected_modes = vec![
            ParamMode::Position, // Implicit
            ParamMode::Position, // Implicit
            ParamMode::Position  // Implicit
        ];
        assert_eq!(opcode, Opcode::Add);
        assert_eq!(modes, expected_modes);
    }

    #[test]
    fn output_test() {
        let mut run = Run {
            memory: vec![1, 0, 0, 0, 99],
        };
        let _ = run.start();
        assert_eq!(run.memory, vec![2, 0, 0, 0, 99]);

        let mut run = Run {
            memory: vec![2, 3, 0, 3, 99],
        };
        let _ = run.start();
        assert_eq!(run.memory, vec![2, 3, 0, 6, 99]);

        let mut run = Run {
            memory: vec![2, 4, 4, 5, 99, 0],
        };
        let _ = run.start();
        assert_eq!(run.memory, vec![2, 4, 4, 5, 99, 9801]);

        let mut run = Run {
            memory: vec![1, 1, 1, 4, 99, 5, 6, 0, 99],
        };
        let _ = run.start();
        assert_eq!(run.memory, vec![30, 1, 1, 4, 2, 5, 6, 0, 99]);
    }

    #[test]
    fn read_program_test() {
        let program = Program::new("".as_bytes()).unwrap();
        assert_eq!(program.src, vec![]);

        let program = Program::new("42".as_bytes()).unwrap();
        assert_eq!(program.src, vec![42]);

        let program = Program::new("1,0,42".as_bytes()).unwrap();
        assert_eq!(program.src, vec![1, 0, 42]);
    }
}
