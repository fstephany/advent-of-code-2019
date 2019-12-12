use std::fmt;
use std::fs::File;
use std::io::{stdin, BufRead, BufReader, Read};

// General note. We could be safer when converting integer
// help: you can convert an `isize` to `usize` and panic if the converted value wouldn't fit
//     |
// 193 |                 self.set_mem(result_position.try_into().unwrap(), a + b);
//     |                              ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

/// The TEST diagnostic program will start by requesting from the user the ID of
/// the system to test by running an input instruction - provide it 1, the ID
/// for the ship's air conditioner unit.
fn main() {
    let input = File::open("day-05/TEST-diagnostic.txt").expect("Could not open file");
    let program = Program::new(input).expect("Could not read program");

    println!("Running the diagnostic program...");
    match program.run() {
        Ok(()) => println!("Done"),
        Err(e) => println!("Error while running: {}", e),
    }
}

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
    IncompleteInstruction,
    /// Error while trying to access a memory address
    PointerAccessError,
    InvalidUserInput,
}

impl fmt::Display for Error {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Error::InvalidSourceCode => write!(f, "Error while reading source code"),
            Error::InvalidOpcode(v) => write!(f, "InvalidOpcode: {})", v),
            Error::InvalidParamMode(v) => write!(f, "InvalidParamMode. Opcode decl.: {})", v),
            Error::IncompleteInstruction => write!(f, "Incomplete Command"),
            Error::PointerAccessError => write!(f, "Invalid pointer address"),
            Error::InvalidUserInput => write!(f, "Invalid user input"),
        }
    }
}

#[derive(PartialEq, Debug, Copy, Clone)]
pub enum Opcode {
    Add = 1,        // OPCODE A B RESULT_POS
    Multiply = 2,   // OPCODE A B RESULT_POS
    StoreInput = 3, // OPCODE A where A is the location where to store input
    Output = 4,     // OPCODE A
    Exit = 99,      // OPCODE
}

impl Opcode {
    /// The total size of the instruction (opcode + parameters)
    pub fn size(&self) -> usize {
        match self {
            Opcode::Add => 4,
            Opcode::Multiply => 4,
            Opcode::StoreInput => 2,
            Opcode::Output => 2,
            Opcode::Exit => 1,
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
    content: isize,
    mode: ParamMode,
}

pub struct Instruction {
    opcode: Opcode,
    params: Vec<Param>,
}

impl Instruction {
    pub fn parse_meta_data(value: isize) -> Result<(Opcode, Vec<ParamMode>), Error> {
        let opcode = match value % 100 {
            // we could use the [num_enum](https://crates.io/crates/num_enum)
            // crate for this.
            1 => Opcode::Add,
            2 => Opcode::Multiply,
            3 => Opcode::StoreInput,
            4 => Opcode::Output,
            99 => Opcode::Exit,
            _ => return Err(Error::InvalidOpcode(value)),
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
                _ => return Err(Error::InvalidParamMode(value)),
            };
        }

        Ok((opcode, modes))
    }
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

    /// As the memory is copied for each run, they are fully independant.
    pub fn run(&self) -> Result<(), Error> {
        let data = self.src.clone();
        let mut run = Run::new(data);
        run.start()
    }
}

/// A Run is separated from the Program because it mutates the memory while
/// runnning. It is useful to keep it separate so we can make multiple
/// independent runs.
/// Memory is a simple Vec
pub struct Run {
    /// The Program Counter moves from one instruction head to another.
    /// It *never* points to the params of an instruction.
    pc: usize,
    memory: Vec<isize>,
}

impl Run {
    pub fn new(memory: Vec<isize>) -> Self {
        Self { pc: 0, memory }
    }

    pub fn ask_integer_from_user(&self) -> Result<isize, Error> {
        println!("Please enter an integer:");
        let mut input = String::new();
        stdin()
            .read_line(&mut input)
            .map_err(|_| Error::InvalidUserInput)?;
        let integer = input
            .trim()
            .parse::<isize>()
            .map_err(|_| Error::InvalidUserInput)?;

        Ok(integer)
    }

    /// Store the value stored at the given address
    fn set_mem(&mut self, address: usize, value: isize) -> Result<(), Error> {
        if address > self.memory.len() {
            Err(Error::PointerAccessError)
        } else {
            self.memory[address] = value;
            Ok(())
        }
    }

    /// Return the value stored at the given address
    fn get_mem(&self, address: usize) -> Result<isize, Error> {
        if address > self.memory.len() {
            Err(Error::PointerAccessError)
        } else {
            Ok(self.memory[address])
        }
    }

    /// Get a param value based on its mode
    fn param_value(&self, param: &Param) -> Result<isize, Error> {
        let val = if param.mode == ParamMode::Immediate {
            param.content
        } else {
            self.get_mem(param.content as usize)?
        };

        Ok(val)
    }

    /// Return false if the program should stop.
    fn execute_instruction(&mut self, instruction: &Instruction) -> Result<bool, Error> {
        match &instruction.opcode {
            Opcode::Add => {
                let a: isize = self.param_value(&instruction.params[0])?;
                let b = self.param_value(&instruction.params[1])?;
                let result_position = instruction.params[2].content;
                self.set_mem(result_position as usize, a + b)?;
            }
            Opcode::Multiply => {
                let a: isize = self.param_value(&instruction.params[0])?;
                let b = self.param_value(&instruction.params[1])?;
                let result_position = instruction.params[2].content;
                self.set_mem(result_position as usize, a * b)?;
            }
            Opcode::StoreInput => {
                let user_input = self.ask_integer_from_user()?;
                let result_position = instruction.params[0].content as usize;
                self.set_mem(result_position, user_input)?;
            }
            Opcode::Output => {
                let a = self.param_value(&instruction.params[0])?;
                println!("Output Instruction: {}", a);
            }
            Opcode::Exit => return Ok(false),
        };

        // By default we just continue execution
        Ok(true)
    }

    pub fn start(&mut self) -> Result<(), Error> {
        self.pc = 0;

        while self.pc < self.memory.len() {
            let instruction_head = self.memory[self.pc];
            let (opcode, param_modes) = Instruction::parse_meta_data(instruction_head)?;

            let params = param_modes
                .iter()
                .enumerate()
                .map(|(index, mode)| -> Result<Param, Error> {
                    Ok(Param {
                        content: self.get_mem(self.pc + index + 1)?,
                        mode: *mode,
                    })
                })
                .collect::<Result<Vec<Param>, Error>>()?;

            let instruction = Instruction { opcode, params };
            if self.execute_instruction(&instruction)? {
                self.pc += opcode.size();
            } else {
                break; // Terminate the program here.
            }
        }

        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn instruction_parse_meta_data_test() {
        let (opcode, modes) = Instruction::parse_meta_data(1002).unwrap();
        let expected_modes = vec![
            ParamMode::Position,  // 0
            ParamMode::Immediate, // 1
            ParamMode::Position,  // This one is implicit
        ];
        assert_eq!(opcode, Opcode::Multiply); // 02
        assert_eq!(modes, expected_modes);

        let (opcode, modes) = Instruction::parse_meta_data(99).unwrap();
        let expected_modes = Vec::new();
        assert_eq!(opcode, Opcode::Exit);
        assert_eq!(modes, expected_modes);

        let (opcode, modes) = Instruction::parse_meta_data(01).unwrap();
        let expected_modes = vec![
            ParamMode::Position, // Implicit
            ParamMode::Position, // Implicit
            ParamMode::Position, // Implicit
        ];
        assert_eq!(opcode, Opcode::Add);
        assert_eq!(modes, expected_modes);

        // FIXME: Add test for invalid ParamMode for a given param
        // e.g., set an Immediate mode for a write location param.
    }

    #[test]
    fn memory_after_run_test() {
        let mut run = Run::new(vec![1, 0, 0, 0, 99]);
        let _ = run.start();
        assert_eq!(run.memory, vec![2, 0, 0, 0, 99]);

        let mut run = Run::new(vec![2, 3, 0, 3, 99]);
        let _ = run.start();
        assert_eq!(run.memory, vec![2, 3, 0, 6, 99]);

        let mut run = Run::new(vec![2, 4, 4, 5, 99, 0]);
        let _ = run.start();
        assert_eq!(run.memory, vec![2, 4, 4, 5, 99, 9801]);

        let mut run = Run::new(vec![1, 1, 1, 4, 99, 5, 6, 0, 99]);
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
