use std::fmt;
use std::io::{BufReader, BufRead, Read};
use std::fs::File;
use std::cmp::Ord;

/// Associated value is the number of steps in that direction
#[derive(Debug, PartialEq)]
enum Instruction {
    Up(usize),
    Down(usize),
    Left(usize),
    Right(usize)
}

#[derive(Debug, Copy, Clone, PartialEq)]
struct Point {
    x: isize,
    y: isize
}

#[derive(Debug, PartialEq)]
enum Error {
    IoError,
    InvalidInstruction
}

impl fmt::Display for Error {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Error::IoError => write!(f, "IO error occured"),
            Error::InvalidInstruction => write!(f, "Invalid Instruction"),
        }
    }
}


/// We could also build the path directly when iterating on the input. At the
/// moment we first build the sequence of instruction _and then_ we retraverse
/// the whole collection to build the segments.
fn main() {
    let input = File::open("day-03/input.txt").unwrap();
    let paths = read_paths(input).unwrap();
    
    let segments_a = path_to_segments(&paths[0]);
    let segments_b = path_to_segments(&paths[1]);
    let intersections = intersections(&segments_a, &segments_b);
    let closest = intersections.iter().min_by_key(|p| p.x.abs() + p.y.abs()).unwrap();
    let distance = closest.x.abs() + closest.y.abs();
    
    println!("Intersections: {:?}", intersections);
    println!("Closest intersections: {:?}: distance: {:?}", closest, distance);
}

/// This can be solved more efficiently. We are using a naive approach that has
/// a O(n²) complexity. Enough for the small input we have.
/// It could be fun to play with sweep line process. 
/// 
// - Does not handle zero length segment
// - Does not handle overlapping segment
fn intersections(segments_a: &Vec<(Point, Point)>, segments_b: &Vec<(Point, Point)>) -> Vec<Point> {
    let mut intersections = Vec::new();

    for a in segments_a {
        for b in segments_b {
            if let Some(i) = intersects(a, b) {
                intersections.push(i)
            }
        }
    }

    intersections
}

fn intersects(a: &(Point, Point), b: &(Point, Point)) -> Option<Point> {
    let is_a_vertical = a.0.x == a.1.x;
    let is_b_vertical = b.0.x == b.1.x;

    // Assume that we don't handle overlapping segment (or if the two segments
    // 'touches' each other)
    if is_a_vertical == is_b_vertical {
        return None;
    }

    let v = if is_a_vertical { a } else { b };
    let h = if is_a_vertical { b } else { a };

    let top_v = v.0.y.max(v.1.y);
    let bottom_v = v.0.y.min(v.1.y);
    let left_h = h.0.x.min(h.1.x);
    let right_h = h.0.x.max(h.1.x);

    if (bottom_v..=top_v).contains(&h.0.y) && (left_h..=right_h).contains(&v.0.x) {
        Some(Point {x: v.0.x, y: h.0.y})
    } else {
        None
    }
}

/// Assumes that a path starts at (0, 0).
fn path_to_segments(path: &Vec<Instruction>) -> Vec<(Point, Point)> {
    if path.is_empty() {
        return Vec::new()
    }

    let mut previous = Point {x: 0, y: 0};
    path.iter().map(|instruction| {
        let current = match instruction {
            Instruction::Up(s) => Point {x: previous.x, y: previous.y + *s as isize},
            Instruction::Down(s) => Point {x: previous.x, y: previous.y - *s as isize},
            Instruction::Left(s) => Point {x: previous.x - *s as isize, y: previous.y},
            Instruction::Right(s) => Point {x: previous.x + *s as isize, y: previous.y},
        };
        let to_return = (previous, current);
        previous = current;
        to_return
    })
    .collect()
}

/// Read all the paths separated by a newline 
fn read_paths<R: Read>(to_read: R) -> Result<Vec<Vec<Instruction>>, Error> {
    BufReader::new(to_read)
        .lines()
        .map(|line| -> Result<Vec<Instruction>, Error> {
            let line = line.map_err(|_| Error::IoError)?;
            read_path(line.as_bytes())
        })
        .collect()
}

/// Read a line describing a path
fn read_path<R: Read>(to_read: R) -> Result<Vec<Instruction>, Error> {
    BufReader::new(to_read)
        .split(b',')
        .map(|chars| -> Result<Instruction, Error> {
            let chars: Vec<u8> = chars.map_err(|_| Error::IoError)?;

            if chars.is_empty() {
                return Err(Error::InvalidInstruction)
            }

            let steps = std::str::from_utf8(&chars[1..])
                .map_err(|_| Error::InvalidInstruction)?;
            let parsed_steps = steps.parse::<usize>()
                .map_err(|_| Error::InvalidInstruction)?;

            match chars.get(0) {
                Some(b'U') => Ok(Instruction::Up(parsed_steps)),
                Some(b'D') => Ok(Instruction::Down(parsed_steps)),
                Some(b'L') => Ok(Instruction::Left(parsed_steps)),
                Some(b'R') => Ok(Instruction::Right(parsed_steps)),
                Some(_)    => Err(Error::InvalidInstruction),
                None => Err(Error::InvalidInstruction)
            }
        })
        .collect()
}


#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn read_path_test() {
        let expected: Vec<Instruction> = vec![]; 
        assert_eq!(read_path("".as_bytes()), Ok(expected));

        let expected: Vec<Instruction> = vec![Instruction::Up(75), 
        Instruction::Down(83), Instruction::Right(7), Instruction::Left(300)];
        assert_eq!(read_path("U75,D83,R7,L300".as_bytes()), Ok(expected));

        // trailing comma is acceptable
        let expected: Vec<Instruction> = vec![Instruction::Up(75)];
        assert_eq!(read_path("U75,".as_bytes()), Ok(expected));

        // Invalid inputs
        assert_eq!(read_path("U75,D83,R7,L".as_bytes()), Err(Error::InvalidInstruction));
        assert_eq!(read_path("U75,D83,R7,300".as_bytes()), Err(Error::InvalidInstruction));
    }

    #[test]
    fn read_paths_test() {
        let input = File::open("input.txt").expect("Could not open file");
        let paths = read_paths(input).unwrap();
        assert_eq!(paths.len(), 2);
    }


    #[test]
    fn intersects_test() {
        let a = (Point { x: 0, y: 0}, Point { x: 0, y: 10});
        let b = (Point { x: -10, y: 5}, Point { x: 10, y: 5});
        assert_eq!(intersects(&a, &b), Some(Point { x: 0, y: 5}));
        assert_eq!(intersects(&b, &a), Some(Point { x: 0, y: 5}));


        let a = (Point { x: 0, y: 0}, Point { x: 0, y: 10});
        let b = (Point { x: 10, y: 5}, Point { x: -10, y: 5});
        assert_eq!(intersects(&a, &b), Some(Point { x: 0, y: 5}));
    }
}