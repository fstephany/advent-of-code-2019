/// Day 05 contains a better version of this computer.
///
use std::cmp::Ord;
use std::fmt;
use std::fs::File;
use std::io::{BufRead, BufReader, Read};

/// Associated value is the number of steps in that direction
#[derive(Debug, PartialEq)]
enum Instruction {
    Up(usize),
    Down(usize),
    Left(usize),
    Right(usize),
}

#[derive(Debug, Copy, Clone, PartialEq)]
enum Direction {
    Horizontal,
    Vertical,
}

#[derive(Debug, Copy, Clone, PartialEq)]
struct Point {
    x: isize,
    y: isize,
}

impl Point {
    fn manhattan_distance_from_origin(&self) -> usize {
        (self.x.abs() + self.y.abs()) as usize
    }
}

#[derive(Debug, Copy, Clone)]
struct Segment {
    from: Point,
    to: Point,
    direction: Direction,

    /// The cumulative #steps from the beginning of the path to the beginning of
    /// this segment.
    cum_steps: usize,
}

#[derive(Debug, Copy, Clone)]
struct Intersection {
    p: Point,
    steps: usize,
}

impl Segment {
    fn new(from: Point, to: Point, steps: usize) -> Self {
        let direction = if from.x == to.x {
            Direction::Vertical
        } else {
            Direction::Horizontal
        };

        Self {
            from,
            to,
            direction,
            cum_steps: steps,
        }
    }

    fn is_vertical(&self) -> bool {
        self.direction == Direction::Vertical
    }
}

#[derive(Debug, PartialEq)]
enum Error {
    IoError,
    InvalidInstruction,
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

    match closest_to_center(&intersections) {
        Some(i) => println!(
            "Closest intersection from origin: {:?}: distance: {:?}",
            i,
            i.p.manhattan_distance_from_origin()
        ),
        None => println!("Couldn't find closest intersection from center"),
    };

    match shortest_signal_delay(&intersections) {
        Some(i) => println!(
            "Closest intersection to minimize signal delay: {:?}. Delay: {}",
            i, i.steps
        ),
        None => println!("Couldn't find closest intersection with shortest signal delay"),
    }
}

fn closest_to_center(intersections: &Vec<Intersection>) -> Option<Intersection> {
    intersections
        .iter()
        .min_by_key(|i| i.p.manhattan_distance_from_origin())
        .map(|c| c.clone())
}

fn shortest_signal_delay(intersections: &Vec<Intersection>) -> Option<Intersection> {
    intersections
        .iter()
        .min_by_key(|i| i.steps)
        .map(|s| s.clone())
}

/// This can be solved more efficiently. We are using a naive approach that has
/// a O(n²) complexity. Enough for the small input we have.
/// It could be fun to play with a sweep line process.
///
/// Beware we have some limitations:
///- Do not handle zero length segment
// - Do not handle overlapping segment.
fn intersections(segments_a: &Vec<Segment>, segments_b: &Vec<Segment>) -> Vec<Intersection> {
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

fn intersects(a: &Segment, b: &Segment) -> Option<Intersection> {
    // Assume that we don't handle overlapping segment (or if the two segments
    // 'touches' each other)
    if a.is_vertical() == b.is_vertical() {
        return None;
    }

    let (v, h) = if a.is_vertical() { (a, b) } else { (b, a) };
    let top_v = v.from.y.max(v.to.y);
    let bottom_v = v.from.y.min(v.to.y);
    let left_h = h.from.x.min(h.to.x);
    let right_h = h.from.x.max(h.to.x);

    // Actual check of a crossing between a vertical and horizontal segment.
    if (bottom_v..=top_v).contains(&h.from.y) && (left_h..=right_h).contains(&v.from.x) {
        let crossing = Point {
            x: v.from.x,
            y: h.from.y,
        };

        // We don't want the origin
        if crossing.x == 0 && crossing.y == 0 {
            return None;
        }

        // add the cumulative distance.
        let v_steps = v.cum_steps + (v.from.y - crossing.y).abs() as usize;
        let h_steps = h.cum_steps + (h.from.x - crossing.x).abs() as usize;

        Some(Intersection {
            p: crossing,
            steps: v_steps + h_steps,
        })
    } else {
        None
    }
}

/// Assumes that a path starts at (0, 0).
fn path_to_segments(path: &Vec<Instruction>) -> Vec<Segment> {
    if path.is_empty() {
        return Vec::new();
    }

    let mut previous = Point { x: 0, y: 0 };
    let mut cumulative_steps = 0;
    path.iter()
        .map(|instruction| {
            let (new_point, length) = match instruction {
                Instruction::Up(s) => (
                    Point {
                        x: previous.x,
                        y: previous.y + *s as isize,
                    },
                    *s,
                ),
                Instruction::Down(s) => (
                    Point {
                        x: previous.x,
                        y: previous.y - *s as isize,
                    },
                    *s,
                ),
                Instruction::Left(s) => (
                    Point {
                        x: previous.x - *s as isize,
                        y: previous.y,
                    },
                    *s,
                ),
                Instruction::Right(s) => (
                    Point {
                        x: previous.x + *s as isize,
                        y: previous.y,
                    },
                    *s,
                ),
            };

            let segment = Segment::new(previous, new_point, cumulative_steps);

            previous = segment.to;
            cumulative_steps += length;
            segment
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
                return Err(Error::InvalidInstruction);
            }

            let steps = std::str::from_utf8(&chars[1..]).map_err(|_| Error::InvalidInstruction)?;
            let parsed_steps = steps
                .parse::<usize>()
                .map_err(|_| Error::InvalidInstruction)?;

            match chars.get(0) {
                Some(b'U') => Ok(Instruction::Up(parsed_steps)),
                Some(b'D') => Ok(Instruction::Down(parsed_steps)),
                Some(b'L') => Ok(Instruction::Left(parsed_steps)),
                Some(b'R') => Ok(Instruction::Right(parsed_steps)),
                Some(_) => Err(Error::InvalidInstruction),
                None => Err(Error::InvalidInstruction),
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

        let expected: Vec<Instruction> = vec![
            Instruction::Up(75),
            Instruction::Down(83),
            Instruction::Right(7),
            Instruction::Left(300),
        ];
        assert_eq!(read_path("U75,D83,R7,L300".as_bytes()), Ok(expected));

        // trailing comma is acceptable
        let expected: Vec<Instruction> = vec![Instruction::Up(75)];
        assert_eq!(read_path("U75,".as_bytes()), Ok(expected));

        // Invalid inputs
        assert_eq!(
            read_path("U75,D83,R7,L".as_bytes()),
            Err(Error::InvalidInstruction)
        );
        assert_eq!(
            read_path("U75,D83,R7,300".as_bytes()),
            Err(Error::InvalidInstruction)
        );
    }

    #[test]
    fn read_paths_test() {
        let input = File::open("input.txt").expect("Could not open file");
        let paths = read_paths(input).unwrap();
        assert_eq!(paths.len(), 2);
    }

    #[test]
    fn segment_creation_test() {
        let instructions = read_path("U75,D83,R7,L300".as_bytes()).unwrap();
        let segments = path_to_segments(&instructions);

        assert_eq!(segments[0].cum_steps, 0);
        assert_eq!(segments[1].cum_steps, 75);
        assert_eq!(segments[2].cum_steps, 75 + 83);
        assert_eq!(segments[3].cum_steps, 75 + 83 + 7);
    }

    #[test]
    fn intersects_test() {
        let a = Segment::new(Point { x: 0, y: 0 }, Point { x: 0, y: 10 }, 100);
        let b = Segment::new(Point { x: -10, y: 5 }, Point { x: 10, y: 5 }, 255);

        // a crosses b in (0, 5)
        // Steps A: 100 + 5
        // Steps B: 255 + 10
        // -> 105 + 265 = 370

        assert_eq!(intersects(&a, &b).unwrap().p, Point { x: 0, y: 5 });
        assert_eq!(intersects(&a, &b).unwrap().steps, 370);

        assert_eq!(intersects(&b, &a).unwrap().p, Point { x: 0, y: 5 });
        assert_eq!(intersects(&b, &a).unwrap().steps, 370);

        let a = Segment::new(Point { x: 0, y: 0 }, Point { x: 0, y: 10 }, 0);
        let b = Segment::new(Point { x: 10, y: 5 }, Point { x: -10, y: 5 }, 0);
        assert_eq!(intersects(&a, &b).unwrap().p, Point { x: 0, y: 5 });
        assert_eq!(intersects(&a, &b).unwrap().steps, 15);
    }

    #[test]
    fn min_delay_test() {
        // 610 steps
        let path_a = read_path("R75,D30,R83,U83,L12,D49,R71,U7,L72".as_bytes()).unwrap();
        let path_b = read_path("U62,R66,U55,R34,D71,R55,D58,R83".as_bytes()).unwrap();
        let segments_a = path_to_segments(&path_a);

        let segments_b = path_to_segments(&path_b);
        let crossings = intersections(&segments_a, &segments_b);

        let min_delay_crossing = shortest_signal_delay(&crossings).unwrap();
        assert_eq!(min_delay_crossing.steps, 610);

        // 410 steps
        let path_a = read_path("R98,U47,R26,D63,R33,U87,L62,D20,R33,U53,R51".as_bytes()).unwrap();
        let path_b = read_path("U98,R91,D20,R16,D67,R40,U7,R15,U6,R7".as_bytes()).unwrap();
        let segment_a = path_to_segments(&path_a);
        let segment_b = path_to_segments(&path_b);
        let crossings = intersections(&segment_a, &segment_b);

        let min_delay_crossing = shortest_signal_delay(&crossings).unwrap();
        assert_eq!(min_delay_crossing.steps, 410);
    }
}
