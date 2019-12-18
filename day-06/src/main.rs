use std::fmt;
use std::io::{Read, BufRead, BufReader};
use std::collections::{HashMap, VecDeque};
use std::fs::File;
use itertools::Itertools;

fn main() {
    let input = File::open("day-06/map.txt").expect("Could not open map file");
    let map = Map::parse(input).unwrap();

    println!("Number of entities in map: {}", map.nodes.len());
    println!("Number of directs & indirects orbits: {}", map.total_orbits);
}


#[derive(Debug, PartialEq)]
pub enum Error {
    IOError,
    NoCOM,
    UnknownEntity(String),
    InvalidOrbitDescription(String)
}


impl fmt::Display for Error {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Error::IOError => write!(f, "IO Error"),
            Error::NoCOM => write!(f, "Missing Center of Mass (COM)"),
            Error::InvalidOrbitDescription(v) => write!(f, "Invalid orbit description: {})", v),
            Error::UnknownEntity(v) => write!(f, "Unknown entity of the map: {})", v),
        }
    }
}

impl std::error::Error for Error {}

struct Map {
    /// Each node is an entry in the hashmap with the form:
    /// (key) -> (value)
    ///  NAME -> Vec<CHILD_NAME>, DEPTH_FROM_ROOT
    /// The root is the "COM" node.
    nodes: HashMap<String, (Vec<String>, u32)>,
    total_orbits: u32,
}

impl Map {
    pub fn parse<R: Read>(src: R) -> Result<Self, Error> {
        let mut nodes = BufReader::new(src)
            .lines()
            .map(|line| -> Result<(String, String), Error> {
                let orbit_desc = line.unwrap();
                let split: Vec<&str> = orbit_desc.split(')').collect();

                if split.len() != 2 {
                    Err(Error::InvalidOrbitDescription(orbit_desc))
                } else {
                    Ok((split[0].to_owned(), split[1].to_owned()))
                }
            })
            .fold_results(HashMap::new(), |mut acc, node| {
                let (parent_name, child_name) = node;

                let _child_node = acc
                    .entry(child_name.to_owned())
                    .or_insert_with(|| (Vec::new(), 0));

                let parent_node = acc
                    .entry(parent_name.to_owned())
                    .or_insert_with(|| (Vec::new(), 0));

                parent_node.0.push(child_name.to_owned());
                acc
            })?;
            
        
        let mut total_orbits = 0;

        // BF tree traversal to set the depth of each node. 
        let mut queue: VecDeque<(String, u32)> = VecDeque::new();
        queue.push_back(("COM".to_owned(), 0));

        while let Some((node_name, level)) = queue.pop_front() {
            let node = nodes
                .get_mut(&node_name)
                .ok_or_else(||Error::UnknownEntity(node_name))?;

            for child in &node.0 {
                queue.push_back((child.clone(), level + 1));
            }

            node.1 = level;
            total_orbits += level
        }


        Ok(Self { nodes, total_orbits })
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    //         G - H       J - K - L
    //        /           /
    // COM - B - C - D - E - F
    //                \
    //                 I
    static MAP_DESCRIPTION: &str = "COM)B\n\
        B)C\n\
        C)D\n\
        D)E\n\
        E)F\n\
        B)G\n\
        G)H\n\
        D)I\n\
        E)J\n\
        J)K\n\
        K)L";

    #[test]
    fn parse_map_test() {
        let map = Map::parse(MAP_DESCRIPTION.as_bytes()).unwrap();
        assert_eq!(map.nodes.len(), 12);
    }

    #[test]
    fn parse_map_ordering_test() {
        let map = Map::parse(MAP_DESCRIPTION.as_bytes()).unwrap();
        
        assert_eq!(map.nodes.get("COM").unwrap().1, 0);
        assert_eq!(map.nodes.get("B").unwrap().1, 1);
        assert_eq!(map.nodes.get("H").unwrap().1, 3);
        assert_eq!(map.nodes.get("D").unwrap().1, 3);
        assert_eq!(map.nodes.get("L").unwrap().1, 7);
    }

    #[test]
    fn total_orbits_test() {
        let map = Map::parse(MAP_DESCRIPTION.as_bytes()).unwrap();
        assert_eq!(map.total_orbits, 42);
    }
}