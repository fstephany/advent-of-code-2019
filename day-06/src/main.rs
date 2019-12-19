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

    // This is weird. I get 428 but AoC tells me it's too low. 
    // I was almost sure that it was an indexing error so I skip the "-1" 
    // when we do the distance sum. And it works (ie., 430). There's something
    // bizarre going on here.
    let santa_path = map.required_orbital_transfers("YOU", "SAN");
    println!("Orbital transfers between YOU & SAN: {}", santa_path.unwrap());
}


#[derive(Debug, PartialEq)]
pub enum Error {
    IOError,
    NoCOM,
    UnknownEntity(String),
    InvalidOrbitDescription(String),
    PathNotFound
}


impl fmt::Display for Error {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Error::IOError => write!(f, "IO Error"),
            Error::NoCOM => write!(f, "Missing Center of Mass (COM)"),
            Error::InvalidOrbitDescription(v) => write!(f, "Invalid orbit description: {})", v),
            Error::UnknownEntity(v) => write!(f, "Unknown entity of the map: {})", v),
            Error::PathNotFound => write!(f, "Could not find a path between two nodes"),
        }
    }
}

impl std::error::Error for Error {}


struct Node {
    name: String,
    parent: Option<String>,
    children: Vec<String>,
    depth: u32
}

impl Node {
    fn new(name: String, parent: Option<String>) -> Self {
        Self {
            name, 
            parent,
            children: Vec::new(),
            depth: 0
        }
    }
}

struct Map {
    /// Each node is an entry in the hashmap with the form:
    /// (key) -> (value)
    ///  NAME -> Vec<CHILD_NAME>, DEPTH_FROM_ROOT
    /// The root is the "COM" node.
    nodes: HashMap<String, Node>,
    total_orbits: u32,
}

impl Map {
    pub fn parse<R: Read>(src: R) -> Result<Self, Error> {
        let mut nodes: HashMap<String, Node> = BufReader::new(src)
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

                let child_node = acc
                    .entry(child_name.to_owned())
                    .or_insert_with(|| Node::new(child_name.to_owned(), Some(parent_name.to_owned())));
                child_node.parent = Some(parent_name.to_owned());
                

                let parent_node = acc
                    .entry(parent_name.to_owned())
                    .or_insert_with(|| Node::new(child_name.to_owned(), None));
                parent_node.children.push(child_name.to_owned());

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

            for child in &node.children {
                queue.push_back((child.clone(), level + 1));
            }

            node.depth = level;
            total_orbits += level
        }

        Ok(Self { nodes, total_orbits })
    }

    pub fn required_orbital_transfers(&self, origin: &str, dst: &str) -> Result<u32, Error> {
        // Collect all the nodes from the destiation up to the root. 
        // That will give us a 'tinted' path that we will cross-check with the 
        // path of the origin up to the root. 
        let mut dst_to_root_path = Vec::new();
        let mut current = self.get(dst)?;
        let dst_depth = current.depth;
        while let Some(parent) = &current.parent {
            current = self.get(parent)?;
            dst_to_root_path.push(current);
        }

        current = self.nodes.get(origin).unwrap(); 
        let origin_depth = current.depth;
        while let Some(parent) = &current.parent {
            let parent_node = self.get(parent)?;
            
            let crossing = dst_to_root_path
                .iter()
                .find(|n| n.name == parent_node.name);
            
            match crossing {
                Some(crossing) => {
                    let dist_dest_crossing = dst_depth - crossing.depth - 1;
                    let dist_origin_crossing = origin_depth - crossing.depth - 1;
                    return Ok(dist_dest_crossing + dist_origin_crossing)
                }
                None => current = parent_node
            }
        }

        Err(Error::PathNotFound)
    }

    fn get(&self, name: &str) -> Result<&Node, Error> {
        self.nodes.get(name).ok_or_else(||Error::UnknownEntity(name.to_owned()))
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
    static MAP_DESC: &str = "COM)B\n\
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

    static SANTA_MAP_DESC: &str = "COM)B\n\
        B)C\n\
        C)D\n\
        D)E\n\
        E)F\n\
        B)G\n\
        G)H\n\
        D)I\n\
        E)J\n\
        J)K\n\
        K)L\n\
        K)YOU\n\
        I)SAN";

    #[test]
    fn parse_map_test() {
        let map = Map::parse(MAP_DESC.as_bytes()).unwrap();
        assert_eq!(map.nodes.len(), 12);
    }

    #[test]
    fn parse_map_ordering_test() {
        let map = Map::parse(MAP_DESC.as_bytes()).unwrap();
        
        assert_eq!(map.nodes.get("COM").unwrap().depth, 0);
        assert_eq!(map.nodes.get("B").unwrap().depth, 1);
        assert_eq!(map.nodes.get("H").unwrap().depth, 3);
        assert_eq!(map.nodes.get("D").unwrap().depth, 3);
        assert_eq!(map.nodes.get("L").unwrap().depth, 7);
    }

    #[test]
    fn total_orbits_test() {
        let map = Map::parse(MAP_DESC.as_bytes()).unwrap();
        assert_eq!(map.total_orbits, 42);
    }

    #[test]
    fn required_orbital_transfers_test() {
        let map = Map::parse(MAP_DESC.as_bytes()).unwrap();

        assert_eq!(map.required_orbital_transfers("L", "H"), Ok(6));
        assert_eq!(map.required_orbital_transfers("L", "I"), Ok(3));
        assert_eq!(map.required_orbital_transfers("H", "I"), Ok(3));

        let santa_map = Map::parse(SANTA_MAP_DESC.as_bytes()).unwrap();
        assert_eq!(santa_map.required_orbital_transfers("YOU", "SAN"), Ok(4));
    }
}