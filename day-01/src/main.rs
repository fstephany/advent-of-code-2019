use std::fs::File;
use std::io::{BufRead, BufReader};

/// Day 1: The Tyranny of the Rocket Equation
fn main() {
    // Part 1: Fuel just for the modules
    let module_fuel = line_reader("day-01/masses.txt")
        .iter()
        .fold(0, |sum, mass| sum + fuel_for_mass(*mass));

    println!("Total fuel for modules only: {}", module_fuel);

    // Part 2: Fuel needed for the module and the extra fuel itself.
    let total_fuel = line_reader("day-01/masses.txt")
        .iter()
        .fold(0, |sum, mass| sum + fuel_series_for_mass(*mass));

    println!("Total fuel needed: {}", total_fuel);
}

fn line_reader(path: &str) -> Vec<u32> {
    let f = File::open(path).expect("Could not open masses.txt file");
    BufReader::new(f)
        .lines()
        .map(|l| {
            let s = l.unwrap();
            s.parse::<u32>().expect("Couldn't convert line to integer")
        })
        .collect()
}

// Computes the fuel needed for a given mass and its associated fuel.
fn fuel_series_for_mass(mass: u32) -> u32 {
    let mut cur_mass = mass;
    let mut total_fuel = 0;

    while {
        cur_mass = fuel_for_mass(cur_mass);
        cur_mass > 0
    } {
        total_fuel += cur_mass;
    }

    total_fuel
}

/// To find the fuel required for a module, take its mass,
/// divide by three, round down, and subtract 2.
fn fuel_for_mass(mass: u32) -> u32 {
    let fuel = (mass as f64 / 3.0).floor() - 2.0;
    if fuel >= 0.0 {
        fuel as u32
    } else {
        0
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn fuel_for_mass_test() {
        // Tests based on given examples in Part 1
        assert_eq!(fuel_for_mass(12), 2);
        assert_eq!(fuel_for_mass(14), 2);
        assert_eq!(fuel_for_mass(1969), 654);
        assert_eq!(fuel_for_mass(100_756), 33_583);

        // Tests based on given examples in Part 2
        assert_eq!(fuel_for_mass(2), 0);
    }

    #[test]
    fn fuel_series_for_mass_test() {
        // Tests based on given examples in Part 2

        assert_eq!(fuel_series_for_mass(1969), 966);
        assert_eq!(fuel_series_for_mass(100_756), 50_346);
    }
}
