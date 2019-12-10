use std::iter::FromIterator;

fn main() {
    bruteforce();
}

fn bruteforce() {
    let passwords: Vec<u32> = (137683..596253)
        .filter(|c| {
            let s = format!("{}", c);
            has_same_adjacent_digits(&s) && digits_never_decrease(&s)
        })
        .collect();

    println!("Valid passwords count: {}", passwords.len());
}

fn has_same_adjacent_digits(candidate: &str) -> bool {
    let mut chars = candidate.chars();
    if let Some(mut previous) = chars.next() {
        while let Some(cur) = chars.next() {
            if previous == cur { 
                return true
            }
            previous = cur;
        }
    }

    false
}

fn digits_never_decrease(candidate: &str) -> bool {
    let origin = Vec::from_iter(candidate.chars());
    let mut ordered = origin.to_vec();
    ordered.sort();

    origin == ordered
}


#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn digits_never_decrease_test() {
        assert!(digits_never_decrease("1234567"));
        assert!(digits_never_decrease("1111111"));
        assert!(digits_never_decrease("1111112"));

        assert!(!digits_never_decrease("1234576"));
        assert!(!digits_never_decrease("9234576"));
        assert!(!digits_never_decrease("12349576"));
    }

    #[test]
    fn has_adjacent_digits_test() {
        assert!(has_same_adjacent_digits("1134567"));
        assert!(has_same_adjacent_digits("1234467"));
        assert!(has_same_adjacent_digits("12345677"));

        assert!(!has_same_adjacent_digits("1214576"));
        assert!(!has_same_adjacent_digits("9234576"));
        assert!(!has_same_adjacent_digits("12349576"));
    }
}


