use std::collections::HashMap;

fn main() {
    let mut map = HashMap::new();
    map.insert('a', 0);

    println!("{}", map[&'a']);
}
    