
use std::collections::HashMap;
use std::env;
use std::process;
use std::fs;

#[derive(Debug, Clone)]
struct Token {
    name: String,
    lexeme: String,
}

impl Token {
    fn new(name: String, lexeme: String) -> Token {
        Token { name, lexeme }
    }
}

fn main() {
    let args: Vec<String> = env::args().collect();
    if args.len() < 2 {
        println!("usage: ./rust-lex \"<file>\"");
        process::exit(1);
    }
    let file = fs::read_to_string(&args[1]).unwrap();
    let mut dfa: HashMap<u32, HashMap<char, u32>> = HashMap::new();
    let mut accepting_states: HashMap<u32, String> = HashMap::new();
dfa.insert(3, HashMap::new());dfa.get_mut(&3).unwrap().insert('x', 4);dfa.insert(4, HashMap::new());dfa.get_mut(&4).unwrap().insert('2', 5);dfa.get_mut(&4).unwrap().insert('8', 5);dfa.get_mut(&4).unwrap().insert('1', 5);dfa.get_mut(&4).unwrap().insert('6', 5);dfa.get_mut(&4).unwrap().insert('5', 5);dfa.get_mut(&4).unwrap().insert('4', 5);dfa.get_mut(&4).unwrap().insert('3', 5);dfa.get_mut(&4).unwrap().insert('F', 5);dfa.get_mut(&4).unwrap().insert('D', 5);dfa.get_mut(&4).unwrap().insert('0', 5);dfa.get_mut(&4).unwrap().insert('A', 5);dfa.get_mut(&4).unwrap().insert('9', 5);dfa.get_mut(&4).unwrap().insert('7', 5);dfa.get_mut(&4).unwrap().insert('C', 5);dfa.get_mut(&4).unwrap().insert('E', 5);dfa.get_mut(&4).unwrap().insert('B', 5);dfa.insert(2, HashMap::new());dfa.get_mut(&2).unwrap().insert('5', 2);dfa.get_mut(&2).unwrap().insert('9', 2);dfa.get_mut(&2).unwrap().insert('6', 2);dfa.get_mut(&2).unwrap().insert('3', 2);dfa.get_mut(&2).unwrap().insert('7', 2);dfa.get_mut(&2).unwrap().insert('8', 2);dfa.get_mut(&2).unwrap().insert('2', 2);dfa.get_mut(&2).unwrap().insert('0', 2);dfa.get_mut(&2).unwrap().insert('1', 2);dfa.get_mut(&2).unwrap().insert('4', 2);dfa.insert(1, HashMap::new());dfa.get_mut(&1).unwrap().insert('R', 1);dfa.get_mut(&1).unwrap().insert('n', 1);dfa.get_mut(&1).unwrap().insert('q', 1);dfa.get_mut(&1).unwrap().insert('K', 1);dfa.get_mut(&1).unwrap().insert('o', 1);dfa.get_mut(&1).unwrap().insert('f', 1);dfa.get_mut(&1).unwrap().insert('D', 1);dfa.get_mut(&1).unwrap().insert('C', 1);dfa.get_mut(&1).unwrap().insert('1', 1);dfa.get_mut(&1).unwrap().insert('c', 1);dfa.get_mut(&1).unwrap().insert('X', 1);dfa.get_mut(&1).unwrap().insert('i', 1);dfa.get_mut(&1).unwrap().insert('s', 1);dfa.get_mut(&1).unwrap().insert('O', 1);dfa.get_mut(&1).unwrap().insert('5', 1);dfa.get_mut(&1).unwrap().insert('z', 1);dfa.get_mut(&1).unwrap().insert('u', 1);dfa.get_mut(&1).unwrap().insert('6', 1);dfa.get_mut(&1).unwrap().insert('E', 1);dfa.get_mut(&1).unwrap().insert('0', 1);dfa.get_mut(&1).unwrap().insert('v', 1);dfa.get_mut(&1).unwrap().insert('S', 1);dfa.get_mut(&1).unwrap().insert('P', 1);dfa.get_mut(&1).unwrap().insert('p', 1);dfa.get_mut(&1).unwrap().insert('7', 1);dfa.get_mut(&1).unwrap().insert('3', 1);dfa.get_mut(&1).unwrap().insert('k', 1);dfa.get_mut(&1).unwrap().insert('L', 1);dfa.get_mut(&1).unwrap().insert('M', 1);dfa.get_mut(&1).unwrap().insert('G', 1);dfa.get_mut(&1).unwrap().insert('y', 1);dfa.get_mut(&1).unwrap().insert('T', 1);dfa.get_mut(&1).unwrap().insert('l', 1);dfa.get_mut(&1).unwrap().insert('x', 1);dfa.get_mut(&1).unwrap().insert('J', 1);dfa.get_mut(&1).unwrap().insert('F', 1);dfa.get_mut(&1).unwrap().insert('r', 1);dfa.get_mut(&1).unwrap().insert('g', 1);dfa.get_mut(&1).unwrap().insert('9', 1);dfa.get_mut(&1).unwrap().insert('N', 1);dfa.get_mut(&1).unwrap().insert('8', 1);dfa.get_mut(&1).unwrap().insert('2', 1);dfa.get_mut(&1).unwrap().insert('V', 1);dfa.get_mut(&1).unwrap().insert('Z', 1);dfa.get_mut(&1).unwrap().insert('b', 1);dfa.get_mut(&1).unwrap().insert('Y', 1);dfa.get_mut(&1).unwrap().insert('A', 1);dfa.get_mut(&1).unwrap().insert('Q', 1);dfa.get_mut(&1).unwrap().insert('I', 1);dfa.get_mut(&1).unwrap().insert('t', 1);dfa.get_mut(&1).unwrap().insert('w', 1);dfa.get_mut(&1).unwrap().insert('m', 1);dfa.get_mut(&1).unwrap().insert('W', 1);dfa.get_mut(&1).unwrap().insert('a', 1);dfa.get_mut(&1).unwrap().insert('e', 1);dfa.get_mut(&1).unwrap().insert('h', 1);dfa.get_mut(&1).unwrap().insert('B', 1);dfa.get_mut(&1).unwrap().insert('j', 1);dfa.get_mut(&1).unwrap().insert('U', 1);dfa.get_mut(&1).unwrap().insert('H', 1);dfa.get_mut(&1).unwrap().insert('4', 1);dfa.get_mut(&1).unwrap().insert('d', 1);dfa.insert(0, HashMap::new());dfa.get_mut(&0).unwrap().insert('c', 1);dfa.get_mut(&0).unwrap().insert('U', 1);dfa.get_mut(&0).unwrap().insert('g', 1);dfa.get_mut(&0).unwrap().insert('2', 2);dfa.get_mut(&0).unwrap().insert('t', 1);dfa.get_mut(&0).unwrap().insert('7', 2);dfa.get_mut(&0).unwrap().insert('u', 1);dfa.get_mut(&0).unwrap().insert('1', 2);dfa.get_mut(&0).unwrap().insert('9', 2);dfa.get_mut(&0).unwrap().insert('H', 1);dfa.get_mut(&0).unwrap().insert('8', 2);dfa.get_mut(&0).unwrap().insert('e', 1);dfa.get_mut(&0).unwrap().insert('Y', 1);dfa.get_mut(&0).unwrap().insert('k', 1);dfa.get_mut(&0).unwrap().insert('A', 1);dfa.get_mut(&0).unwrap().insert('6', 2);dfa.get_mut(&0).unwrap().insert('w', 1);dfa.get_mut(&0).unwrap().insert('X', 1);dfa.get_mut(&0).unwrap().insert('l', 1);dfa.get_mut(&0).unwrap().insert('m', 1);dfa.get_mut(&0).unwrap().insert('i', 1);dfa.get_mut(&0).unwrap().insert('J', 1);dfa.get_mut(&0).unwrap().insert('x', 1);dfa.get_mut(&0).unwrap().insert('E', 1);dfa.get_mut(&0).unwrap().insert('T', 1);dfa.get_mut(&0).unwrap().insert('q', 1);dfa.get_mut(&0).unwrap().insert('L', 1);dfa.get_mut(&0).unwrap().insert('D', 1);dfa.get_mut(&0).unwrap().insert('Z', 1);dfa.get_mut(&0).unwrap().insert('K', 1);dfa.get_mut(&0).unwrap().insert('y', 1);dfa.get_mut(&0).unwrap().insert('h', 1);dfa.get_mut(&0).unwrap().insert('P', 1);dfa.get_mut(&0).unwrap().insert('4', 2);dfa.get_mut(&0).unwrap().insert('z', 1);dfa.get_mut(&0).unwrap().insert('N', 1);dfa.get_mut(&0).unwrap().insert('f', 1);dfa.get_mut(&0).unwrap().insert('C', 1);dfa.get_mut(&0).unwrap().insert('G', 1);dfa.get_mut(&0).unwrap().insert('n', 1);dfa.get_mut(&0).unwrap().insert('M', 1);dfa.get_mut(&0).unwrap().insert('O', 1);dfa.get_mut(&0).unwrap().insert('p', 1);dfa.get_mut(&0).unwrap().insert('s', 1);dfa.get_mut(&0).unwrap().insert('a', 1);dfa.get_mut(&0).unwrap().insert('b', 1);dfa.get_mut(&0).unwrap().insert('d', 1);dfa.get_mut(&0).unwrap().insert('5', 2);dfa.get_mut(&0).unwrap().insert('W', 1);dfa.get_mut(&0).unwrap().insert('3', 2);dfa.get_mut(&0).unwrap().insert('o', 1);dfa.get_mut(&0).unwrap().insert('0', 3);dfa.get_mut(&0).unwrap().insert('R', 1);dfa.get_mut(&0).unwrap().insert('v', 1);dfa.get_mut(&0).unwrap().insert('V', 1);dfa.get_mut(&0).unwrap().insert('F', 1);dfa.get_mut(&0).unwrap().insert('I', 1);dfa.get_mut(&0).unwrap().insert('Q', 1);dfa.get_mut(&0).unwrap().insert('B', 1);dfa.get_mut(&0).unwrap().insert('j', 1);dfa.get_mut(&0).unwrap().insert('r', 1);dfa.get_mut(&0).unwrap().insert('S', 1);dfa.insert(5, HashMap::new());dfa.get_mut(&5).unwrap().insert('7', 5);dfa.get_mut(&5).unwrap().insert('C', 5);dfa.get_mut(&5).unwrap().insert('A', 5);dfa.get_mut(&5).unwrap().insert('5', 5);dfa.get_mut(&5).unwrap().insert('6', 5);dfa.get_mut(&5).unwrap().insert('3', 5);dfa.get_mut(&5).unwrap().insert('8', 5);dfa.get_mut(&5).unwrap().insert('B', 5);dfa.get_mut(&5).unwrap().insert('2', 5);dfa.get_mut(&5).unwrap().insert('D', 5);dfa.get_mut(&5).unwrap().insert('0', 5);dfa.get_mut(&5).unwrap().insert('4', 5);dfa.get_mut(&5).unwrap().insert('F', 5);dfa.get_mut(&5).unwrap().insert('9', 5);dfa.get_mut(&5).unwrap().insert('E', 5);dfa.get_mut(&5).unwrap().insert('1', 5);accepting_states.insert(5, String::from("hexnumber "));accepting_states.insert(1, String::from("id "));accepting_states.insert(2, String::from("integer "));
    let bytes: &[u8] = file.as_bytes();
    let mut curr_idx = 0;
    let mut curr_state = 0;
    let mut states: Vec<u32> = Vec::new();
    let mut curr_lexeme = String::new();
    let mut found_tokens: Vec<Token> = Vec::new();
    while curr_idx < bytes.len() {
        let curr_char = bytes[curr_idx] as char;
        if dfa[&curr_state].contains_key(&curr_char) {
            let next_state = dfa[&curr_state][&curr_char];
            curr_state = next_state;
            states.push(curr_state);
            curr_lexeme.push(curr_char);
            curr_idx += 1;
        }
        else if !states.is_empty() {
            while !states.is_empty() {
                let top = states.pop().unwrap();
                if accepting_states.contains_key(&top) {
                    found_tokens.push(Token::new(
                        accepting_states[&top].clone(),
                        curr_lexeme.clone(),
                    ));
                    curr_state = 0;
                    states.clear();
                    curr_lexeme.clear();
                }
            }
        } else {
            curr_idx += 1;
        }
    }
    for token in found_tokens {
        println!("Token {:?}", token);
    }
    }