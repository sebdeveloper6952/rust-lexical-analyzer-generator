
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
    let mut dfa:  HashMap<u32, HashMap<u8, u32>> = HashMap::new();
    let mut accepting_states: HashMap<u32, String> = HashMap::new();
dfa.insert(4, HashMap::new());dfa.get_mut(&4).unwrap().insert(55, 4);dfa.get_mut(&4).unwrap().insert(54, 4);dfa.get_mut(&4).unwrap().insert(52, 4);dfa.get_mut(&4).unwrap().insert(49, 4);dfa.get_mut(&4).unwrap().insert(53, 4);dfa.get_mut(&4).unwrap().insert(48, 4);dfa.get_mut(&4).unwrap().insert(50, 4);dfa.get_mut(&4).unwrap().insert(56, 4);dfa.get_mut(&4).unwrap().insert(57, 4);dfa.get_mut(&4).unwrap().insert(51, 4);dfa.insert(3, HashMap::new());dfa.get_mut(&3).unwrap().insert(54, 4);dfa.get_mut(&3).unwrap().insert(52, 4);dfa.get_mut(&3).unwrap().insert(55, 4);dfa.get_mut(&3).unwrap().insert(49, 4);dfa.get_mut(&3).unwrap().insert(56, 4);dfa.get_mut(&3).unwrap().insert(53, 4);dfa.get_mut(&3).unwrap().insert(50, 4);dfa.get_mut(&3).unwrap().insert(48, 4);dfa.get_mut(&3).unwrap().insert(57, 4);dfa.get_mut(&3).unwrap().insert(51, 4);dfa.insert(2, HashMap::new());dfa.get_mut(&2).unwrap().insert(10, 2);dfa.get_mut(&2).unwrap().insert(32, 2);dfa.get_mut(&2).unwrap().insert(13, 2);dfa.get_mut(&2).unwrap().insert(9, 2);dfa.insert(1, HashMap::new());dfa.get_mut(&1).unwrap().insert(48, 1);dfa.get_mut(&1).unwrap().insert(57, 1);dfa.get_mut(&1).unwrap().insert(52, 1);dfa.get_mut(&1).unwrap().insert(55, 1);dfa.get_mut(&1).unwrap().insert(50, 1);dfa.get_mut(&1).unwrap().insert(49, 1);dfa.get_mut(&1).unwrap().insert(46, 3);dfa.get_mut(&1).unwrap().insert(56, 1);dfa.get_mut(&1).unwrap().insert(53, 1);dfa.get_mut(&1).unwrap().insert(54, 1);dfa.get_mut(&1).unwrap().insert(51, 1);dfa.insert(0, HashMap::new());dfa.get_mut(&0).unwrap().insert(57, 1);dfa.get_mut(&0).unwrap().insert(32, 2);dfa.get_mut(&0).unwrap().insert(9, 2);dfa.get_mut(&0).unwrap().insert(49, 1);dfa.get_mut(&0).unwrap().insert(55, 1);dfa.get_mut(&0).unwrap().insert(53, 1);dfa.get_mut(&0).unwrap().insert(52, 1);dfa.get_mut(&0).unwrap().insert(54, 1);dfa.get_mut(&0).unwrap().insert(48, 1);dfa.get_mut(&0).unwrap().insert(51, 1);dfa.get_mut(&0).unwrap().insert(10, 2);dfa.get_mut(&0).unwrap().insert(56, 1);dfa.get_mut(&0).unwrap().insert(13, 2);dfa.get_mut(&0).unwrap().insert(50, 1);accepting_states.insert(4, String::from("decnumber"));accepting_states.insert(1, String::from("number"));accepting_states.insert(2, String::from("white"));let mut keywords: HashMap<String, String> = HashMap::new();keywords.insert(String::from( "while"), String::from("while"));keywords.insert(String::from( "do"), String::from("do"));
    let bytes: &[u8] = file.as_bytes();
    let mut curr_idx = 0;
    let mut curr_state = 0;
    let mut states: Vec<u32> = Vec::new();
    let mut curr_lexeme = String::new();
    let mut found_tokens: Vec<Token> = Vec::new();
    while curr_idx < bytes.len() {
        let curr_char = bytes[curr_idx];
    if dfa[&curr_state].contains_key(&curr_char) {
        let next_state = dfa[&curr_state][&curr_char];
        curr_state = next_state;
        states.push(curr_state);
        curr_lexeme.push(curr_char as char);
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
                } else {
                    curr_lexeme.pop();
                    curr_idx -= 1;
                }
            }
        } else {
            println!("Scanner: char {} is invalid.", curr_char as char);
            curr_state = 0;
            curr_idx += 1;
        }
    }
    for token in found_tokens {
        println!("{:?}", token);
    }
}
    