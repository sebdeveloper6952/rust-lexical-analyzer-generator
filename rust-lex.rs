
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
dfa.insert(5, HashMap::new());dfa.get_mut(&5).unwrap().insert(48, 5);dfa.get_mut(&5).unwrap().insert(52, 5);dfa.get_mut(&5).unwrap().insert(56, 5);dfa.get_mut(&5).unwrap().insert(54, 5);dfa.get_mut(&5).unwrap().insert(57, 5);dfa.get_mut(&5).unwrap().insert(55, 5);dfa.get_mut(&5).unwrap().insert(50, 5);dfa.get_mut(&5).unwrap().insert(51, 5);dfa.get_mut(&5).unwrap().insert(53, 5);dfa.get_mut(&5).unwrap().insert(49, 5);dfa.insert(4, HashMap::new());dfa.get_mut(&4).unwrap().insert(56, 5);dfa.get_mut(&4).unwrap().insert(48, 5);dfa.get_mut(&4).unwrap().insert(53, 5);dfa.get_mut(&4).unwrap().insert(54, 5);dfa.get_mut(&4).unwrap().insert(57, 5);dfa.get_mut(&4).unwrap().insert(52, 5);dfa.get_mut(&4).unwrap().insert(49, 5);dfa.get_mut(&4).unwrap().insert(120, 6);dfa.get_mut(&4).unwrap().insert(51, 5);dfa.get_mut(&4).unwrap().insert(55, 5);dfa.get_mut(&4).unwrap().insert(50, 5);dfa.insert(1, HashMap::new());dfa.get_mut(&1).unwrap().insert(9, 1);dfa.get_mut(&1).unwrap().insert(13, 1);dfa.get_mut(&1).unwrap().insert(10, 1);dfa.insert(0, HashMap::new());dfa.get_mut(&0).unwrap().insert(104, 3);dfa.get_mut(&0).unwrap().insert(48, 4);dfa.get_mut(&0).unwrap().insert(97, 3);dfa.get_mut(&0).unwrap().insert(52, 5);dfa.get_mut(&0).unwrap().insert(13, 1);dfa.get_mut(&0).unwrap().insert(49, 5);dfa.get_mut(&0).unwrap().insert(108, 3);dfa.get_mut(&0).unwrap().insert(98, 3);dfa.get_mut(&0).unwrap().insert(119, 3);dfa.get_mut(&0).unwrap().insert(112, 3);dfa.get_mut(&0).unwrap().insert(45, 2);dfa.get_mut(&0).unwrap().insert(118, 3);dfa.get_mut(&0).unwrap().insert(51, 5);dfa.get_mut(&0).unwrap().insert(111, 3);dfa.get_mut(&0).unwrap().insert(105, 3);dfa.get_mut(&0).unwrap().insert(50, 5);dfa.get_mut(&0).unwrap().insert(116, 3);dfa.get_mut(&0).unwrap().insert(90, 3);dfa.get_mut(&0).unwrap().insert(57, 5);dfa.get_mut(&0).unwrap().insert(113, 3);dfa.get_mut(&0).unwrap().insert(56, 5);dfa.get_mut(&0).unwrap().insert(115, 3);dfa.get_mut(&0).unwrap().insert(99, 3);dfa.get_mut(&0).unwrap().insert(10, 1);dfa.get_mut(&0).unwrap().insert(100, 3);dfa.get_mut(&0).unwrap().insert(55, 5);dfa.get_mut(&0).unwrap().insert(101, 3);dfa.get_mut(&0).unwrap().insert(109, 3);dfa.get_mut(&0).unwrap().insert(117, 3);dfa.get_mut(&0).unwrap().insert(122, 3);dfa.get_mut(&0).unwrap().insert(43, 2);dfa.get_mut(&0).unwrap().insert(110, 3);dfa.get_mut(&0).unwrap().insert(106, 3);dfa.get_mut(&0).unwrap().insert(107, 3);dfa.get_mut(&0).unwrap().insert(103, 3);dfa.get_mut(&0).unwrap().insert(120, 3);dfa.get_mut(&0).unwrap().insert(54, 5);dfa.get_mut(&0).unwrap().insert(102, 3);dfa.get_mut(&0).unwrap().insert(9, 1);dfa.get_mut(&0).unwrap().insert(53, 5);dfa.get_mut(&0).unwrap().insert(121, 3);dfa.get_mut(&0).unwrap().insert(65, 3);dfa.get_mut(&0).unwrap().insert(114, 3);dfa.insert(3, HashMap::new());dfa.get_mut(&3).unwrap().insert(101, 3);dfa.get_mut(&3).unwrap().insert(97, 3);dfa.get_mut(&3).unwrap().insert(49, 3);dfa.get_mut(&3).unwrap().insert(116, 3);dfa.get_mut(&3).unwrap().insert(104, 3);dfa.get_mut(&3).unwrap().insert(112, 3);dfa.get_mut(&3).unwrap().insert(121, 3);dfa.get_mut(&3).unwrap().insert(98, 3);dfa.get_mut(&3).unwrap().insert(100, 3);dfa.get_mut(&3).unwrap().insert(107, 3);dfa.get_mut(&3).unwrap().insert(52, 3);dfa.get_mut(&3).unwrap().insert(119, 3);dfa.get_mut(&3).unwrap().insert(115, 3);dfa.get_mut(&3).unwrap().insert(111, 3);dfa.get_mut(&3).unwrap().insert(50, 3);dfa.get_mut(&3).unwrap().insert(122, 3);dfa.get_mut(&3).unwrap().insert(48, 3);dfa.get_mut(&3).unwrap().insert(113, 3);dfa.get_mut(&3).unwrap().insert(105, 3);dfa.get_mut(&3).unwrap().insert(65, 3);dfa.get_mut(&3).unwrap().insert(120, 3);dfa.get_mut(&3).unwrap().insert(103, 3);dfa.get_mut(&3).unwrap().insert(51, 3);dfa.get_mut(&3).unwrap().insert(57, 3);dfa.get_mut(&3).unwrap().insert(117, 3);dfa.get_mut(&3).unwrap().insert(114, 3);dfa.get_mut(&3).unwrap().insert(56, 3);dfa.get_mut(&3).unwrap().insert(108, 3);dfa.get_mut(&3).unwrap().insert(118, 3);dfa.get_mut(&3).unwrap().insert(55, 3);dfa.get_mut(&3).unwrap().insert(90, 3);dfa.get_mut(&3).unwrap().insert(109, 3);dfa.get_mut(&3).unwrap().insert(110, 3);dfa.get_mut(&3).unwrap().insert(53, 3);dfa.get_mut(&3).unwrap().insert(54, 3);dfa.get_mut(&3).unwrap().insert(99, 3);dfa.get_mut(&3).unwrap().insert(106, 3);dfa.get_mut(&3).unwrap().insert(102, 3);dfa.insert(2, HashMap::new());dfa.get_mut(&2).unwrap().insert(57, 8);dfa.get_mut(&2).unwrap().insert(49, 8);dfa.get_mut(&2).unwrap().insert(53, 8);dfa.get_mut(&2).unwrap().insert(56, 8);dfa.get_mut(&2).unwrap().insert(55, 8);dfa.get_mut(&2).unwrap().insert(51, 8);dfa.get_mut(&2).unwrap().insert(48, 8);dfa.get_mut(&2).unwrap().insert(50, 8);dfa.get_mut(&2).unwrap().insert(54, 8);dfa.get_mut(&2).unwrap().insert(52, 8);dfa.insert(8, HashMap::new());dfa.get_mut(&8).unwrap().insert(57, 8);dfa.get_mut(&8).unwrap().insert(53, 8);dfa.get_mut(&8).unwrap().insert(55, 8);dfa.get_mut(&8).unwrap().insert(50, 8);dfa.get_mut(&8).unwrap().insert(56, 8);dfa.get_mut(&8).unwrap().insert(51, 8);dfa.get_mut(&8).unwrap().insert(49, 8);dfa.get_mut(&8).unwrap().insert(54, 8);dfa.get_mut(&8).unwrap().insert(48, 8);dfa.get_mut(&8).unwrap().insert(52, 8);dfa.insert(6, HashMap::new());dfa.get_mut(&6).unwrap().insert(97, 7);dfa.get_mut(&6).unwrap().insert(102, 7);dfa.get_mut(&6).unwrap().insert(100, 7);dfa.get_mut(&6).unwrap().insert(67, 7);dfa.get_mut(&6).unwrap().insert(49, 7);dfa.get_mut(&6).unwrap().insert(68, 7);dfa.get_mut(&6).unwrap().insert(52, 7);dfa.get_mut(&6).unwrap().insert(54, 7);dfa.get_mut(&6).unwrap().insert(57, 7);dfa.get_mut(&6).unwrap().insert(101, 7);dfa.get_mut(&6).unwrap().insert(48, 7);dfa.get_mut(&6).unwrap().insert(65, 7);dfa.get_mut(&6).unwrap().insert(51, 7);dfa.get_mut(&6).unwrap().insert(70, 7);dfa.get_mut(&6).unwrap().insert(55, 7);dfa.get_mut(&6).unwrap().insert(98, 7);dfa.get_mut(&6).unwrap().insert(50, 7);dfa.get_mut(&6).unwrap().insert(69, 7);dfa.get_mut(&6).unwrap().insert(56, 7);dfa.get_mut(&6).unwrap().insert(99, 7);dfa.get_mut(&6).unwrap().insert(66, 7);dfa.get_mut(&6).unwrap().insert(53, 7);dfa.insert(7, HashMap::new());dfa.get_mut(&7).unwrap().insert(48, 7);dfa.get_mut(&7).unwrap().insert(97, 7);dfa.get_mut(&7).unwrap().insert(98, 7);dfa.get_mut(&7).unwrap().insert(69, 7);dfa.get_mut(&7).unwrap().insert(100, 7);dfa.get_mut(&7).unwrap().insert(70, 7);dfa.get_mut(&7).unwrap().insert(57, 7);dfa.get_mut(&7).unwrap().insert(66, 7);dfa.get_mut(&7).unwrap().insert(56, 7);dfa.get_mut(&7).unwrap().insert(49, 7);dfa.get_mut(&7).unwrap().insert(52, 7);dfa.get_mut(&7).unwrap().insert(50, 7);dfa.get_mut(&7).unwrap().insert(53, 7);dfa.get_mut(&7).unwrap().insert(101, 7);dfa.get_mut(&7).unwrap().insert(102, 7);dfa.get_mut(&7).unwrap().insert(65, 7);dfa.get_mut(&7).unwrap().insert(55, 7);dfa.get_mut(&7).unwrap().insert(68, 7);dfa.get_mut(&7).unwrap().insert(67, 7);dfa.get_mut(&7).unwrap().insert(51, 7);dfa.get_mut(&7).unwrap().insert(99, 7);dfa.get_mut(&7).unwrap().insert(54, 7);accepting_states.insert(5, String::from("number"));accepting_states.insert(1, String::from("whitetoken"));accepting_states.insert(4, String::from("number"));accepting_states.insert(8, String::from("signnumber"));accepting_states.insert(3, String::from("ident"));accepting_states.insert(7, String::from("hexnumber"));let mut keywords: HashMap<String, String> = HashMap::new();keywords.insert(String::from( "do"), String::from("do"));keywords.insert(String::from( "while"), String::from("while"));let mut except_table: HashMap<String, bool> = HashMap::new();except_table.insert(String::from("ident"), true);except_table.insert(String::from("hexnumber"), true);
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
    
        if except_table.contains_key(&accepting_states[&top]) {
            if keywords.contains_key(&curr_lexeme) {
                found_tokens.push(Token::new(String::from("keyword"), curr_lexeme.clone()));
            } else {
                found_tokens.push(Token::new(
                    accepting_states[&top].clone(),
                    curr_lexeme.clone(),
                ));    
            }
        } else {
            found_tokens.push(Token::new(
                accepting_states[&top].clone(),
                curr_lexeme.clone(),
            ));
        }
        
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
    