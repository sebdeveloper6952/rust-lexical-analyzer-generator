use serde::{Deserialize, Serialize};
use std::collections::{HashMap, HashSet};
use std::env;
use std::fmt;
use std::fs;
use std::process;
use std::str::FromStr;

/// Global variables
/// the representation of the Epsilon character
const EPSILON: char = '@';
const CONCAT_CHAR: char = 31 as char;

/// AST node representation
#[derive(Debug, Clone)]
struct CocolToken {
    name: String,
    regex: String,
}

impl CocolToken {
    fn new(name: String, regex: String) -> CocolToken {
        CocolToken { name, regex }
    }
}

/// TODO document handler operators
fn handle_operators(next_op: char, final_set: &mut Vec<char>, curr_set: &mut Vec<char>) -> bool {
    // handle operator
    let mut ret_val = true;
    if next_op == '+' {
        final_set.extend(&*curr_set);
    } else if next_op == '-' {
        let s_0: HashSet<char> = final_set.clone().into_iter().collect();
        let s_1: HashSet<char> = curr_set.clone().into_iter().collect();
        let v: Vec<char> = s_0.difference(&s_1).map(|c| *c).collect();
        final_set.clear();
        final_set.extend(&v);
    } else {
        final_set.extend(&*curr_set);
        ret_val = false;
    }

    curr_set.clear();
    return ret_val;
}

/// TODO document parse_cocol_file
fn parse_cocol_file(
    path: &str,
    cat_table: &mut HashMap<String, Vec<char>>,
    keywords: &mut HashMap<String, String>,
    tok_table: &mut HashMap<String, String>,
    tokens_vec: &mut Vec<CocolToken>,
    except_table: &mut HashMap<String, bool>,
    whitespace: &mut HashSet<char>,
) {
    let file = fs::read_to_string(path).unwrap();
    let mut lines: Vec<&str> = file.split('\n').rev().collect();
    let mut grammar_name = String::new();
    // first token must be COMPILER
    match lines.pop() {
        Some(line) => {
            let tokens: Vec<&str> = line.split(' ').collect();
            if tokens.len() == 2 && tokens[0] == "COMPILER" {
                grammar_name.push_str(tokens[1]);
            }
        }
        None => panic!("Invalid Cocol/R format."),
    };

    /* current section of file being processed
        0 = COMPILER
        1 = CHARACTERS
        2 = KEYWORDS
        3 = TOKENS
        4 = PRODUCTIONS
        5 = END
    */
    let sections = vec![
        "COMPILER",
        "CHARACTERS",
        "KEYWORDS",
        "TOKENS",
        "PRODUCTIONS",
        "END",
    ];
    let mut section = 0;

    while !lines.is_empty() {
        let line = lines.pop().unwrap();
        let tokens: Vec<&str> = line.splitn(2, ' ').collect();
        // parse WhiteSpaceDecl
        if tokens.first().unwrap() == &"IGNORE" {
            println!("WhiteSpaceDecl");
            let mut ident_vec = String::new();
            let mut final_set: Vec<char> = Vec::new();
            let mut curr_set: Vec<char> = Vec::new();
            let mut next_op: char = 0 as char;
            let mut char_index = 0;
            while char_index < tokens[1].chars().count() {
                let c: char = tokens[1].chars().nth(char_index).unwrap();

                if c == '+' || c == '-' {
                    next_op = c;
                    char_index += 1;
                    continue;
                }

                // basic set
                if c == '\"' {
                    char_index += 1;
                    while tokens[1].chars().nth(char_index).unwrap() != '\"' {
                        curr_set.push(tokens[1].chars().nth(char_index).unwrap());
                        char_index += 1;
                    }
                    // handle operators (+|-)
                    handle_operators(next_op, &mut final_set, &mut curr_set);
                    next_op = 0 as char;
                }
                // letter{leter|digit} | CHR() | CHR()..CHR()
                else if c.is_alphabetic() {
                    let mut cc = tokens[1].chars().nth(char_index).unwrap();
                    while cc.is_ascii_alphanumeric() {
                        ident_vec.push(cc);
                        char_index += 1;
                        cc = tokens[1].chars().nth(char_index).unwrap();
                    }
                    // ident is CHR
                    if ident_vec == "CHR" {
                        ident_vec.clear();
                        if tokens[1].chars().nth(char_index).unwrap() == '(' {
                            let mut int_stack = String::new();
                            char_index += 1;
                            while tokens[1].chars().nth(char_index).unwrap().is_numeric() {
                                int_stack.push(tokens[1].chars().nth(char_index).unwrap());
                                char_index += 1;
                            }
                            let range_start = int_stack.parse::<u8>().unwrap();
                            if (tokens[1].chars().count() - char_index > 6)
                                && tokens[1].chars().nth(char_index + 1).unwrap() == '.'
                                && tokens[1].chars().nth(char_index + 2).unwrap() == '.'
                                && tokens[1].chars().nth(char_index + 3).unwrap() == 'C'
                                && tokens[1].chars().nth(char_index + 4).unwrap() == 'H'
                                && tokens[1].chars().nth(char_index + 5).unwrap() == 'R'
                                && tokens[1].chars().nth(char_index + 6).unwrap() == '('
                            {
                                char_index += 7;
                                int_stack.clear();
                                while tokens[1].chars().nth(char_index).unwrap().is_numeric() {
                                    int_stack.push(tokens[1].chars().nth(char_index).unwrap());
                                    char_index += 1;
                                }
                                let range_end = int_stack.parse::<u8>().unwrap();
                                // push range
                                for i in range_start..range_end {
                                    curr_set.push(i as char);
                                }
                            } else {
                                curr_set.push(range_start as char);
                            }
                            // handle operator
                            handle_operators(next_op, &mut final_set, &mut curr_set);
                            next_op = 0 as char;
                        }
                    } else {
                        curr_set.extend(cat_table[&ident_vec].clone());
                        // handle operators
                        handle_operators(next_op, &mut final_set, &mut curr_set);
                        next_op = 0 as char;

                        // clear data
                        ident_vec.clear();
                        continue;
                    }
                }
                // char literal
                else if c == '\'' {
                    if tokens[1].chars().nth(char_index + 1).unwrap() == '\''
                        && tokens[1].chars().nth(char_index + 2).unwrap() != '\''
                    {
                        panic!("Error while parsing char literal.");
                    }
                    char_index += 1;
                    curr_set.push(tokens[1].chars().nth(char_index).unwrap());
                    // handle operators
                    handle_operators(next_op, &mut final_set, &mut curr_set);
                    next_op = 0 as char;

                    // closing \'
                    char_index += 1;
                }
                char_index += 1;
            }
            for i in final_set {
                whitespace.insert(i);
            }
        }

        let tokens: Vec<&str> = line.splitn(2, '=').collect();
        // update file section
        match sections.iter().position(|&s| s == tokens[0]) {
            Some(pos) => {
                section = pos;
                continue;
            }
            None => (),
        };
        // process each section
        if section == 1 {
            // CHARACTERS
            if tokens.len() > 1 {
                if tokens[0].len() > 0 {
                    let key = String::from_str(tokens[0].trim_end()).unwrap();
                    let mut ident_vec = String::new();
                    let mut final_set: Vec<char> = Vec::new();
                    let mut curr_set: Vec<char> = Vec::new();
                    let mut next_op: char = 0 as char;

                    // loop through each char
                    let mut char_index = 0;
                    while char_index < tokens[1].chars().count() {
                        let c: char = tokens[1].chars().nth(char_index).unwrap();

                        if c == '+' || c == '-' {
                            next_op = c;
                            char_index += 1;
                            continue;
                        }

                        // basic set
                        if c == '\"' {
                            char_index += 1;
                            while tokens[1].chars().nth(char_index).unwrap() != '\"' {
                                curr_set.push(tokens[1].chars().nth(char_index).unwrap());
                                char_index += 1;
                            }
                            // handle operators (+|-)
                            handle_operators(next_op, &mut final_set, &mut curr_set);
                            next_op = 0 as char;
                        }
                        // letter{leter|digit} | CHR() | CHR()..CHR()
                        else if c.is_alphabetic() {
                            let mut cc = tokens[1].chars().nth(char_index).unwrap();
                            while cc.is_ascii_alphanumeric() {
                                ident_vec.push(cc);
                                char_index += 1;
                                cc = tokens[1].chars().nth(char_index).unwrap();
                            }
                            // ident is CHR
                            if ident_vec == "CHR" {
                                ident_vec.clear();
                                if tokens[1].chars().nth(char_index).unwrap() == '(' {
                                    let mut int_stack = String::new();
                                    char_index += 1;
                                    while tokens[1].chars().nth(char_index).unwrap().is_numeric() {
                                        int_stack.push(tokens[1].chars().nth(char_index).unwrap());
                                        char_index += 1;
                                    }
                                    let range_start = int_stack.parse::<u8>().unwrap();
                                    if (tokens[1].chars().count() - char_index > 6)
                                        && tokens[1].chars().nth(char_index + 1).unwrap() == '.'
                                        && tokens[1].chars().nth(char_index + 2).unwrap() == '.'
                                        && tokens[1].chars().nth(char_index + 3).unwrap() == 'C'
                                        && tokens[1].chars().nth(char_index + 4).unwrap() == 'H'
                                        && tokens[1].chars().nth(char_index + 5).unwrap() == 'R'
                                        && tokens[1].chars().nth(char_index + 6).unwrap() == '('
                                    {
                                        char_index += 7;
                                        int_stack.clear();
                                        while tokens[1]
                                            .chars()
                                            .nth(char_index)
                                            .unwrap()
                                            .is_numeric()
                                        {
                                            int_stack
                                                .push(tokens[1].chars().nth(char_index).unwrap());
                                            char_index += 1;
                                        }
                                        let range_end = int_stack.parse::<u8>().unwrap();
                                        // push range
                                        for i in range_start..range_end {
                                            curr_set.push(i as char);
                                        }
                                    } else {
                                        curr_set.push(range_start as char);
                                    }
                                    // handle operator
                                    handle_operators(next_op, &mut final_set, &mut curr_set);
                                    next_op = 0 as char;
                                }
                            } else {
                                curr_set.extend(cat_table[&ident_vec].clone());
                                // handle operators
                                handle_operators(next_op, &mut final_set, &mut curr_set);
                                next_op = 0 as char;

                                // clear data
                                ident_vec.clear();
                                continue;
                            }
                        }
                        // char literal
                        else if c == '\'' {
                            if tokens[1].chars().nth(char_index + 1).unwrap() == '\''
                                && tokens[1].chars().nth(char_index + 2).unwrap() != '\''
                            {
                                panic!("Error while parsing char literal.");
                            }
                            char_index += 1;
                            if tokens[1].chars().nth(char_index).unwrap() == '\\' {
                                char_index += 1;
                            }
                            curr_set.push(tokens[1].chars().nth(char_index).unwrap());
                            // handle operators
                            handle_operators(next_op, &mut final_set, &mut curr_set);
                            next_op = 0 as char;

                            // closing \'
                            char_index += 1;
                        }

                        if char_index == tokens[1].chars().count() - 1 {
                            cat_table.insert(key.clone(), final_set.clone());
                        }
                        char_index += 1;
                    }
                }
            }
        } else if section == 2 {
            // KEYWORDS
            if tokens.len() == 2 {
                let mut keyword = String::from_str(tokens[1]).unwrap();
                keyword.retain(|a| a != '.');
                keywords.insert(keyword, String::from_str(tokens[0]).unwrap());
            }
        } else if section == 3 {
            // TOKENS
            if tokens.len() > 1 {
                let mut regex = String::from('(');
                let mut char_index = 0;
                let sentence = tokens[1].trim();
                while char_index < sentence.chars().count() {
                    let mut c = sentence.chars().nth(char_index).unwrap();
                    if c == '\"' {
                        char_index += 1;
                        regex.push('(');
                        while sentence.chars().nth(char_index).unwrap() != '\"' {
                            regex.push_str(&format!(
                                "{}{}",
                                sentence.chars().nth(char_index).unwrap(),
                                CONCAT_CHAR
                            ));
                            char_index += 1;
                        }
                        regex.pop();
                        regex.push(')');
                    } else if c == '\'' {
                        char_index += 1;
                        regex.push('(');
                        regex.push(sentence.chars().nth(char_index).unwrap());
                        char_index += 1;
                        regex.push(')');
                    } else if c.is_ascii_alphabetic() {
                        let mut char_stack = String::new();
                        let mut cc = sentence.chars().nth(char_index).unwrap();
                        while cc.is_ascii_alphabetic() || cc.is_ascii_digit() {
                            char_stack.push(sentence.chars().nth(char_index).unwrap());
                            char_index += 1;
                            cc = sentence.chars().nth(char_index).unwrap();
                        }
                        if cat_table.contains_key(&char_stack) {
                            regex.push('(');
                            for cc in &cat_table[&char_stack] {
                                regex.push_str(&format!("{}|", cc));
                            }
                            regex.pop();
                            regex.push(')');
                        } else {
                            println!("Error found while parsing TOKENS sections: token \"{}\" does not exist", char_stack);
                            process::exit(-1);
                        }
                        char_index -= 1;
                        println!("regex: {}", regex);
                    }

                    c = sentence.chars().nth(char_index).unwrap();
                    if c == ' ' || c == '{' || c == '[' || c == '(' {
                        regex.push_str(&format!("{}(", CONCAT_CHAR));
                    } else if c == '\'' || c == '\"' {
                        regex.push(CONCAT_CHAR);
                    } else if c == '}' {
                        regex.push_str(&format!(")*{}", CONCAT_CHAR));
                    } else if c == ']' {
                        regex.push_str(&format!(")?{}", CONCAT_CHAR));
                    } else if c == ')' {
                        regex.push_str(&format!("){}", CONCAT_CHAR));
                    } else if c == '|' {
                        regex.push('|');
                    }
                    char_index += 1;

                    // TODO process the last '.' of each token declaration
                }
                let last = regex.pop().unwrap();
                if last == CONCAT_CHAR {
                    regex.push_str(&format!("{}#", CONCAT_CHAR));
                } else {
                    regex.push_str(&format!("{}{}#", last, CONCAT_CHAR));
                }
                // regex.push_str("#");
                regex.push(')');
                tok_table.insert(String::from_str(tokens[0]).unwrap(), regex.clone());
                tokens_vec.push(CocolToken::new(
                    String::from_str(tokens[0].trim()).unwrap(),
                    regex,
                ));
                if tokens[1].contains("EXCEPT KEYWORDS") {
                    except_table.insert(String::from(tokens[0].trim()), true);
                }
            }
        } else if section == 4 {
            // PRODUCTIONS
        } else if section == 5 {
            if tokens[1] == grammar_name {
                // println!("Cocol/R file parsed successfully.");
            }
        }
    }
}

/// Is the char an operator?
fn is_op(c: char) -> bool {
    match c {
        '*' => true,
        CONCAT_CHAR => true,
        '|' => true,
        _ => false,
    }
}

/// Is the char valid in our regular expressions?
fn is_valid_regex_symbol(c: &char) -> bool {
    c.is_ascii_alphanumeric() || *c == '#' || *c == EPSILON || *c == '\'' || *c == '\"' || *c == '.'
}

/// Process the extension operators of regexes:
///  - '+'
/// - '?'
///
/// The instances of the above operators are replaced with the
/// equivalent expressions, using only the basic operators.
///
/// For example:
/// - `a+` is replaced as `a.a*`
/// - `a?` is replaced as `(a|@)`
///
/// `@` is used to represent `EPSILON`.
fn preprocess_regex(regex: &String) -> String {
    let mut new_regex = String::new();
    let mut stack = Vec::new();
    let bytes = regex.as_bytes();
    for i in 0..bytes.len() {
        let curr = bytes[i] as char;
        if curr == '(' {
            let next = bytes[i + 1] as char;
            if next != '+' || next != '?' {
                stack.clear()
            }
        }
        if curr == '+' {
            let top = stack.pop().unwrap();
            if top == ')' {
                let mut temp = String::new();
                while !stack.is_empty() {
                    temp.insert(0, stack.pop().unwrap());
                }
                for c in temp.chars() {
                    new_regex.push(c);
                }
                new_regex.push_str(&format!(")*"));
                continue;
            } else {
                new_regex.push_str(&format!("{}*", top));
            }
        } else if curr == '?' {
            let top = stack.pop().unwrap();
            if top == ')' {
                let mut temp = String::new();
                while !stack.is_empty() {
                    new_regex.pop();
                    temp.insert(0, stack.pop().unwrap());
                }
                temp.push(')');
                for c in temp.chars() {
                    new_regex.push(c);
                }
                new_regex.push_str(&format!("|{})", EPSILON));
                continue;
            } else {
                new_regex.pop();
                new_regex.push_str(&format!("({}|{})", top, EPSILON));
            }
        } else {
            // push char to stack
            stack.push(curr);
            // add char to preprocessed regex
            new_regex.push(curr);
        }
    }
    new_regex
}

/// AST node representation
#[derive(Debug, Clone)]
struct Node {
    /// The symbol of the regex that this node represents.
    symbol: char,
    /// Left child.
    left: Option<Box<Node>>,
    /// Right child.
    right: Option<Box<Node>>,
    /// The position of this node in the syntax tree. This position is used
    /// in the `regex_dfa` algorithm.
    position: u32,
    /// Is this node nullable?
    nullable: bool,
    /// Set of positions that can appear as the first symbols, given the
    /// sub regular expression represented by this node.
    firstpos: HashSet<u32>,
    /// Set of positions that can appear as the last symbols, given the
    /// sub regular expression represented by this node.
    lastpos: HashSet<u32>,
}

impl Node {
    /// Creates a new node given the symbol, position, and its
    /// nullability.
    ///
    /// Left and right children can be set using `set_left_child` and
    /// `set_right_child` respectively.
    fn new(symbol: char, position: u32, nullable: bool) -> Node {
        Node {
            symbol,
            left: None,
            right: None,
            position: position,
            nullable: nullable,
            firstpos: HashSet::new(),
            lastpos: HashSet::new(),
        }
    }

    /// Create a new node to represent the UNION (OR) operator.
    ///
    /// Firstpos and lastpos are calculated based on the given
    /// children.
    fn new_union_node(left: Node, right: Node) -> Node {
        // create new node
        let mut new_node = Node::new('|', 0, false);
        // compute nullable
        let nullable = left.nullable || right.nullable;
        new_node.nullable = nullable;
        // compute firstpos
        let union: HashSet<&u32> = left.firstpos.union(&right.firstpos).collect();
        new_node.firstpos = union.iter().cloned().map(|a| *a).collect();
        let union: HashSet<&u32> = left.lastpos.union(&right.lastpos).collect();
        new_node.lastpos = union.iter().cloned().map(|a| *a).collect();
        // add children
        new_node.left = Some(Box::new(left));
        new_node.right = Some(Box::new(right));

        new_node
    }

    /// Create a new node to represent the CONCATENATION
    /// operator.
    ///
    /// Firstpos and lastpos are calculated based on the given
    /// children.
    fn new_concat_node(left: Node, right: Node) -> Node {
        // new node instance
        let mut new_node = Node::new(CONCAT_CHAR, 0, false);
        // compute and set nullable
        new_node.nullable = left.nullable && right.nullable;
        // compute firstpos
        let mut firstpos: HashSet<u32> = HashSet::new();
        if left.nullable {
            let union: HashSet<&u32> = left.firstpos.union(&right.firstpos).collect();
            for x in union {
                firstpos.insert(*x);
            }
        } else {
            for x in &left.firstpos {
                firstpos.insert(*x);
            }
        }
        new_node.firstpos = firstpos;
        // compute lastpos
        let mut lastpos: HashSet<u32> = HashSet::new();
        if right.nullable {
            let union: HashSet<&u32> = left.lastpos.union(&right.lastpos).collect();
            for x in union {
                lastpos.insert(*x);
            }
        } else {
            for x in &right.lastpos {
                lastpos.insert(*x);
            }
        }
        new_node.lastpos = lastpos;
        // add children
        new_node.left = Some(Box::new(left));
        new_node.right = Some(Box::new(right));

        new_node
    }

    /// Create a new node to represent the KLEENE CLOSURE
    /// operator.
    ///
    /// Firstpos and lastpos are calculated based on the given
    /// child.
    fn new_star_node(left: Node) -> Node {
        let mut new_node = Node::new('*', 0, true);
        // firstpos of star node is the same as firstpos of its child
        let mut firstpos: HashSet<u32> = HashSet::new();
        for x in &left.firstpos {
            firstpos.insert(*x);
        }
        new_node.firstpos = firstpos;
        // lastpos is lastpos of child
        let mut lastpos: HashSet<u32> = HashSet::new();
        for x in &left.lastpos {
            lastpos.insert(*x);
        }
        new_node.lastpos = lastpos;
        new_node.left = Some(Box::new(left));

        new_node
    }
}

/// DFA representation
#[derive(Debug, Serialize, Deserialize)]
struct Dfa {
    /// The transition table of this `Dfa`.
    dfa: HashMap<u32, HashMap<u8, u32>>,
    /// The set of accepting states of this `Dfa`.
    accepting_states: Vec<u32>,
}

impl Dfa {
    /// Create a new DFA.
    ///
    /// `dfa`: the transition table for the new DFA.
    /// `accepting_states`: a vector containing the set of accepting states of
    /// the new DFA.
    fn new(dfa: HashMap<u32, HashMap<u8, u32>>, accepting_states: Vec<u32>) -> Dfa {
        Dfa {
            dfa,
            accepting_states,
        }
    }
}

impl fmt::Display for Dfa {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        let mut states = HashSet::new();
        for (key, _) in &self.dfa {
            states.insert(key);
        }
        write!(
            f,
            "ESTADOS = {:?}\nSIMBOLOS = {:?}\nINICIO = {{0}}\nACEPTACION = {{{:?}}}\nTRANSICION = {:?}",
            states,
            vec!['a', 'b'],
            &self.accepting_states,
            &self.dfa
        )
    }
}

// ***************************************** Regex Parse and Tree *****************************************
/// loop through input regex to build the Abstract Syntax Tree for the regex.
/// the algorithm used is the one created by Edsger Dijkstra, Shunting Yard Algorithm.
/// <https://en.wikipedia.org/wiki/Shunting-yard_algorithm>
///
/// Input: a regular expression
/// Output: the node that represents the root of the tree.
///
/// The followpos table is also updated to be used later
/// in the REGEX -> DFA algorithm.
fn parse_regex(
    regex: &String,
    fp_table: &mut HashMap<u32, HashSet<u32>>,
    pos_table: &mut HashMap<char, HashSet<u32>>,
) -> Node {
    // holds nodes
    let mut tree_stack: Vec<Node> = Vec::new();
    // holds operators and parentheses
    let mut op_stack: Vec<char> = Vec::new();
    // tree node id
    let mut next_position: u32 = 1;
    // hashmap of operators and precedences
    let mut precedences = HashMap::<char, u8>::new();
    // populate precedences
    precedences.insert('(', 0);
    precedences.insert('|', 1);
    precedences.insert(CONCAT_CHAR, 2);
    precedences.insert('*', 3);

    // for each char in the regex
    for c in regex.chars() {
        if is_valid_regex_symbol(&c) {
            // (a|b)
            // build node for c and push into tree_stack
            let mut n = Node::new(c, 0, false);
            if c != EPSILON {
                n.position = next_position;
                next_position += 1;
                // firstpos of a symbol node is only its position
                let mut hs = HashSet::new();
                hs.insert(n.position);
                n.firstpos = hs.clone();
                // lastpos of a symbol node is only its position
                n.lastpos = hs;
                // update s_table to save this char position in the tree
                if !pos_table.contains_key(&c) {
                    pos_table.insert(c, HashSet::new());
                }
                pos_table.get_mut(&c).unwrap().insert(n.position);
            } else {
                n.nullable = true;
            }
            // push this node to the stack of nodes
            tree_stack.push(n);
        } else if c == '(' {
            // push into op_stack
            op_stack.push(c);
        } else if c == ')' {
            // pop from op_stack until '(' is found
            // build nodes for the operators popped from stack
            loop {
                // pop until '(' is found
                let op = match op_stack.pop() {
                    Some(op) => op,
                    None => {
                        println!("An error was found: missing opening parentheses, please check your input regular expression.");
                        process::exit(1);
                    }
                };
                if op == '(' {
                    break;
                }

                // build node for operator
                let mut n = Node::new(op, 0, false);
                if op == '|' {
                    // OR
                    let right = tree_stack.pop().unwrap();
                    let left = tree_stack.pop().unwrap();
                    n = Node::new_union_node(left, right);
                } else if op == CONCAT_CHAR {
                    let right = tree_stack.pop().unwrap();
                    let left = tree_stack.pop().unwrap();
                    // update followpos table
                    for x in &left.lastpos {
                        if !fp_table.contains_key(&x) {
                            fp_table.insert(*x, HashSet::new());
                        }
                        for y in &right.firstpos {
                            fp_table.get_mut(&x).unwrap().insert(*y);
                        }
                    }
                    n = Node::new_concat_node(left, right);
                } else if op == '*' {
                    let left = tree_stack.pop().unwrap();
                    n = Node::new_star_node(left);
                    // update followpos table
                    for x in &n.lastpos {
                        if !fp_table.contains_key(x) {
                            fp_table.insert(*x, HashSet::new());
                        }
                        for y in &n.firstpos {
                            fp_table.get_mut(x).unwrap().insert(*y);
                        }
                    }
                }

                // push new node into tree
                tree_stack.push(n);
            }
        } else if is_op(c) {
            // while top of stack has an operator with greater or equal precedence as 'c',
            // pop from stack and create nodes
            while op_stack.len() > 0 && precedences[op_stack.last().unwrap()] >= precedences[&c] {
                // pop top operator from stack
                let top_op = op_stack.pop().unwrap();
                // create new node for this operator
                let mut n = Node::new(top_op, 0, false);
                if top_op == '|' {
                    // OR
                    let right = tree_stack.pop().unwrap();
                    let left = tree_stack.pop().unwrap();
                    n = Node::new_union_node(left, right);
                } else if top_op == CONCAT_CHAR {
                    let right = tree_stack.pop().unwrap();
                    let left = tree_stack.pop().unwrap();
                    // update followpos table
                    for x in &left.lastpos {
                        if !fp_table.contains_key(&x) {
                            fp_table.insert(*x, HashSet::new());
                        }
                        for y in &right.firstpos {
                            fp_table.get_mut(&x).unwrap().insert(*y);
                        }
                    }
                    n = Node::new_concat_node(left, right);
                } else if top_op == '*' {
                    let left = tree_stack.pop().unwrap();
                    n = Node::new_star_node(left);
                    // update followpos table
                    for x in &n.lastpos {
                        if !fp_table.contains_key(x) {
                            fp_table.insert(*x, HashSet::new());
                        }
                        for y in &n.firstpos {
                            fp_table.get_mut(x).unwrap().insert(*y);
                        }
                    }
                }

                // push new node to tree_stack
                tree_stack.push(n);
            }

            // push to op_stack
            op_stack.push(c);
        } else if c == EPSILON {
            continue;
        } else {
            // expression error
            panic!("Invalid character found in expression.");
        }
    }
    // process remaining nodes in op_stack
    while !op_stack.is_empty() {
        let top_op = op_stack.pop().unwrap();
        let mut n = Node::new(top_op, 0, false);
        if top_op == '|' {
            // OR
            let right = tree_stack.pop().unwrap();
            let left = tree_stack.pop().unwrap();
            n = Node::new_union_node(left, right);
        } else if top_op == CONCAT_CHAR {
            let right = tree_stack.pop().unwrap();
            let left = tree_stack.pop().unwrap();
            // update followpos table
            for x in &left.lastpos {
                if !fp_table.contains_key(&x) {
                    fp_table.insert(*x, HashSet::new());
                }
                for y in &right.firstpos {
                    fp_table.get_mut(&x).unwrap().insert(*y);
                }
            }
            n = Node::new_concat_node(left, right);
        } else if top_op == '*' {
            let left = tree_stack.pop().unwrap();
            n = Node::new_star_node(left);
            // update followpos table
            for x in &n.lastpos {
                if !fp_table.contains_key(x) {
                    fp_table.insert(*x, HashSet::new());
                }
                for y in &n.firstpos {
                    fp_table.get_mut(x).unwrap().insert(*y);
                }
            }
        } else {
            println!("An error was found, please check your input regular expression.");
            process::exit(1);
        }
        // add node to tree stack
        tree_stack.push(n);
    }

    tree_stack.pop().unwrap()
}

// ************************************************ Regex -> DFA ************************************************
/// Constructs a DFA directly from the regular expression.
///
/// `fp_table`: the followpos table that was built while parsing the regular expression.
/// `s_table`: the symbol table that was built while parsing the regular expression.
/// `root`: the root `Node` of the parse tree for the regular expression.
/// `alphabet`: the alphabet found on the regular expression.
///
/// output: DFA.
///
/// `fp_table` and `s_table` should be built using the `parse_regex` method. `root` is also
/// obtained by calling `parse_regex`.
fn regex_dfa(
    fp_table: &HashMap<u32, HashSet<u32>>,
    s_table: &HashMap<char, HashSet<u32>>,
    tokens: &Vec<CocolToken>,
    tokens_accepting_states: &mut HashMap<u32, CocolToken>,
    root: &Node,
    alphabet: &HashSet<char>,
) -> Dfa {
    let mut dfa: HashMap<u32, HashMap<u8, u32>> = HashMap::new();
    let mut d_states: HashSet<Vec<u32>> = HashSet::new();
    let mut d_acc_states: Vec<u32> = Vec::new();
    let mut d_states_map: HashMap<Vec<u32>, u32> = HashMap::new();
    let mut unmarked: Vec<Vec<u32>> = Vec::new();
    let mut curr_state = 0;

    // TODO think of better implementation
    let mut hashtag_positions: Vec<u32> = s_table[&'#'].clone().into_iter().collect();
    hashtag_positions.sort();

    // push start state, it is firstpos of the root of the tree
    let mut start_state: Vec<u32> = root.firstpos.clone().into_iter().collect();
    start_state.sort();
    unmarked.push(start_state.clone());
    d_states.insert(start_state.clone());
    d_states_map.insert(start_state.clone(), curr_state);
    curr_state += 1;

    // check if starting state is an accepting state
    if root.firstpos.intersection(&s_table[&'#']).count() > 0 {
        d_acc_states.push(0);
    }

    // main loop
    while !unmarked.is_empty() {
        // pop and mark T
        let state_t = unmarked.pop().unwrap();
        // foreach input symbol
        for a in alphabet {
            if *a == '#' {
                continue;
            }
            // union of followpos of a
            let mut u: HashSet<u32> = HashSet::new();
            // for each position s in state_t
            for p in &state_t {
                // for each position that corresponds to char a
                if s_table[a].contains(&p) {
                    if fp_table.contains_key(&p) {
                        u.extend(&fp_table[&p]);
                    }
                }
            }
            let mut u_vec: Vec<u32> = u.clone().into_iter().collect();
            // sort vec so Hash is the same for all vectors
            // containing the same elements
            u_vec.sort();
            // if U is not in Dstates
            if u_vec.len() > 0 && !d_states.contains(&u_vec) {
                d_states.insert(u_vec.clone());
                // save state as unmarked for processing
                unmarked.push(u_vec.clone());
                // update map and current state number
                d_states_map.insert(u_vec.clone(), curr_state);
                curr_state += 1;
            }
            // Update the transition table
            if !dfa.contains_key(&d_states_map[&state_t]) {
                dfa.insert(d_states_map[&state_t], HashMap::new());
            }
            // update transition table to reflect DFA[T, a] = U
            if u_vec.len() > 0 {
                dfa.get_mut(&d_states_map[&state_t])
                    .unwrap()
                    .insert(*a as u8, d_states_map[&u_vec]);
            }
            // check if U is an accepting state
            let intersection = u.intersection(&s_table[&'#']);
            let count = intersection.clone().count();
            if count > 0 {
                if !d_acc_states.contains(&d_states_map[&u_vec]) {
                    let state_num = d_states_map[&u_vec];
                    d_acc_states.push(state_num);
                    let mut inter_vec: Vec<u32> = intersection.into_iter().map(|a| *a).collect();
                    inter_vec.sort();
                    let hash_pos = hashtag_positions
                        .iter()
                        .position(|&a| a == inter_vec[0])
                        .unwrap();
                    let token = tokens[hash_pos].clone();
                    tokens_accepting_states.insert(state_num, token);
                }
            }
        }
    }

    Dfa::new(dfa, d_acc_states)
}

fn generate_code(
    filename: &str,
    dfa: &Dfa,
    accepting_states: &HashMap<u32, CocolToken>,
    keywords: &HashMap<String, String>,
    except_table: &HashMap<String, bool>,
    whitespace: &HashSet<char>,
) {
    let mut code = String::from(
        "
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
        println!(\"usage: ./rust-lex \\\"<file>\\\"\");
        process::exit(1);
    }
    let file = fs::read_to_string(&args[1]).unwrap();
    let mut dfa:  HashMap<u32, HashMap<u8, u32>> = HashMap::new();
    let mut accepting_states: HashMap<u32, String> = HashMap::new();
",
    );

    // build dfa
    let mut first_time = true;
    for (key, value) in &dfa.dfa {
        if first_time {
            code.push_str(&format!("dfa.insert({}, HashMap::new());", key));
            first_time = false;
        }
        for (key_char, value_s) in value {
            code.push_str(&format!(
                "dfa.get_mut(&{}).unwrap().insert({}, {});",
                key, key_char, value_s
            ));
        }
        first_time = true;
    }

    // accepting states
    for (key, value) in accepting_states {
        code.push_str(&format!(
            "accepting_states.insert({}, String::from(\"{}\"));",
            key, value.name
        ));
    }

    // keywords
    if keywords.len() > 0 {
        code.push_str("let mut keywords: HashMap<String, String> = HashMap::new();");
        for (key, value) in keywords {
            code.push_str(&format!(
                "keywords.insert(String::from({}), String::from(\"{}\"));",
                key,
                value.trim()
            ));
        }
    }

    // build except table
    if except_table.len() > 0 {
        code.push_str("let mut except_table: HashMap<String, bool> = HashMap::new();");
        for (key, _) in except_table {
            code.push_str(&format!(
                "except_table.insert(String::from(\"{}\"), true);",
                key
            ));
        }
    }

    // whitespace
    if whitespace.len() > 0 {
        code.push_str(
            "use std::collections::HashSet;\nlet mut whitespace: HashSet<u8> = HashSet::new();",
        );
        for c in whitespace {
            code.push_str(&format!("whitespace.insert({});", *c as u8));
        }
    }

    // simulation code
    code.push_str(
        "
    let bytes: &[u8] = file.as_bytes();
    let mut curr_idx = 0;
    let mut curr_state = 0;
    let mut states: Vec<u32> = Vec::new();
    let mut curr_lexeme = String::new();
    let mut found_tokens: Vec<Token> = Vec::new();
    while curr_idx < bytes.len() {
        let curr_char = bytes[curr_idx];
    ",
    );

    if whitespace.len() > 0 {
        code.push_str(
            "
        if whitespace.contains(&(curr_char as u8)) {
            curr_idx += 1;
            continue;
        }
        ",
        )
    }

    code.push_str(
        "if dfa[&curr_state].contains_key(&curr_char) {
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
    ",
    );

    if except_table.len() > 0 {
        code.push_str(
            "
        if except_table.contains_key(&accepting_states[&top]) {
            if keywords.contains_key(&curr_lexeme) {
                found_tokens.push(Token::new(String::from(\"keyword\"), curr_lexeme.clone()));
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
        ",
        );
    } else {
        code.push_str(
            "
        found_tokens.push(Token::new(
            accepting_states[&top].clone(),
            curr_lexeme.clone(),
        ));
        ",
        );
    }

    code.push_str(
        "
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
        println!(\"{:?}\", token);
    }
}
    ",
    );
    fs::write(filename, code).expect(&format!("Error writing file: {}.", filename));
}

// *********************************************** Main ***********************************************
fn main() {
    // program arguments
    let args: Vec<String> = env::args().collect();

    if args.len() < 2 {
        println!("usage: ./exec \"<file>\"");
        process::exit(1);
    }

    // categories table
    let mut cat_table: HashMap<String, Vec<char>> = HashMap::new();
    let mut tok_table: HashMap<String, String> = HashMap::new();
    let mut keywords: HashMap<String, String> = HashMap::new();
    let mut tokens: Vec<CocolToken> = Vec::new();
    let mut except_table: HashMap<String, bool> = HashMap::new();
    let mut whitespace: HashSet<char> = HashSet::new();

    // fill the ANY category
    cat_table.insert(String::from("ANY"), Vec::new());
    for i in 0..255 as u8 {
        cat_table.get_mut("ANY").unwrap().push(i as char);
    }

    // parse cocol file and update data structures
    parse_cocol_file(
        &args[1],
        &mut cat_table,
        &mut keywords,
        &mut tok_table,
        &mut tokens,
        &mut except_table,
        &mut whitespace,
    );

    println!("\n******************* Scanner Info ***********************");
    println!("********************* CHARACTERS *************************");
    for (key, value) in cat_table {
        println!("{} => {:?}", key, value);
    }
    println!("********************* KEYWORDS *************************");
    for (key, value) in &keywords {
        println!("{} => {}", key, value);
    }
    println!("********************* TOKENS *************************");
    let mut regex = String::from("(");
    for token in &tokens {
        regex.push_str(&format!("{}|", token.regex));
        println!("{:?}", token);
        if except_table.contains_key(&token.name) {
            println!("\tcontains EXCEPT KEYWORDS");
        }
    }
    regex.pop();
    println!("******************* WHITESPACE ***********************");
    for c in &whitespace {
        println!("\tascii code: {}", *c as u8);
    }
    println!("****************** FINAL REGEX ***********************");
    regex.push(')');
    // replace '?' and '+' operators by the basic operators
    let proc_regex = preprocess_regex(&regex);
    println!("{}", proc_regex);
    // create the alphabet using the symbols in the regex
    let mut letters = regex.clone();
    letters.retain(|c| (is_valid_regex_symbol(&c) && c != EPSILON));
    let alphabet: HashSet<char> = letters.chars().into_iter().collect();

    // followpos table
    let mut fp_table: HashMap<u32, HashSet<u32>> = HashMap::new();
    let mut pos_table: HashMap<char, HashSet<u32>> = HashMap::new();
    let tree_root = parse_regex(&proc_regex, &mut fp_table, &mut pos_table);

    // regex -> dfa
    let mut accepting_states: HashMap<u32, CocolToken> = HashMap::new();
    let direct_dfa = regex_dfa(
        &fp_table,
        &pos_table,
        &tokens,
        &mut accepting_states,
        &tree_root,
        &alphabet,
    );

    // code generation
    generate_code(
        "rust-lex.rs",
        &direct_dfa,
        &accepting_states,
        &keywords,
        &except_table,
        &whitespace,
    );
    println!("File rust-lex.rs written correctly.");
}
