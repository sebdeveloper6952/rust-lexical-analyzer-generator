use serde::{Deserialize, Serialize};
use std::collections::{HashMap, HashSet};
use std::env;
use std::fs;
use std::process;
use std::str::FromStr;

/// The representation of the Epsilon character
const EPSILON: char = '@';
/// Character used instead of '('
const PARENTHESES_OPEN: char = 15 as char;
/// Character used instead of ')'
const PARENTHESES_CLOSE: char = 16 as char;
/// The character used as an explicit concatenation operator
/// in the regular expressions.
// const CONCAT_CHAR: char = 17 as char;
const KLEENE_CHAR: char = 18 as char;
const POSITIVE_CHAR: char = 19 as char;
// const UNION_CHAR: char = 20 as char;
// const EXT_CHAR: char = 26 as char;
const OPTIONAL_CHAR: char = 22 as char;

// const PARENTHESES_OPEN: char = '(';
// const PARENTHESES_CLOSE: char = ')';
const CONCAT_CHAR: char = '~';
// const KLEENE_CHAR: char = '*';
// const POSITIVE_CHAR: char = '+';
const UNION_CHAR: char = '|';
const EXT_CHAR: char = '&';
// const OPTIONAL_CHAR: char = '?';

/// Cocol token representation.
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

/// Is the char an operator?
fn is_op(c: &char) -> bool {
    match *c {
        KLEENE_CHAR => true,
        CONCAT_CHAR => true,
        UNION_CHAR => true,
        POSITIVE_CHAR => true,
        OPTIONAL_CHAR => true,
        PARENTHESES_OPEN => true,
        PARENTHESES_CLOSE => true,
        _ => false,
    }
}

/// Is the char valid in our regular expressions?
fn is_valid_regex_symbol(c: &char) -> bool {
    !(is_op(c)) /* && ((*c as u8) >= 32 && (*c as u8) < 132) */
    // c.is_ascii_alphanumeric() || *c == '#' || *c == EPSILON || *c == '\'' || *c == '\"' || *c == '.'
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
        if curr == /*'('*/PARENTHESES_OPEN {
            let next = bytes[i + 1] as char;
            if next != POSITIVE_CHAR || next != OPTIONAL_CHAR {
                stack.clear()
            }
        }
        if curr == POSITIVE_CHAR {
            let top = stack.pop().unwrap();
            if top == PARENTHESES_CLOSE {
                let mut temp = String::new();
                while !stack.is_empty() {
                    temp.insert(0, stack.pop().unwrap());
                }
                for c in temp.chars() {
                    new_regex.push(c);
                }
                new_regex.push_str(&format!("{}{}", PARENTHESES_CLOSE, KLEENE_CHAR));
                continue;
            } else {
                new_regex.push_str(&format!("{}{}", top, KLEENE_CHAR));
            }
        } else if curr == OPTIONAL_CHAR {
            let top = stack.pop().unwrap();
            if top == PARENTHESES_CLOSE {
                let mut temp = String::new();
                while !stack.is_empty() {
                    new_regex.pop();
                    temp.insert(0, stack.pop().unwrap());
                }
                temp.push(PARENTHESES_CLOSE);
                for c in temp.chars() {
                    new_regex.push(c);
                }
                new_regex.push_str(&format!("{}{}{}", UNION_CHAR, EPSILON, PARENTHESES_CLOSE));
                continue;
            } else {
                new_regex.pop();
                new_regex.push_str(&format!(
                    "{}{}{}{}{}",
                    PARENTHESES_OPEN, top, UNION_CHAR, EPSILON, PARENTHESES_CLOSE
                ));
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
        let mut new_node = Node::new(UNION_CHAR, 0, false);
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
        let mut new_node = Node::new(KLEENE_CHAR, 0, true);
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
    precedences.insert(PARENTHESES_OPEN, 0);
    precedences.insert(UNION_CHAR, 1);
    precedences.insert(CONCAT_CHAR, 2);
    precedences.insert(KLEENE_CHAR, 3);

    // for each char in the regex
    for c in regex.chars() {
        if is_valid_regex_symbol(&c) {
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
        } else if c == /*'(' */ PARENTHESES_OPEN {
            // push into op_stack
            op_stack.push(c);
        } else if c == /* ')' */ PARENTHESES_CLOSE {
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
                if op == /* '(' */ PARENTHESES_OPEN {
                    break;
                }

                // build node for operator
                let mut n = Node::new(op, 0, false);
                if op == UNION_CHAR {
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
                } else if op == KLEENE_CHAR {
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
        } else if is_op(&c) {
            // while top of stack has an operator with greater or equal precedence as 'c',
            // pop from stack and create nodes
            while op_stack.len() > 0 && precedences[op_stack.last().unwrap()] >= precedences[&c] {
                // pop top operator from stack
                let top_op = op_stack.pop().unwrap();
                // create new node for this operator
                let mut n = Node::new(top_op, 0, false);
                if top_op == UNION_CHAR {
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
                } else if top_op == KLEENE_CHAR {
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
            panic!("Invalid character found in expression: {}", c as u8);
        }
    }
    // process remaining nodes in op_stack
    while !op_stack.is_empty() {
        let top_op = op_stack.pop().unwrap();
        let mut n = Node::new(top_op, 0, false);
        if top_op == UNION_CHAR {
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
        } else if top_op == KLEENE_CHAR {
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
    let mut hashtag_positions: Vec<u32> = s_table[&EXT_CHAR].clone().into_iter().collect();
    hashtag_positions.sort();

    // push start state, it is firstpos of the root of the tree
    let mut start_state: Vec<u32> = root.firstpos.clone().into_iter().collect();
    start_state.sort();
    unmarked.push(start_state.clone());
    d_states.insert(start_state.clone());
    d_states_map.insert(start_state.clone(), curr_state);
    curr_state += 1;

    // check if starting state is an accepting state
    if root.firstpos.intersection(&s_table[&EXT_CHAR]).count() > 0 {
        d_acc_states.push(0);
    }

    // main loop
    while !unmarked.is_empty() {
        // pop and mark T
        let state_t = unmarked.pop().unwrap();
        // foreach input symbol
        for a in alphabet {
            if *a == EXT_CHAR {
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
            let intersection = u.intersection(&s_table[&EXT_CHAR]);
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

/// Parses a line from the CHARACTERS section of a IGNORE line (whitespace).
///
/// Input:
///  - line:         a vector of str containing the parts of a line. V[0] is the name
///                  of the category, or "IGNORE". V[1] is the set representation.
///                  Ex.: V = [my_set, ""a" + "b" + "c"."]
/// - cat_table:     a mutable reference to the character sets table.
/// - whitespace:    a mutable reference to the whitespace characters set.
/// - is_whitespace: a boolean value indicating if the line is a whitespace.
///                  If `false`, the line is considered as a CHARACTERS set.
///
/// Output: updates the appropiate data structures passed as inputs.
fn parse_characters_line(
    line: Vec<&str>,
    cat_table: &mut HashMap<String, Vec<char>>,
    whitespace: &mut HashSet<char>,
    is_whitespace: bool,
) {
    let key = String::from_str(line[0].trim_end()).unwrap();
    let mut ident_vec = String::new();
    let mut final_set: Vec<char> = Vec::new();
    let mut curr_set: Vec<char> = Vec::new();
    let mut next_op: char = 0 as char;
    let mut char_index = 0;

    while char_index < line[1].chars().count() {
        let c: char = line[1].chars().nth(char_index).unwrap();

        if c == '+' || c == '-' {
            next_op = c;
            char_index += 1;
            continue;
        }

        // basic set
        if c == '\"' {
            char_index += 1;
            while line[1].chars().nth(char_index).unwrap() != '\"' {
                curr_set.push(line[1].chars().nth(char_index).unwrap());
                char_index += 1;
            }
            // handle operators (+|-)
            handle_operators(next_op, &mut final_set, &mut curr_set);
            next_op = 0 as char;
        }
        // letter{leter|digit} | CHR() | CHR()..CHR()
        else if c.is_alphabetic() {
            let mut cc = line[1].chars().nth(char_index).unwrap();
            while cc.is_ascii_alphanumeric() {
                ident_vec.push(cc);
                char_index += 1;
                cc = line[1].chars().nth(char_index).unwrap();
            }
            // ident is CHR
            if ident_vec == "CHR" {
                ident_vec.clear();
                if line[1].chars().nth(char_index).unwrap() == '(' {
                    let mut int_stack = String::new();
                    char_index += 1;
                    while line[1].chars().nth(char_index).unwrap().is_numeric() {
                        int_stack.push(line[1].chars().nth(char_index).unwrap());
                        char_index += 1;
                    }
                    let range_start = int_stack.parse::<u8>().unwrap();
                    if (line[1].chars().count() - char_index > 6)
                        && line[1].chars().nth(char_index + 1).unwrap() == '.'
                        && line[1].chars().nth(char_index + 2).unwrap() == '.'
                        && line[1].chars().nth(char_index + 3).unwrap() == 'C'
                        && line[1].chars().nth(char_index + 4).unwrap() == 'H'
                        && line[1].chars().nth(char_index + 5).unwrap() == 'R'
                        && line[1].chars().nth(char_index + 6).unwrap() == '('
                    {
                        char_index += 7;
                        int_stack.clear();
                        while line[1].chars().nth(char_index).unwrap().is_numeric() {
                            int_stack.push(line[1].chars().nth(char_index).unwrap());
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
                println!("ident_vec: {:?}", ident_vec);
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
            if line[1].chars().nth(char_index + 1).unwrap() == '\''
                && line[1].chars().nth(char_index + 2).unwrap() != '\''
            {
                panic!("Error while parsing char literal: quote must be escaped");
            }
            char_index += 1;
            if line[1].chars().nth(char_index).unwrap() == '\\' {
                char_index += 1;
            }
            // push the character literal
            curr_set.push(line[1].chars().nth(char_index).unwrap());
            // handle char range
            if (line[1].chars().count() - char_index) > 5
                && line[1].chars().nth(char_index + 2).unwrap() == '.'
                && line[1].chars().nth(char_index + 3).unwrap() == '.'
                && line[1].chars().nth(char_index + 4).unwrap() == '\''
            {
                let range_start: u8 = line[1].chars().nth(char_index).unwrap() as u8 + 1;
                let range_end: u8 = line[1].chars().nth(char_index + 5).unwrap() as u8;
                if range_start > range_end {
                    println!("Error while parsing character range: range start must be greater than range end.");
                    process::exit(-1);
                }
                for i in range_start..range_end {
                    curr_set.push(i as char);
                }
            }

            // handle operators
            handle_operators(next_op, &mut final_set, &mut curr_set);
            next_op = 0 as char;

            // closing \'
            char_index += 1;
        }

        if char_index == line[1].chars().count() - 1 {
            if is_whitespace {
                for c in &final_set {
                    whitespace.insert(*c);
                }
            } else {
                cat_table.insert(key.clone(), final_set.clone());
            }
        }
        char_index += 1;
    }
}

/// Parses a line from the TOKENS section. A regular expression is created for
/// the token and inserted in the `tok_table`.
///
/// Inputs:
///  - line:         a vector of `&str` representing the line.
///  - except_table: a mutable reference to the table that holds tokens that
///                  specify a "EXCEPT KEYWORDS" instruction.
///  - cat_table:    a reference to the character sets categories table.
///  - tok_table:    a mutable reference to the table holding the tokens.
///  - tokens_vec:   a mutable reference to the vector holding the `CocolToken`
///                  tokens. One `CocolToken` is created for every found token.
///
/// Outputs: updates the appropiate data structures passed as input.
fn parse_tokens_line(
    line: Vec<&str>,
    except_table: &mut HashMap<String, bool>,
    cat_table: &HashMap<String, Vec<char>>,
    tok_table: &mut HashMap<String, String>,
    tokens_vec: &mut Vec<CocolToken>,
) {
    let mut regex = String::from(PARENTHESES_OPEN);
    let mut char_index = 0;
    let mut sentence = line[1].trim().to_string();

    // process EXCEPT KEYWORDS
    if sentence.contains("EXCEPT KEYWORDS.") {
        except_table.insert(String::from(line[0].trim()), true);
        sentence = sentence.as_str()[0..sentence.len() - 17].to_string();
        sentence.push('.');
    }

    // token declaration must end with '.'
    if sentence.chars().nth(sentence.len() - 1).unwrap() != '.' {
        println!("Error: a token declaration must end with '.'");
        process::exit(-1);
    }

    while char_index < sentence.chars().count() {
        let c = sentence.chars().nth(char_index).unwrap();
        if c == ' ' {
            char_index += 1;
        } else if c == ')' || c == ']' || c == '}' {
            let cc = regex.pop().unwrap();
            if cc != CONCAT_CHAR {
                regex.push(cc);
            }
            regex.push(PARENTHESES_CLOSE);
            if c == ']' {
                regex.push(OPTIONAL_CHAR);
            } else if c == '}' {
                regex.push(KLEENE_CHAR);
            }
            regex.push(CONCAT_CHAR);
            char_index += 1;
        } else if c == '(' || c == '[' || c == '{' {
            regex.push(PARENTHESES_OPEN);
            char_index += 1;
            continue;
        } else if c == '|' {
            let cc = regex.pop().unwrap();
            if cc != CONCAT_CHAR {
                regex.push(cc);
            }
            regex.push(UNION_CHAR);
            char_index += 1;
            continue;
        } else if c == '\'' {
            char_index += 1;
            regex.push(PARENTHESES_OPEN);
            if sentence.chars().nth(char_index).unwrap() == '\\' {
                char_index += 1;
            }
            regex.push(sentence.chars().nth(char_index).unwrap());
            regex.push(PARENTHESES_CLOSE);
            regex.push(CONCAT_CHAR);
            // skip the closing '\''
            char_index += 2;
        } else if c == '\"' {
            char_index += 1;
            regex.push(PARENTHESES_OPEN);
            while sentence.chars().nth(char_index).unwrap() != '\"' {
                regex.push_str(&format!(
                    "{}{}",
                    sentence.chars().nth(char_index).unwrap(),
                    CONCAT_CHAR
                ));
                char_index += 1;
            }
            regex.pop();
            regex.push_str(&format!("{}{}", PARENTHESES_CLOSE, CONCAT_CHAR));
            char_index += 1;
            continue;
        } else if c.is_ascii_alphabetic() {
            let mut char_stack = String::new();
            let mut cc = sentence.chars().nth(char_index).unwrap();
            // grab the ident
            while cc.is_ascii_alphabetic() || cc.is_ascii_digit() {
                char_stack.push(sentence.chars().nth(char_index).unwrap());
                char_index += 1;
                cc = sentence.chars().nth(char_index).unwrap();
            }
            // search ident in cat table
            if cat_table.contains_key(&char_stack) {
                regex.push(PARENTHESES_OPEN);
                for cc in &cat_table[&char_stack] {
                    regex.push_str(&format!("{}{}", cc, UNION_CHAR));
                }
                regex.pop();
                regex.push_str(&format!("{}{}", PARENTHESES_CLOSE, CONCAT_CHAR));
            } else {
                println!(
                    "Error found while parsing TOKENS sections: token \"{}\" does not exist",
                    char_stack
                );
                process::exit(-1);
            }
        } else if c == '.' {
            break;
        }
    }
    // close regex
    regex.push(PARENTHESES_CLOSE);
    tok_table.insert(String::from_str(line[0].trim()).unwrap(), regex.clone());
    tokens_vec.push(CocolToken::new(
        String::from_str(line[0].trim()).unwrap(),
        regex,
    ));
}

/// This function is only used inside the parse_cocol_file function to avoid code repetition.
///
/// It mutates both sets `final_set` and `curr_set` accordingly to the value of `next_op`
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

/// Parses a COCOL/R grammar file, section by section.
///
/// Output:
/// - cat_table:    A table that holds all the character sets defined in the
///                 CHARACTERS section.
/// - keywords:     A table that holds all keywords defined in the KEYWORDS section.
/// - tok_table:    A table that holds all tokens found in the TOKENS section. The
///                 key is the token name and the value is the token regular expression.
/// - tokens_vec:   A vector that holds instances of `CocolToken`, for each token found
///                 in the TOKENS section.
/// - except_table: A table holding which tokens use the `EXCEPT KEYWORDS` syntax.
/// - whitespace:   A set of characters that are considered whitespace, as defined using
///                 the IGNORE syntax.
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
        let tokens: Vec<&str> = line.splitn(2, '=').collect();
        println!("tokens: {:?}", tokens);
        // update file section
        match sections.iter().position(|&s| s == tokens[0].trim()) {
            Some(pos) => {
                section = pos;
                continue;
            }
            None => (),
        };
        // process each section
        if section == 1 {
            // CHARACTERS
            if tokens.len() > 1 && tokens[0].len() > 0 {
                parse_characters_line(tokens, cat_table, whitespace, false);
            }
        } else if section == 2 {
            // KEYWORDS
            if tokens.len() == 2 {
                let mut keyword = String::from_str(tokens[1]).unwrap();
                keyword.retain(|a| a != '.');
                keywords.insert(keyword, String::from_str(tokens[0].trim()).unwrap());
            }
        } else if section == 3 && tokens.len() > 1 {
            parse_tokens_line(tokens, except_table, cat_table, tok_table, tokens_vec);
        } else if section == 4 {
            // PRODUCTIONS
        } else if section == 5 {
            if tokens[1] == grammar_name {
                // println!("Cocol/R file parsed successfully.");
            }
        } else if line.contains("IGNORE") {
            parse_characters_line(line.splitn(2, ' ').collect(), cat_table, whitespace, true);
        }
    }
}

/// Generates the lexical analyzer source file.
///
/// Input
///  - filename:         the file name of the lexical analyzer source file.
///  - dfa:              the DFA that represents the grammar parsed in the COCOL file.
///  - accepting_states: a mapping of state number to their corresponding token.
///  - keywords:         a map holding all the keywords found in the KEYWORDS section
///  - except_table:     a table holding which tokens use the `EXCEPT KEYWORDS` syntax.
///  - whitespace:       a set of characters marked as whitespace.
///
/// Output
///  - Writes the lexical analyzer source file to the project root directory.
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
                } else {
                    curr_lexeme.pop();
                    curr_idx -= 1;
                }
            }
        } else {
            println!(\"Scanner: char {} is invalid.\", curr_char as char);
            curr_state = 0;
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
    for i in 32..127 as u8 {
        if i as char == EXT_CHAR
            || i as char == UNION_CHAR
            || i as char == KLEENE_CHAR
            || i as char == CONCAT_CHAR
            || i as char == EPSILON
            || i as char == POSITIVE_CHAR
            || i as char == OPTIONAL_CHAR
        {
            continue;
        }
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

    println!("*************** COCOL/R Scanner Generator ****************");
    println!("* Reserved characters:");
    println!(
        "* {} {} {} {} {} {} {}",
        EXT_CHAR, UNION_CHAR, KLEENE_CHAR, CONCAT_CHAR, EPSILON, POSITIVE_CHAR, OPTIONAL_CHAR
    );
    println!("******************* Scanner Info ***********************");
    println!("********************* CHARACTERS *************************");
    for (key, value) in cat_table {
        println!("* {} => {:?}", key, value);
    }
    println!("********************* KEYWORDS *************************");
    for (key, value) in &keywords {
        println!("* {} => {}", key, value);
    }
    println!("********************* TOKENS *************************");
    let mut regex = String::from(PARENTHESES_OPEN);
    for token in &tokens {
        // extend the current regular expression
        let mut rregex = token.regex.clone();
        let mut count = 1;
        while rregex.chars().nth(rregex.len() - count).unwrap() == PARENTHESES_CLOSE {
            count += 1;
        }
        rregex.insert(rregex.len() - count + 1, EXT_CHAR);
        // append the current regex to the global regex with a UNION character.
        regex.push_str(&format!("{}{}", rregex, UNION_CHAR));
        println!("* {:?}", token);
        if except_table.contains_key(&token.name) {
            println!("\tcontains EXCEPT KEYWORDS");
        }
    }
    regex.pop();
    println!("******************* WHITESPACE ***********************");
    for c in &whitespace {
        println!("* ascii code: {}", *c as u8);
    }
    println!("****************** FINAL REGEX ***********************");
    regex.push(PARENTHESES_CLOSE);
    // replace '?' and '+' operators by the basic operators
    let proc_regex = preprocess_regex(&regex);
    // println!("{}", proc_regex);
    // create the alphabet using the symbols in the regex
    let mut letters = proc_regex.clone();
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
