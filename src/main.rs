use serde::{Deserialize, Serialize};
use std::collections::{HashMap, HashSet};
use std::env;
use std::fmt;
use std::fs;
use std::fs::File;
use std::io::{self, BufRead};
use std::iter::FromIterator;
use std::process;
use std::str::FromStr;
use std::time::Instant;

/// Global variables
/// the representation of the Epsilon character
const EPSILON: char = '@';

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

fn parse_cocol_file(
    path: &str,
    cat_table: &mut HashMap<String, Vec<char>>,
    keywords: &mut HashMap<String, String>,
    tok_table: &mut HashMap<String, String>,
    tokens_vec: &mut Vec<CocolToken>,
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
        let tokens: Vec<&str> = line.split(' ').collect();
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
            if tokens.len() == 3 {
                if tokens[0].len() > 0 {
                    let key = String::from_str(tokens[0]).unwrap();
                    if !cat_table.contains_key(tokens[0]) {
                        cat_table.insert(key.clone(), Vec::new());
                    }

                    let mut parsing_basic_set = false;
                    let mut parsing_ident = false;
                    let mut ident_vec = String::new();
                    let mut final_set: Vec<char> = Vec::new();
                    let mut curr_set: Vec<char> = Vec::new();
                    let mut next_op: char = 0 as char;
                    for c in tokens[2].chars() {
                        // begin parsing basic set
                        if c == '\"' && !parsing_basic_set && !parsing_ident {
                            parsing_basic_set = true;
                            continue;
                        }
                        // begin parsing ident
                        if c.is_ascii_alphanumeric() && !parsing_ident && !parsing_basic_set {
                            parsing_ident = true;
                            ident_vec.push(c);
                            continue;
                        }

                        // save next operator
                        if c == '+' || c == '-' {
                            next_op = c;
                            if parsing_basic_set {
                                parsing_basic_set = false;
                                cat_table.insert(key.clone(), final_set.clone());
                            } else if parsing_ident {
                                parsing_ident = false;
                                final_set.extend(cat_table[&ident_vec].clone());
                                ident_vec.clear()
                            }
                            continue;
                        }

                        if parsing_basic_set {
                            if c == '\"' {
                                parsing_basic_set = false;
                                if next_op == '+' {
                                    // final_set UNION curr_set
                                    final_set.extend(&curr_set);
                                    cat_table.insert(key.clone(), final_set.clone());
                                    next_op = 0 as char;
                                } else if next_op == '-' {
                                    // final_set DIFF curr_set
                                    let s_0: HashSet<char> =
                                        final_set.clone().into_iter().collect();
                                    let s_1: HashSet<char> = curr_set.clone().into_iter().collect();
                                    let v: Vec<char> = s_0.difference(&s_1).map(|c| *c).collect();
                                    final_set.clear();
                                    final_set.extend(&v);
                                    // push
                                    cat_table.insert(key.clone(), final_set.clone());
                                    next_op = 0 as char;
                                } else {
                                    // push
                                    cat_table.insert(key.clone(), curr_set.clone());
                                }
                            } else {
                                curr_set.push(c);
                            }
                        } else if parsing_ident {
                            if c.is_ascii_alphanumeric() {
                                ident_vec.push(c);
                            } else {
                                parsing_ident = false;
                                curr_set.extend(cat_table[&ident_vec].clone());
                                if next_op == '+' {
                                    // final_set UNION curr_set
                                    final_set.extend(&curr_set);
                                    next_op = 0 as char;
                                } else if next_op == '-' {
                                    // final_set DIFF curr_set
                                    let s_0: HashSet<char> =
                                        final_set.clone().into_iter().collect();
                                    let s_1: HashSet<char> = curr_set.clone().into_iter().collect();
                                    let v: Vec<char> = s_0.intersection(&s_1).map(|c| *c).collect();
                                    final_set.clear();
                                    final_set.extend(&v);
                                    next_op = 0 as char;
                                }
                                // reset state
                                ident_vec.clear();
                                continue;
                            }
                        }
                    }
                }
            }
        } else if section == 2 {
            // KEYWORDS
            if tokens.len() == 3 {
                println!("parsing keyword: {:?}", tokens);
                let mut keyword = String::from_str(tokens[2]).unwrap();
                keyword.retain(|a| a != '.');
                keywords.insert(keyword, String::from_str(tokens[0]).unwrap());
            }
        } else if section == 3 {
            // TOKENS
            if tokens.len() > 2 {
                println!("parsing token: {:?}", tokens);
                let mut char_stack = String::new();
                let mut regex = String::from('(');
                for i in 0..tokens[2].chars().count() {
                    let c = tokens[2].chars().nth(i).unwrap();
                    if c.is_ascii_alphanumeric() {
                        // accumulate identifier
                        char_stack.push(c);
                    } else {
                        if char_stack.is_empty() {
                            if c == '(' || c == '{' || c == '[' || c == '\"' {
                                regex.push('(');
                            }
                            continue;
                        }
                        // check if ident exists
                        if cat_table.contains_key(&char_stack) {
                            println!("\tfound ident: {:?}", char_stack);
                            // get symbols from category table
                            let symbols = cat_table[&char_stack].clone();
                            regex.push('(');
                            for s in symbols {
                                regex.push_str(&format!("{}|", s));
                            }
                            // pop extra '|'
                            regex.pop();
                            // insert closing parentheses
                            regex.push(')');

                            // handle ident finish character
                            if c == '{' {
                                regex.push_str(".(");
                            } else if c == '}' {
                                regex.push_str(")*");
                            } else if c == '[' {
                                regex.push_str(".(");
                            } else if c == ']' {
                                regex.push_str(")?");
                            } else if c == '(' {
                                regex.push_str(".(");
                            } else if c == ')' {
                                regex.push(')');
                            } else if c == '|' {
                                regex.push('|');
                            } else if c == '\"' {
                                regex.push(')');
                            }
                        } else if c == '\"' {
                            while !char_stack.is_empty() {
                                regex.push_str(&format!("{}.", char_stack.remove(0)));
                            }
                            regex.pop();
                            regex.push_str(").");
                        }
                        // TODO process EXCEPT

                        // clear stack to get next ident
                        char_stack.clear();
                    }
                }
                regex.push_str(".#");
                regex.push(')');
                tok_table.insert(String::from_str(tokens[0]).unwrap(), regex.clone());
                tokens_vec.push(CocolToken::new(String::from_str(tokens[0]).unwrap(), regex));
            }
        } else if section == 4 {
            // PRODUCTIONS
        } else if section == 5 {
            if tokens[1] == grammar_name {
                println!("Cocol/R file parsed successfully.");
            }
        }
    }
}

/// Is the char an operator?
fn is_op(c: char) -> bool {
    match c {
        '*' => true,
        '.' => true,
        '|' => true,
        _ => false,
    }
}

/// Is the char valid in our regular expressions?
fn is_valid_regex_symbol(c: &char) -> bool {
    c.is_ascii_alphanumeric() || *c == '#' || *c == EPSILON
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
        let mut new_node = Node::new('.', 0, false);
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
    dfa: HashMap<u32, HashMap<char, u32>>,
    /// The set of accepting states of this `Dfa`.
    accepting_states: Vec<u32>,
}

impl Dfa {
    /// Create a new DFA.
    ///
    /// `dfa`: the transition table for the new DFA.
    /// `accepting_states`: a vector containing the set of accepting states of
    /// the new DFA.
    fn new(dfa: HashMap<u32, HashMap<char, u32>>, accepting_states: Vec<u32>) -> Dfa {
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

#[derive(Serialize)]
/// Struct to represent a finite automata and serialize it
/// to JSON.
///
/// Contains a regular expression, an alphabet, and the finite
/// automata. The finite automata can be an instance of a Nfa,
/// or a Dfa.
struct FAFile {
    /// The alphabet that was extracted from the `regex`.
    alphabet: HashSet<char>,
    /// The regular expression recognized by this `fa`.
    regex: String,
    /// A finite automata instance, it can be a `Nfa` of a `Dfa`.
    dfa: Dfa,
}

impl FAFile {
    /// Create a new FaFile.
    fn new(alphabet: HashSet<char>, regex: String, dfa: Dfa) -> FAFile {
        FAFile {
            alphabet,
            regex,
            dfa,
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
    precedences.insert('(', 0);
    precedences.insert('|', 1);
    precedences.insert('.', 2);
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
                } else if op == '.' {
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
                } else if top_op == '.' {
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
        } else if top_op == '.' {
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
    let mut dfa: HashMap<u32, HashMap<char, u32>> = HashMap::new();
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
                    .insert(*a, d_states_map[&u_vec]);
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

fn simulate(
    dfa: &Dfa,
    accepting_states: &HashMap<u32, CocolToken>,
    sentence: &String,
) -> Vec<Token> {
    let bytes: &[u8] = sentence.as_bytes();
    let mut curr_idx = 0;
    let mut curr_state = 0;
    let mut states: Vec<u32> = Vec::new();
    let mut curr_lexeme = String::new();
    let mut found_tokens: Vec<Token> = Vec::new();
    while curr_idx < bytes.len() {
        // move to the next state
        let curr_char = bytes[curr_idx] as char;
        if dfa.dfa[&curr_state].contains_key(&curr_char) {
            let next_state = dfa.dfa[&curr_state][&curr_char];
            curr_state = next_state;
            states.push(curr_state);
            curr_lexeme.push(curr_char);
            curr_idx += 1;
        }
        // no match, we are in the ERROR STATE
        else if !states.is_empty() {
            while !states.is_empty() {
                let top = states.pop().unwrap();
                if accepting_states.contains_key(&top) {
                    found_tokens.push(Token::new(
                        accepting_states[&top].name.clone(),
                        curr_lexeme.clone(),
                    ));
                    // reset state
                    curr_state = 0;
                    states.clear();
                    curr_lexeme.clear();
                }
            }
        } else {
            curr_idx += 1;
        }
    }

    found_tokens
}

fn generate_code(filename: &str, dfa: &Dfa) {
    let serialized_dfa = serde_json::to_string(&dfa).unwrap();
    let code = String::from(&format!(
        "
use std::collections::HashMap;
use serde::Deserialize;

fn main() {{
    let dfa: Dfa = serde_json::from_str(\"{}\").unwrap();
    println!(\"{{:?}}\", dfa);
}}
    ",
        serialized_dfa
    ));
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

    // parse cocol file and update data structures
    parse_cocol_file(
        &args[1],
        &mut cat_table,
        &mut keywords,
        &mut tok_table,
        &mut tokens,
    );

    println!("\n******************* Scanner Info ***********************");
    println!("********************* CHARACTERS *************************");
    for (key, value) in cat_table {
        println!("{} => {:?}", key, value);
    }
    println!("********************* KEYWORDS *************************");
    for (key, value) in keywords {
        println!("{} => {}", key, value);
    }
    println!("********************* TOKENS *************************");
    let mut regex = String::from("(");
    for token in &tokens {
        regex.push_str(&format!("{}|", token.regex));
        println!("{:?}", token);
    }
    regex.pop();
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
    let mut tokens_accepting_states: HashMap<u32, CocolToken> = HashMap::new();
    let direct_dfa = regex_dfa(
        &fp_table,
        &pos_table,
        &tokens,
        &mut tokens_accepting_states,
        &tree_root,
        &alphabet,
    );

    // code generation
    generate_code("rust-lex.rs", &direct_dfa);
    println!("File rust-lex.rs written correctly.");

    // println!("****************** FINAL ACCEPTING STATES ***********************");
    // for (key, value) in &tokens_accepting_states {
    //     println!("{} => {:?}", key, value);
    // }

    // println!("\n****************** SIMULATION ***********************");
    // let sentence = String::from("var = 123; hex = 0xFF;");
    // println!("Simulating sentence: {}", sentence);
    // let tokens = simulate(&direct_dfa, &tokens_accepting_states, &sentence);
    // for token in tokens {
    //     println!("Found token: {:?}", token);
    // }

    // direct
    // let ddfa_file = FAFile::new(alphabet.clone(), regex.to_string(), direct_dfa);
    // let serialized = serde_json::to_string(&ddfa_file).unwrap();
    // fs::write("./dfa.json", serialized).expect("Error writing to file.");
}
