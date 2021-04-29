# Compilers Course 1 - Project 2 - Lexical Analyzer Generator

### Link to Video Presentation of Project

<https://youtu.be/0XQtm6eh_xE>

### Prerequisites
- Rust <>

### To Begin
- clone or download the whole repository (<https://github.com/sebdeveloper6952/rust-lexical-analyzer-generator>)

### How to run

1. cd into the `rust-lexical-analyzer-generator` directory.
2. run the following command to create the project executable: `cargo build --release`
3. run the project executable with an input grammar file: `./target/release/rust-lexical-analyzer-generator ./pruebas/CoCol.ATG`
4. compile the generated lexical analyzer: `rustc -O ./rust-lex.rs`
5. run the lexical analyzer with an input file: `./rust-lex ./pruebas/CoCol.ATG`

### Generate the Project Documentation
1. cd into the `rust-lexical-analyzer-generator` directory.
1. run `cargo doc --open`
