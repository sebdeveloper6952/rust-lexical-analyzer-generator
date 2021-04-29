# Compilers Course 1 - Project 2 - Lexical Analyzer Generator

### Link to Video Presentation of Project

<https://youtu.be/gDfzbq9Sg0k>

### Prerequisites
- Docker

### To Begin
- clone or download the whole repository (<https://github.com/sebdeveloper6952/rust-lexical-analyzer-generator>)

### How to run

1. cd into the `rust-lexical-analyzer-generator` directory.
2. run the following command to create the project executable: `docker run --rm --user "$(id -u)":"$(id -g)" -v "$PWD:/usr/src/myapp" -w /usr/src/myapp rust cargo build --release`
3. run the following command to run the executable: `docker run --rm --user "$(id -u)":"$(id -g)" -v "$PWD:/usr/src/myapp" -w /usr/src/myapp rust ./target/release/rust-lexical-analyzer-generator <grammar_file>` There are some test grammar files on the `./pruebas` director. An example is: `./pruebas/CoCol.ATG`
4. compile the generated lexical analyzer: `docker run --rm --user "$(id -u)":"$(id -g)" -v "$PWD:/usr/src/myapp" -w /usr/src/myapp rust rustc -O ./rust-lex.rs`
5. run the lexical analyzer with a input file. An example is: `docker run --rm --user "$(id -u)":"$(id -g)" -v "$PWD:/usr/src/myapp" -w /usr/src/myapp rust ./rust-lex ./pruebas/CoCol.ATG`

### Generate the Project Documentation
1. cd into the `rust-lexical-analyzer-generator` directory.
1. run `docker run --rm --user "$(id -u)":"$(id -g)" -v "$PWD:/usr/src/myapp" -w /usr/src/myapp rust cargo doc`
2. in your web browser, open the file: `./target/doc/rust-lexical-analyzer-generator/index.html`. Browse through the documentation.
