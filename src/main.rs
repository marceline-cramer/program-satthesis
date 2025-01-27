fn main() {
    let path = std::env::args()
        .nth(1)
        .expect("expected path to DIMACS file");

    program_satthesis::run(&path, false);
}
