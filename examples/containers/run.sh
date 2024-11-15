rm out *.o
cargo run --manifest-path ../../Cargo.toml -- ./main.bok --ast
clang ./main.o -o out
./out