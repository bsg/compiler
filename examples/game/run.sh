rm game *.o
cargo run --manifest-path ../../Cargo.toml -- ./main.bok --ast
clang ./main.o -o game -lSDL2 -lSDL2_image -lSDL2_ttf
./game