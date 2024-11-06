rm game *.o
cargo run --manifest-path ../../Cargo.toml -- ./main.bok
clang ./main.o -o game -lSDL2 -lSDL2_image -lSDL2_ttf -lSDL2_mixer
./game