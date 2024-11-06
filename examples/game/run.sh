rm game *.o
cargo run --manifest-path ../../Cargo.toml -- ./main.bok --asm
clang ./main.o -o game -lSDL2 -lSDL2_image -lSDL2_ttf -lSDL2_mixer
echo Running
./game