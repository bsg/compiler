rm out *.o
cargo run -- --ast examples/test.bok
clang main.o -o out
./out
echo "exit code:" $?