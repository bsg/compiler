rm out *.o
cargo run -- --ast examples/test.bok
clang hello.o -o out
./out
echo "exit code:" $?