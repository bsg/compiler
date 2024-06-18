cargo run -- examples/test.bok
# don't run this twice
# cargo run -- --ast examples/hello.bok > ast.txt
clang hello.o -o out
./out
echo "exit code:" $?