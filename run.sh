cargo run -- examples/hello.bok > out.ll
cargo run -- --ast examples/hello.bok > ast.txt
clang out.ll -o out
./out
echo "exit code:" $?