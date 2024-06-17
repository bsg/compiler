cargo run -- examples/hello.txt > out.ll
cargo run -- --ast examples/hello.txt > ast.txt
clang out.ll -o out
./out
echo "exit code:" $?