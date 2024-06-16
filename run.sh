cargo run -- examples/hello.txt > out.ll
clang out.ll -o out
./out
echo $?