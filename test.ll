define i32 @main() {
    %1 = add nsw i32 2, 3
    %2 = add nsw i32 1, %1
    ret i32 %2
}