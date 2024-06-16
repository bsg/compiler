define i32 @main() {
%1 = mul nsw i32 4, 3
%2 = add nsw i32 %1, 10
%3 = add nsw i32 5, %2
ret i32 %3
}
