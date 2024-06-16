define i32 @main() {
%1 = alloca i32, align 4
store i32 0, ptr %1, align 4

%2 = mul nsw i32 4, 3
%3 = load i32, ptr %1
%4 = add nsw i32 %2, %3
%5 = add nsw i32 5, %4
ret i32 %5
}
