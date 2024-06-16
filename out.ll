define i32 @main() {
%1 = alloca i32, align 4
%2 = mul nsw i32 10, 2

store i32 %2, ptr %1, align 4

%3 = mul nsw i32 4, 3
%4 = load i32, ptr %1
%5 = add nsw i32 %3, %4
%6 = add nsw i32 5, %5
ret i32 %6
}
