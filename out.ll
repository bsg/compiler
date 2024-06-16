define i32 @main(i32 %0) {
%2 = alloca i32, align 4
%3 = mul nsw i32 10, 2
store i32 %3, ptr %2, align 4
%4 = mul nsw i32 4, 3
%5 = load i32, ptr %2
%6 = add nsw i32 %4, %5
%7 = add nsw i32 5, %6
ret i32 %7
}
