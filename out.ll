define i32 @main(i32 %0) {
%2 = alloca i32, align 4
%3 = mul nsw i32 10, 2
store i32 %3, ptr %2, align 4
%4 = load i32, ptr %2
%5 = call i32 @square(i32 2)
%6 = call i32 @add(i32 %4, i32 %5)
ret i32 %6
}

define i32 @square(i32 %0) {
%2 = mul nsw i32 %0, %0
ret i32 %2
}

define i32 @add(i32 %0, i32 %1) {
%3 = add nsw i32 %0, %1
ret i32 %3
}

define i1 @foo(i1 %0) {
ret i1 %0
}


