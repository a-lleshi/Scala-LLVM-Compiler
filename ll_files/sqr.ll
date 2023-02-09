
declare i32 @printf(i8*, ...)

@.str = private constant [4 x i8] c"%d\0A\00"
@.str_nl = private constant [2 x i8] c"\0A\00"
@.str_star = private constant [2 x i8] c"*\00"
@.str_space = private constant [2 x i8] c" \00"
@.str_char = private constant [2 x i8] c"%c"

define void @new_line() #0 {
  %t0 = getelementptr [2 x i8], [2 x i8]* @.str_nl, i32 0, i32 0
  %1 = call i32 (i8*, ...) @printf(i8* %t0)
  ret void
}

define void @print_star() #0 {
  %t0 = getelementptr [2 x i8], [2 x i8]* @.str_star, i32 0, i32 0
  %1 = call i32 (i8*, ...) @printf(i8* %t0)
  ret void
}

define void @print_space() #0 {
  %t0 = getelementptr [2 x i8], [2 x i8]* @.str_space, i32 0, i32 0
  %1 = call i32 (i8*, ...) @printf(i8* %t0)
  ret void
}

define void @print_int(i32 %x) {
   %t0 = getelementptr [4 x i8], [4 x i8]* @.str, i32 0, i32 0
   call i32 (i8*, ...) @printf(i8* %t0, i32 %x) 
   ret void
}

define void @print_char(i32 %x) {
   %t0 = getelementptr [2 x i8], [2 x i8]* @.str_char, i32 0, i32 0
   call i32 (i8*, ...) @printf(i8* %t0, i32 %x) 
   ret void
}

define void @skip() #0 {
  ret void
}

; END OF BUILD-IN FUNCTIONS (prelude)
   @Max = global i32 10
define i32 @sqr(i32  %x) {
   %tmp_0 = mul i32  %x, %x
   ret i32 %tmp_0
}

define void @all(i32  %n) {
   %tmp_2 = load i32, i32* @Max
   %tmp_1 = icmp sle i32  %n, %tmp_2
   br i1 %tmp_1, label %if_branch_9, label %else_branch_10

if_branch_9:
   %tmp_3 = call i32 @sqr(i32 %n)
   call void @print_int(i32 %tmp_3)
   call void @new_line()
   %tmp_6 = add i32  %n, 1
   call void @all(i32 %tmp_6)
   ret void

else_branch_10:
   call void @skip()
   ret void
}

define i32 @main() {
   call void @all(i32 0)
   ret i32 0
}
