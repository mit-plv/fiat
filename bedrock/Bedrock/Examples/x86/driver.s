        .section        .rodata
.LC0:
        .string "Answer: %d\n"
        .text

        .globl main, factDriver_main
main:
        movl    $ret, %esi
        jmp     factDriver_main
ret:
        movl    %edi, %esi
        movl    $.LC0, %eax
        movq    %rax, %rdi
        movl    $0, %eax
        call printf
        call _exit
