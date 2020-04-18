        .section        .rodata
.LC0:
        .string "%d\n"
        .text

        .globl main
main:
        movl    $0, %ebx
        movl    $5, bedrock_heap+4
        movl    $ret, %ecx
        jmp     fact_fact
ret:
        movl    %eax, %esi
        movl    $.LC0, %eax
        movq    %rax, %rdi
        movl    $0, %eax
        call printf
        call _exit
