        .section        .rodata
.LC0:
        .string "Bedrock main() returned (should never happen!)\n"
        .text

        .globl sys_abort
        .globl _sys_printInt, sys_printInt
	.global _sys_listen, sys_listen
	.global _sys_accept, sys_accept
     	.global _sys_connect, sys_connect
	.globl _sys_read, sys_read
	.globl _sys_write, sys_write
        .global _sys_declare, sys_declare
	.global _sys_wait, sys_wait
        .global _sys_close, sys_close

        .globl main
main:
        movl    $ret, %esi
        jmp     main_main
ret:
        movl    $.LC0, %eax
        movq    %rax, %rdi
        movl    $0, %eax
        call printf
        call _exit

sys_printInt:
        movl	bedrock_heap+4(%rbx), %edi
        pushq   %rsi
        jmp     _sys_printInt

sys_listen:
        movl	bedrock_heap+4(%rbx), %edi
	pushq	%rsi
        pushq   $sys_ret
        jmp     _sys_listen
sys_ret:
	movl	%eax, %edi
	retq

sys_accept:
        movl	bedrock_heap+4(%rbx), %edi
	pushq	%rsi
        pushq   $sys_ret
        jmp     _sys_accept

sys_connect:
	pushq	%rsi
        movl	bedrock_heap+4(%rbx), %edi
       	addl	$bedrock_heap, %edi
        movl	bedrock_heap+8(%rbx), %esi
        pushq   $sys_ret
        jmp     _sys_connect

sys_read:
	pushq	%rsi
        movl	bedrock_heap+4(%rbx), %edi
	movl	bedrock_heap+8(%rbx), %esi
	addl	$bedrock_heap, %esi
	movl	bedrock_heap+12(%rbx), %edx
        pushq   $sys_ret
        jmp     _sys_read

sys_write:
	pushq	%rsi
        movl	bedrock_heap+4(%rbx), %edi
	movl	bedrock_heap+8(%rbx), %esi
	addl	$bedrock_heap, %esi
	movl	bedrock_heap+12(%rbx), %edx
        pushq   $sys_ret
        jmp     _sys_write

sys_declare:
	pushq	%rsi
        movl	bedrock_heap+4(%rbx), %edi
	movl	bedrock_heap+8(%rbx), %esi
        pushq   $sys_ret
        jmp     _sys_declare

sys_wait:
        movl	bedrock_heap+4(%rbx), %edi
        pushq   %rsi
        pushq   $sys_ret
        jmp     _sys_wait

sys_close:
        movl	bedrock_heap+4(%rbx), %edi
        pushq   %rsi
        jmp     _sys_close
