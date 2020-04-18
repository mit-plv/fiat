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
        pushl   $.LC0
        call    puts
        call    _exit

sys_ret1:
        addl    $4, %esp
	movl	%eax, %edi
	ret

sys_ret2:
        addl    $8, %esp
	movl	%eax, %edi
	ret

sys_ret3:
        addl    $12, %esp
	movl	%eax, %edi
	ret
        
sys_printInt:
        pushl   %esi
        pushl	bedrock_heap+4(%ebx)
        pushl   $sys_ret1
        jmp     _sys_printInt

sys_listen:
        pushl   %esi
        pushl	bedrock_heap+4(%ebx)
        pushl   $sys_ret1
        jmp     _sys_listen

sys_accept:
        pushl   %esi
        pushl	bedrock_heap+4(%ebx)
        pushl   $sys_ret1
        jmp     _sys_accept

sys_connect:
        pushl   %esi
        pushl	bedrock_heap+8(%ebx)
        movl	bedrock_heap+4(%ebx), %esi
	addl	$bedrock_heap, %esi
        pushl	%esi
        pushl   $sys_ret2
        jmp     _sys_connect

sys_read:
        pushl   %esi
        pushl	bedrock_heap+12(%ebx)
        movl	bedrock_heap+8(%ebx), %esi
	addl	$bedrock_heap, %esi
        pushl	%esi
        pushl	bedrock_heap+4(%ebx)
        pushl   $sys_ret3
        jmp     _sys_read

sys_write:
        pushl   %esi
        pushl	bedrock_heap+12(%ebx)
        movl	bedrock_heap+8(%ebx), %esi
	addl	$bedrock_heap, %esi
        pushl	%esi
        pushl	bedrock_heap+4(%ebx)
        pushl   $sys_ret3
        jmp     _sys_write

sys_declare:
        pushl   %esi
        pushl	bedrock_heap+8(%ebx)
        pushl	bedrock_heap+4(%ebx)
        pushl   $sys_ret2
        jmp     _sys_declare

sys_wait:
        pushl   %esi
        pushl	bedrock_heap+4(%ebx)
        pushl   $sys_ret1
        jmp     _sys_wait

sys_close:
        pushl   %esi
        pushl	bedrock_heap+4(%ebx)
        pushl   $sys_ret1
        jmp     _sys_close
