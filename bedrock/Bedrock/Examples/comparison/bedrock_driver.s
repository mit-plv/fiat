        .section        .rodata
.LC0:
        .string "%d\n"
        .text

        .equ HEAP_SIZE, 100*1024*1024
        .equ STACK_OFFSET, 4*HEAP_SIZE+12
        .equ STACK_START, bedrock_heap+STACK_OFFSET
        
        .globl main
main:
        # Initialize malloc heap
        movl    $4, bedrock_heap
        movl    $HEAP_SIZE, bedrock_heap+4
        movl    $0, bedrock_heap+8

        # Initialize Bedrock stack pointer
        movl    $STACK_OFFSET, %ebx

        # Set up parameters to m.main()
        # cmd
        movl    $cmd, %eax
        subl    $bedrock_heap, %eax
        movl    %eax, STACK_START+4
        # cmdLen
        movl    cmdLen, %eax
        movl    %eax, STACK_START+8
        # data
        movl    $data, %eax
        subl    $bedrock_heap, %eax
        movl    %eax, STACK_START+12
        # dataLen
        movl    dataLen, %eax
        movl    %eax, STACK_START+16
        
        movl    $ret, %esi
        jmp     m_main
ret:
        movl    %edi, %ebx
loop:
        cmpl    $0, %ebx
        jz      done
        movl    bedrock_heap(%ebx), %esi
        movl    $.LC0, %eax
        movq    %rax, %rdi
        movl    $0, %eax
        call    printf
        movl    bedrock_heap+4(%ebx), %ebx
        jmp     loop
done:
        
        call exit
