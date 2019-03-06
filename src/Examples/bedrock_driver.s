        .equ HEAP_SIZE, 100*1024*1024
        .equ STACK_OFFSET, 4*HEAP_SIZE
        .equ STACK_START, bedrock_heap+STACK_OFFSET
        .equ LIST_START, 4
        
        .globl bedrock_main
bedrock_main:
        # Initialize Bedrock stack pointer
        movl    $STACK_OFFSET, %ebx

        # Set up parameters to entry point
        movl    $LIST_START, STACK_START+4
        movl    $0, STACK_START+8
       
        movl    $ret, %esi
        jmp     export_dffun
ret:
        movl    %edi, %eax
        ret
