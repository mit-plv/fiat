// Bedrock "Real-Time Operating System" C interface

// This is a library for cooperative multithreading, which does not depend on
// the underlying system to provide any multiplexing of memory or CPU.
// It runs on Linux, but it should also run directly on top of CertiKOS.
// The file `bedrock.s' is generated with the Bedrock system within Coq.
// The thread library code therein has been formally verified.
// The formal guarantees aren't about interaction with C code, so you can
// definitely make bad things happen using this packaging as a C library!

// For instance, stack overflows won't be caught dynamically, so be sure to
// allocate enough stack space for your threads!
// Create the following global variable in your application, storing the number
// of _words_ (4 bytes each) per thread stack.
extern int bedrock_stack_size;

// Your application should create an entry-point function
//   void rtos_main() { ... }
// Before returning, you probably want to create some threads, by passing their
// entry-point function pointers to this function:
typedef void (*thread_entry_point)(void);
void bedrock_spawn(thread_entry_point);
// Define the entry-point functions using some macros at the end of this file,
// like so:
// BEDROCK_THREAD(name) { ...code here... }
// BEDROCK_WRAP(name)
// void rtos_main() { ... bedrock_spawn(name); ... }

// A thread should finish by calling the following function.
// GCC should signal a static error if a thread handler could return normally.
__attribute__((noreturn)) void bedrock_exit();

// This is _cooperative_ multithreading, so a compute-bound thread should call
// the following function periodically, to switch to a different thread.
void bedrock_yield();

// Next come a set of IO functions, for manipulating file descriptors.
typedef unsigned fd_t;
// Functions described as blocking may switch to a different thread, if the
// requested IO action isn't enabled yet.  Other functions stay in the
// current thread.

fd_t bedrock_listen(unsigned port);
// Listen for TCP connections on a specific port.

fd_t bedrock_accept(fd_t listener);
// Accept a connection from a listener.  (Blocking)

fd_t bedrock_connect(const char *address, unsigned size);
// Connect to a host/port described with a string.
// We represent a string with bytes+length, instead of zero termination.

void bedrock_close(fd_t);
// Close an open file descriptor.

unsigned bedrock_read(fd_t, const char *buf, unsigned size);
unsigned bedrock_write(fd_t, char *buf, unsigned size);
// The usual C-style input-output interface.  (Blocking)

void bedrock_connected(fd_t);
// Wait until a stream opened with bedrock_connect() is established.  (Blocking)


// Nasty macros for wrapping C functions so that they look like Bedrock code
#define BEDROCK_THREAD(name) __attribute__((noreturn)) void name##_handler()
#define BEDROCK_WRAP(name) __attribute__((noreturn)) void name(); asm(#name ":"); asm("movl %ebx, bedrock_heap + (1024 * 1024 + 50 + 1)*4"); asm("movl bedrock_stack_size, %esp"); asm("shll $2, %esp"); asm("addl %ebx, %esp"); asm("addl $bedrock_heap, %esp"); asm("jmp " #name "_handler");
