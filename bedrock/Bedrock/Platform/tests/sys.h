__attribute__((noreturn)) void sys_abort();
void _sys_printInt(unsigned);
unsigned _sys_listen(unsigned port);
unsigned _sys_accept(unsigned sock);
unsigned _sys_read(unsigned sock, void *buf, unsigned count);
unsigned _sys_write(unsigned sock, void *buf, unsigned count);
unsigned _sys_declare(unsigned sock, unsigned mode);
unsigned _sys_wait(unsigned blocking);
void _sys_close(unsigned sock);
