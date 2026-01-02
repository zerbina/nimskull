/* Provides some bridging for making LibC entities available to LLVM code */

#include <stdio.h>
#include <stdlib.h>
#include <errno.h>

FILE* impl_stdin;
FILE* impl_stdout;
FILE* impl_stderr;

_Thread_local errno_t* impl_errno;

wchar_t ** impl_wenviron;

void llvm_init() {
  impl_stdin = stdin;
  impl_stdout = stdout;
  impl_stderr = stderr;

  impl_errno = &errno;

#ifdef WIN32
  impl_wenviron = _wenviron;
#endif
}
