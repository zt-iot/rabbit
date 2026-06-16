#if defined(__CYGWIN__) || defined(_WIN32)
#define __WINDOWS__
#else
#include <sys/types.h>
#include <sys/ioctl.h>
#include <stdio.h>
#endif

#define CAML_NAME_SPACE
#include <caml/config.h>
#include <caml/mlvalues.h>
#include <caml/memory.h>
#include <caml/alloc.h>

CAMLprim value get_columns(value unit)
{
  CAMLparam1(unit);
  CAMLlocal1(result);
#ifdef __WINDOWS__
  result = Val_long(-1);
#else
  struct winsize ws;
  ioctl(1, TIOCGWINSZ, &ws);
  result = Val_long(ws.ws_col);
#endif
  CAMLreturn(result);
}
