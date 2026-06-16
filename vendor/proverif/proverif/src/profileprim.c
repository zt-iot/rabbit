#include <stdio.h>
#include <sys/time.h>

#include <errno.h>
#include <fcntl.h>
#include <signal.h>
#include <stdlib.h>
#include <string.h>
#if !macintosh
#include <sys/types.h>
#include <sys/stat.h>
#endif
#include <caml/config.h>
#ifdef HAS_UNISTD
#include <unistd.h>
#endif
#include <time.h>
#include <sys/times.h>
#include <caml/mlvalues.h>
#include <caml/memory.h>
#ifndef CLK_TCK
#ifdef HZ
#define CLK_TCK HZ
#else
#define CLK_TCK 60
#endif
#endif


#define stack_size 1000

typedef struct {
   int self_ctr, total_ctr;
} prof_info;

prof_info stack[stack_size];

int sp;
int ticks;

void handler(sig)
      int sig;
{
  int i;

#ifndef POSIX_SIGNALS
#ifndef BSD_SIGNALS
  signal(sig, handler);
#endif
#endif

   ticks++;

   if (sp>0) stack[sp-1].self_ctr++;
   for (i=0; i<sp; i++)
      stack[i].total_ctr++;

}

value push_stack(dummy) /* ML */
       value dummy;
{
   stack[sp].self_ctr = 0;
   stack[sp].total_ctr = 0;
   sp++;

   return Val_unit;
}

value pop_stack(info) /* ML */
      value info;
{
   sp--;
   caml_modify(&Field(info,2), Val_int(stack[sp].self_ctr + Int_val(Field(info,2))));
   caml_modify(&Field(info,3), Val_int(stack[sp].total_ctr + Int_val(Field(info,3))));

   return Val_unit;
}

value start(dummy) /* ML */
     value dummy;
{
  struct itimerval itvalue = {{0, 1000},{0,1000}};
#ifdef POSIX_SIGNALS
  struct sigaction sigact;
#endif

  sp = 0;
  ticks = 0;
#ifdef POSIX_SIGNALS
  sigact.sa_handler = handler;
  sigemptyset(&sigact.sa_mask);
  sigact.sa_flags = 0;
  sigaction(SIGPROF, &sigact, NULL);
#else
  signal(SIGPROF, handler);
#endif
  setitimer(ITIMER_PROF, &itvalue, NULL);
  return Val_unit;
}

value stop(dummy) /* ML */
      value dummy;
{
  struct itimerval itvalue = {{0, 0}, {0, 0}};
#ifdef POSIX_SIGNALS
  struct sigaction sigact;
#endif

  setitimer(ITIMER_PROF, &itvalue, NULL);
#ifdef POSIX_SIGNALS
  sigact.sa_handler = SIG_DFL;
  sigemptyset(&sigact.sa_mask);
  sigact.sa_flags = 0;
  sigaction(SIGPROF, &sigact, NULL);
#else
  signal(SIGPROF, SIG_DFL);
#endif

  return Val_int(ticks);
}
