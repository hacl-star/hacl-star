#include <sys/types.h>
#include <sys/wait.h>
#include <unistd.h>
#include <stdlib.h>
#include <signal.h>

pid_t f;

void timeout(int s)
{
  killpg(f,SIGTERM);
  kill(getpid(),SIGALRM);
  _exit(111);
}

int main(int argc,char **argv)
{
  struct sigaction sa;
  int seconds;
  int w;

  if (!*argv) return 100;

  if (!*++argv) return 100;
  seconds = atoi(*argv);

  if (!*++argv) return 100;

  f = fork();
  if (f == -1) return 111;

  if (f == 0) {
    setpgid(0,0);
    execvp(*argv,argv);
    return 111;
  }

  sa.sa_handler = timeout;
  sigemptyset(&sa.sa_mask);
  sa.sa_flags = SA_RESETHAND | SA_NODEFER;
  sigaction(SIGALRM,&sa,0);
  alarm(seconds);

  while (wait(&w) != f) ;
  if (WIFEXITED(w)) return WEXITSTATUS(w);
  return 111;
}
