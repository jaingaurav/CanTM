#if 0
int a, b, c, d;

int foo(int& e)
{
    return e+1;
}

int tx()
{
    int *f = &b;
    a = 2;
    *f = 50;
    if (d > 0)
    {
        b = foo(*f);
        b = c;
        f = &a;
    }
    else
    {
        f = &c;
        a = foo(b);
    }
    *f = 100;

    return a + b;
}
#endif

#include <inttypes.h>

#include <stdint.h>
#include <stdio.h>
#include <stdarg.h>

void stm_reserve( int num_args, ...)
{
  int i;
  uintptr_t val;
  va_list vl;
  va_start(vl,num_args);
  int num_loads = va_arg(vl,int);
  printf ("%d Load(s) passed: ", num_loads);
  for (i=0;i<num_loads;i++)
  {
    val=va_arg(vl,uintptr_t);
    printf ("%016"PRIxPTR" ", val);
  }
  int num_stores = va_arg(vl,int);
  printf ("%d Store(s) passed: ", num_stores);
  for (i=0;i<num_stores;i++)
  {
    val=va_arg(vl,uintptr_t);
    printf ("%016"PRIxPTR" ", val);
  }
  va_end(vl);
  printf ("\n");
}

int a, b, c, d;

int foo(int& b)
{
    return b+1;
}

int tx()
{
    int i = 1;
    a = 2;
    a = i;
    d = -2;
    if (d > 0) {
        i = 2;
        b = c;
        ++b;
    } else {
        i = 3;
        a = foo(b);
    }
    b = i;
    return a + b;
}

int main()
{
    return tx();
}
