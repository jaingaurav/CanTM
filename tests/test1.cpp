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

int stm_load( uintptr_t addr)
{
  printf ("Loading value stored at: ");
  printf ("%016"PRIxPTR" ", addr);
  printf("currently has value: %d", *(int*)addr);
  return *(int*)addr;
}

void stm_store(int val, uintptr_t addr)
{
    printf ("Storing value stored at: ");
    printf ("%016"PRIxPTR" ", addr);
    printf("with new value: %d", val);
    *(int *)addr = val;
}

int a, b, c, d;

int foo(int& b)
{
    return b+1;
}

#if 0

int* foo2(int& b)
{
    return &b;
}

int* foo3(int& b)
{
    int s = b;
    return &s;
}

int* foo4(int& b)
{
    int* s = new int();
    *s = b;
    return s;
}

int foo5(int& b, int* c)
{
    int s;
    c = &s;
    int t;
    t=s;
    return b+1;
}

int foo6(int b)
{
    return b+1;
}

int foo7(int& b)
{
    int retVal = 0;
    int* s = new int();
    *s = b;
    retVal = *s;
    delete s;
    return retVal;
}

int tx()
{
    int *j;
    if (a > b)
    j = &a;
    else
    j= &b;
    *j = 2;
    if (c > d)
    j = &c;
    else
    j= &d;
    int i = a;
    *j = 3;
    a = 2;
    a = i;
    d = -2;
    if (d > 0) {
        i = 2;
        b = c;
        ++b;
    } else {
        i = 3;
        foo6(b);
        a = foo(b);
    }
    b = i;
    return a + b;
}
#else

int tx()
{
    a = 2;
    d = 2;
    int *j;
    if (b > c)
        j = &a;
    else
        j = &d;

    *j = 2;
    if (d > 0) {
        b = c;
        ++b;
    } else {
        a = foo(b);
    }
    return a + b;
}
#endif

int main()
{
    return tx();
}
