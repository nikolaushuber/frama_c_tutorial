#include <limits.h>

/*@
    requires INT_MIN <= (x+y) <= INT_MAX;
    ensures \result == x + y;
*/
int add(int x, int y) 
{
    return x + y;
}

int v;

void main(void)
{
    v = 10;
    int r = add(3,4);
    //@ assert r == 7;
    //@ assert v == 10;
}
