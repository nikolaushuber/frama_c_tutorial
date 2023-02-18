/*@
    requires n >= 0;
    requires \valid_read(a + (0 .. n-1));
    requires \valid_read(b + (0 .. n-1));

    assigns \nothing;
*/
int array_equals(int* a, int* b, int n);
