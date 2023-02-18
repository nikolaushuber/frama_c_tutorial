/*@
    requires 0 <= length;
    requires \valid(arr + (0 .. length-1));
    assigns arr[0 .. length-1];
    ensures \forall int i; 0 <= i < length ==> arr[i] == 0;
*/
void clear_array(int* arr, int length)
{
    /*@
        loop invariant 0 <= i <= length;
        loop invariant \forall int j; 0 <= j < i ==> arr[j] == 0;
        loop assigns i, arr[0 .. length-1];
    */
    for(int i = 0; i < length; i++)
    {
        arr[i] = 0;
    }
}
