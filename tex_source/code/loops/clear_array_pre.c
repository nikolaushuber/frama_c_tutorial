/*@
    requires 0 <= length;
    requires \valid(arr + (0 .. length-1));
    assigns arr[0 .. length-1];
*/
void clear_array(int* arr, int length)
{
    for(int i = 0; i < length; i++)
    {
        arr[i] = 0;
    }
}
