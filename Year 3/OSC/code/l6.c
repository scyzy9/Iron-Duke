#include <stdio.h>
#include <stdlib.h>
#define BUFFER_LENGTH 5
void set(int *value, int const i){
    *value = i * i;
}

int main()
{
    int *const buffer = malloc(BUFFER_LENGTH * sizeof(int));
    if (!buffer){
        abort();
    }
    for(int i = 0; i < BUFFER_LENGTH; ++i)
    {
        set(value + i, i);
    }
    for(int i = 0; i < BUFFER_LENGTH; ++i)
    {
        printf("buffer[%d] = %d",i, buffer[i]);
    }
}