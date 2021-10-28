#include <stdio.h>
#include <unistd.h>
#include <fcntl.h>
int main(void){
    open("file",O_RDONLY);
    return 0;
}