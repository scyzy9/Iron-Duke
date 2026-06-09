#include <sys/types.h>
#include <unistd.h>
#include <stdio.h>
#include <stdlib.h>
#DEFINE number 4

int main(){
    for(int i = 0; i < number; i++){
        pid_t pid = fork();
        if(pid = 0){
            printf("Hello from the child %d with pid %d\n",i,getpid());
            exit(0);
        }
    }
    

}