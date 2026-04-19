typedef struct{
    int count;
    struct process * list;
}semaphore;

void wait(semaphore *S){
    S -> count --;
    if(S -> count < 0){
        block();
    }
}

void post(semaphore *S){
    S -> count ++;
    if(S -> count <= 0){
        wakeup(P);
    }
}