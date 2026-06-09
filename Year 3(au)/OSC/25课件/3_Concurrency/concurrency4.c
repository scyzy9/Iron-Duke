//producer
void * producer(void * a)
{
    while(1)
    {
        sem_wait(&empty);
        sem_wait(&sync);
        items++;
        printf("Producer: %d\n",items);
        sem_post(&sync);
        sem_post(&full);
    }
}
//comsumer
void consumer(void * a )
{
    sem_wait(&full);
    sem_wait(&sync);
    items--;
    printf("Consumer: %d\n",items);
    sem_post(&sync);
    sem_post(&empty);
}