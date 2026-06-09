void * consumer(void *p)
{
    sem_wait(&delay_consumer);
    while(1)
    {
        sem_wait(&sync);
        items--;
        printf("%d\n",items);
        if(items == 0)
        {
            sem_wait(&delay_consumer);
        }
        sem_post(&sync);
    }
}

void * producer(void * p)
{
    while(1)
    {
        sem_wait(&sync);
        items++;
        printf("%d\n",items);
        if(items == 1)
        {
            sem_post(&delay_consumer);
        }
        sem_post(&sync);
    }
}