int iReadCount = 0;
pthread_mutex_t sync;
sem_t rwSync;

void * reader(void * arg)
{
    while(1)
    {
        pthread_mutex_lock(&sync);

        iReadCount++;
        if(iReadCount == 1)
        {
            sem_wait(&rwSync);
        }

        pthread_mutex_unlock(&sync);

        printf("reading record\n");

        pthread_mutex_lock(&sync);
        iReadCount--;
        if(iReadCount == 0)
        {
            sem_post(&rwSync);
        }
        pthread_mutex_unlock(&sync);
    }
}

void * writer(void * writer)
{
    while(1)
    {
        sem_wait(&rwSync);
        printf("writing\n");
        sem_post(&rwSync);
    }
}