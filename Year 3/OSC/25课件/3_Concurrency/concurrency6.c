void * reader(void * arg)
{
    while(1)
    {
        sem_wait(&sReadTry);
        sem_wait(&sRead);
        iReadCount++;
        if(iReadCount == `)
        {
            sem_wait(&sResource);
        }
        sem_post(&sRead);
        sem_post(&sReadTry);

        printf("reading\n");

        sem_wait(&sRead);
        iReadCount--;
        if(iReadCount == 0)
        {
            sem_post(sResource);
        }
        sem_post(&sRead);
    }
}

void * writer(void * arg)
{
    while(1)
    {
        sem_wait(&sWrite)
        {
            iWriteCount++;
            if(iWriteCount == 1)
            {
                sem_wait(&sReadTry);
            }
            sem_post(&sWrite);
            sem_wait(&sResource);
            printf("Writing\n");
            sem_post(&sResource);
            sem_wait(&sWrite);
            iWriteCount--;
            if(iWriteCount == 0)
            {
                sem_post(&sReadTry);
            }
            sem_post(&sWrite);
        }
    }
}