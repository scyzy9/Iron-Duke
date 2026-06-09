#include <stdio.h>
#include <stdlib.h>
#include <pthread.h>
#include <semaphore.h>
#include <unistd.h>

#DEFINE BUFFER_SIZE 100
#DEFINE PRODUCE_COUNT 20

int buffer[BUFFER_SIZE];
int in = 0, out = 0;

sem_t items;
sem_t mutex;

void* producer(void * arg)
{
    for(int i = 0; i < PRODUCE_COUNT; i++)
    {
        int item = i + 1;

        sem_wait(&mutex);

        buffer[in] = item;
        in = (in + 1) % BUFFER_SIZE;
        printf("Producer produced item %d\n",item);

        sem_post(&mutex);

        sem_post(&items);
        usleep(rand()% 200000);
    }
    return NULL;
}

void* consumer(void * arg)
{
    for(int i = 0; i < PRODUCE_COUNT; i++)
    {
        sem_wait(&items);

        sem_wait(&mutex);

        int item = buffer[out];
        out = (out + 1) % BUFFER_SIZE;
        printf("Consumer consume item %d.\n",item);

        sem_post(&mutex);

        usleep(rand() % 300000)
    }
    return NULL;
}

int main()
{
    pthread_t prod, cons;

    sem_init(&items, 0, 0);
    sem_init(&mutex, 0, 1);

    pthread_create(&prod, NULL, producer, NULL);
    pthread_create(&cons, NULL, consumer, NULL );

    pthread_join(prod, NULL);
    pthread_join(cons, NULL);

    sem_destroy(&items);
    sem_destroy(&mutex);

    printf("All items produced and consumed successfully.\n");
    return 0;
}
