//producer
do{
    wait(empty);
    wait(mutex);
    buffer[in] = item;
    in = (in + 1) % BUFFER_SIZE;
    signal(mutex);
    signal(full);
}while(true);
//comsumer
do{
    wait(full)
    wait(mutex);
    item = buffer[out];
    out = (out + 1) % BUFFER_SIZE;
    signal(mutex);
    signal(empty);
}while(true);