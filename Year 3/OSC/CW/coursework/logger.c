// Student: ZhenYe ID: 20616296

#include "logger.h"
#include "utilities.h"

#include <pthread.h>
#include <stdio.h>
#include <time.h>

pthread_mutex_t logger_mutex;
unsigned long long message_counter = 0;

static int logger_enabled = 0;
static int debug_enabled = 0;
static int priority_enabled = 0;

void logger_start(int logger_stream, int debug_stream, int priority_stream) {
    pthread_mutex_init(&logger_mutex, NULL);
    
    logger_enabled = logger_stream;
    debug_enabled = debug_stream;
    priority_enabled = priority_stream;
    
    message_counter = 0;
}

void logger_stop() {
    pthread_mutex_destroy(&logger_mutex);
}

static void write_message(const char* type, const char* message) {
    time_t now;
    struct tm* timeinfo;
    char time_buffer[32];
    unsigned long long msg_num;
    
    pthread_mutex_lock(&logger_mutex);
    
    msg_num = message_counter++;
    
    time(&now);
    timeinfo = localtime(&now);
    strftime(time_buffer, sizeof(time_buffer), "%H:%M:%S", timeinfo);
    
    printf("%llu : %s : [%s] %s\n", msg_num, time_buffer, type, message);
    
    pthread_mutex_unlock(&logger_mutex);
}

void logger_write(char const* message) {
    if (logger_enabled) {
        write_message("Log", message);
    }
}

void debug_write(char const* message) {
    if (debug_enabled) {
        write_message("Debug", message);
    }
}

void priority_write(char const* message) {
    if (priority_enabled) {
        write_message("Priority", message);
    }
}