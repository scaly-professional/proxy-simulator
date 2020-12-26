/**
 * @file proxy.c
 * @brief A proxy server implementation that acts as an intermediary between
 * clients. The proxy acts like a web proxy and takes in HTTP GET requests and
 * checks if the appropriate response is already in the global cache. If not,
 * then sends the request to the server, which writes back and also stores the
 * repsonse in the global cache for possible future requests
 *
 * Cache Implementation: Queue as a LinkedList
 * The global cache acts liks a direct mapped cache is just a linked list of
 * lines/objects. Since the cache acts like a queue, the struct has a pointer to
 * the front of the queue and the end of the queue for enqueues and dequeues, as
 * well as an int sizeLeft field that describes how much space of the remaining
 * MAX_CACHE_SIZE is left. The objects in the queue contain the uri as a key and
 * the data. There is also a pointer to the next object in the queue, as well as
 * the size of the object so we can decrement and increment the space available
 * inside the actual cache based on enqueues and dequeues.
 *
 * @author Eric Gan <ehgan>
 */
#include "csapp.h"
#include "http_parser.h"
#include <assert.h>
#include <ctype.h>
#include <inttypes.h>
#include <stdbool.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <strings.h>
#include <unistd.h>

#include <errno.h>
#include <netdb.h>
#include <netinet/in.h>
#include <pthread.h>
#include <signal.h>
#include <sys/socket.h>
#include <sys/types.h>

/*
 * Debug macros, which can be enabled by adding -DDEBUG in the Makefile
 * Use these if you find them useful, or delete them if not
 */
#ifdef DEBUG
#define dbg_assert(...) assert(__VA_ARGS__)
#define dbg_printf(...) fprintf(stderr, __VA_ARGS__)
#else
#define dbg_assert(...)
#define dbg_printf(...)
#endif

/*
 * Max cache and object sizes
 * You might want to move these to the file containing your cache implementation
 */
#define MAX_CACHE_SIZE (1024 * 1024)
#define MAX_OBJECT_SIZE (100 * 1024)

#define HOSTLEN 256
#define SERVLEN 8

/* Typedef for convenience */
typedef struct sockaddr SA;

/* Information about a connected client. */
typedef struct {
    struct sockaddr_in addr; // Socket address
    socklen_t addrlen;       // Socket address length
    int connfd;              // Client connection file descriptor
    char host[HOSTLEN];      // Client host
    char serv[SERVLEN];      // Client service (port)
} client_info;

/* Line struct in direct-mapped cache (Queue implementation) */
typedef struct line_header {
    int size;
    char *uri;
    char *data;
    struct line_header *next;
} Line;

/* Cache stuct (Queue implementation) */
typedef struct cache_header {
    int sizeLeft;
    Line *front;
    Line *end;
} Cache;

/* Global cache and global locking mutex */
Cache *cache;
pthread_mutex_t mutex;

/**
 * @brief Creating new line of data with the uri as the key
 * @param[in] uri
 * @param[in] data
 * @param[in] size
 * @return The line with the input arguments put into the struct fields
 */
Line *newLine(const char *uri, char *data, int size) {
    Line *line = (Line *)Malloc(sizeof(Line));
    line->size = size;
    char *newUri = Malloc(strlen(uri) + 1);
    strcpy(newUri, uri);
    line->uri = newUri;
    char *newData = Malloc(size);
    memcpy(newData, data, size);
    line->data = newData;
    line->next = NULL;
    return line;
}

/**
 * @brief Creating empty cache
 * @return empty cache
 */
Cache *createCache(void) {
    Cache *cache = (Cache *)Malloc(sizeof(Cache));
    cache->sizeLeft = MAX_CACHE_SIZE;
    cache->front = NULL;
    cache->end = NULL;
    return cache;
}

/**
 * @brief Dequeue from cache queue
 * @param[in] cache
 */
void deq(Cache *cache) {
    /* If cache is already empty, do nothing */
    if (cache->front == NULL)
        return;
    Line *temp = cache->front;
    /* Adjust pointers at the front */
    cache->front = cache->front->next;
    if (cache->front == NULL)
        cache->end = NULL;
    cache->sizeLeft = cache->sizeLeft + temp->size;
    /* Free the dequeued line */
    Free(temp->data);
    Free(temp->uri);
    Free(temp);
}

/**
 * @brief Enqueue element/line onto the cache queue
 * @param[in] cache
 * @param[in] line
 */
void enq(Cache *cache, Line *line) {
    /* Evict LRU from cache until enough space in cache to fit object */
    while (cache->sizeLeft - line->size < 0) {
        deq(cache);
    }
    /* If queue is empty, enqueue element in as the only element */
    if (cache->front == NULL) {
        cache->front = line;
        cache->end = cache->front;
        cache->sizeLeft = cache->sizeLeft - line->size;
    } else {
        /* If queue is not empty, enqueue element at end and adjust end pointer
         */
        cache->end->next = line;
        cache->end = line;
        cache->sizeLeft = cache->sizeLeft - line->size;
    }
}

/**
 * @brief Remove a certain line with key uri from the queue and returns it or
 * returns NULL if miss
 * @param[in] cache
 * @param[in] uri
 * @return removed line and NULL if not in cache (miss)
 */
Line *retrieveLine(Cache *cache, const char *uri) {
    Line *iterator = cache->front;
    Line *prev = iterator;
    if (iterator != NULL && strlen(iterator->uri) == strlen(uri) &&
        strcmp(iterator->uri, uri) == 0) {
        cache->front = cache->front->next;
        cache->sizeLeft = cache->sizeLeft + iterator->size;
        iterator->next = NULL;
        return iterator;
    }
    while (iterator != NULL) {
        if (strlen(iterator->uri) == strlen(uri) &&
            strcmp(iterator->uri, uri) == 0) {
            break;
        }
        prev = iterator;
        iterator = iterator->next;
    }
    if (iterator == NULL) {
        return NULL;
    }
    prev->next = iterator->next;
    iterator->next = NULL;
    cache->sizeLeft = cache->sizeLeft + iterator->size;
    return iterator;
}

/**
 * @brief Checks if object with key uri is in cache
 * @param[in] cache
 * @param[in] uri
 * @return true if object is in cache, false otherwise
 */
bool in_Cache(Cache *cache, const char *uri) {
    Line *iterator = cache->front;
    while (iterator != NULL) {
        if (strlen(iterator->uri) == strlen(uri) &&
            strcmp(iterator->uri, uri) == 0) {
            return true;
        }
        iterator = iterator->next;
    }
    return false;
}

/*
 * String to use for the User-Agent header.
 * Don't forget to terminate with \r\n
 */
static const char *header_user_agent = "Mozilla/5.0"
                                       " (X11; Linux x86_64; rv:3.10.0)"
                                       " Gecko/20201123 Firefox/63.0.1";

/*
 * String to use for the Connection header.
 * Don't forget to terminate with \r\n
 */
static const char *header_connection = "close";

/*
 * String to use for the Proxy-Connection header.
 * Don't forget to terminate with \r\n
 */
static const char *header_proxy_connection = "close";

/*
 * clienterror - returns an error message to the client (taken from tiny.c)
 */
void clienterror(int fd, const char *errnum, const char *shortmsg,
                 const char *longmsg) {
    char buf[MAXLINE];
    char body[MAXBUF];
    size_t buflen;
    size_t bodylen;

    /* Build the HTTP response body */
    bodylen = snprintf(body, MAXBUF,
                       "<!DOCTYPE html>\r\n"
                       "<html>\r\n"
                       "<head><title>Tiny Error</title></head>\r\n"
                       "<body bgcolor=\"ffffff\">\r\n"
                       "<h1>%s: %s</h1>\r\n"
                       "<p>%s</p>\r\n"
                       "<hr /><em>The Tiny Web server</em>\r\n"
                       "</body></html>\r\n",
                       errnum, shortmsg, longmsg);
    if (bodylen >= MAXBUF) {
        return; // Overflow!
    }

    /* Build the HTTP response headers */
    buflen = snprintf(buf, MAXLINE,
                      "HTTP/1.0 %s %s\r\n"
                      "Content-Type: text/html\r\n"
                      "Content-Length: %zu\r\n\r\n",
                      errnum, shortmsg, bodylen);
    if (buflen >= MAXLINE) {
        return; // Overflow!
    }

    /* Write the headers */
    if (rio_writen(fd, buf, buflen) < 0) {
        fprintf(stderr, "Error writing error response headers to client\n");
        return;
    }

    /* Write the body */
    if (rio_writen(fd, body, bodylen) < 0) {
        fprintf(stderr, "Error writing error response body to client\n");
        return;
    }
}

/**
 * @brief Send request line to the server fd
 * @param[in] fd
 * @param[in] method
 * @param[in] path
 */
void forward_request_line(int fd, const char *method, const char *path) {
    char result[MAXLINE];
    strcpy(result, method);
    strcat(result, " ");
    strcat(result, path);
    strcat(result, " HTTP/1.0\r\n");
    int test = rio_writen(fd, result, strlen(result));
    if (test < 0) {
        fprintf(stderr, "Error forwarding request line\n");
        return;
    }
}

/**
 * @brief Send header to the server fd
 * @param[in] fd
 * @param[in] name
 * @param[in] value
 */
void forward_header(int fd, const char *name, const char *value) {
    char result[MAXLINE];
    strcpy(result, name);
    strcat(result, ": ");
    strcat(result, value);
    strcat(result, "\r\n");
    int test = rio_writen(fd, result, strlen(result));
    if (test < 0) {
        fprintf(stderr, "Error forwarding header\n");
        return;
    }
}

/*
 * read_requesthdrs - read HTTP request headers
 * Returns true if an error occurred, or false otherwise.
 * (taken from tiny.c)
 */
bool read_requesthdrs(int connfd, rio_t *rp, int fd, bool *host_header) {
    char buf[MAXLINE];
    char name[MAXLINE];
    char value[MAXLINE];

    while (true) {
        if (rio_readlineb(rp, buf, sizeof(buf)) <= 0) {
            return true;
        }

        /* Check for end of request headers */
        if (strcmp(buf, "\r\n") == 0) {
            return false;
        }

        /* Parse header into name and value */
        if (sscanf(buf, "%[^:]: %[^\r\n]", name, value) != 2) {
            /* Error parsing header */
            clienterror(connfd, "400", "Bad Request",
                        "Proxy could not parse request headers");
            return true;
        }

        if (strcmp(name, "Host") == 0) {
            *host_header = true;
        }
        if (strcmp(name, "User-Agent") != 0 &&
            strcmp(name, "Connection") != 0 &&
            strcmp(name, "Proxy-Connection") != 0) {
            forward_header(fd, name, value);
        }
    }
}

/**
 * @brief Read from server srcfd and write back to client destfd, and store in
 * cache with key uri
 * @param[in] srcfd
 * @param[in] destfd
 * @param[in] uri
 */
void server_to_client(int srcfd, int destfd, const char *uri) {
    rio_t rp;
    int msglength;
    int total_length = 0;
    char total_data[MAX_OBJECT_SIZE];
    char buf[MAXLINE];
    rio_readinitb(&rp, srcfd);
    /* Read from the srcfd */
    while ((msglength = rio_readnb(&rp, buf, MAXLINE)) > 0) {
        /* If the newly read data still fits within max cache object, then
         * concatenate to total_data */
        if (total_length + msglength <= MAX_OBJECT_SIZE) {
            memcpy(total_data + total_length, buf, msglength);
        }
        /* Increment total_length of the data */
        total_length = total_length + msglength;
        /* write to the destfd */
        int test = rio_writen(destfd, buf, msglength);
        if (test < 0) {
            fprintf(stderr, "Error writing from src to dest\n");
            return;
        }
    }
    /* If total data is within object size constraints */
    pthread_mutex_lock(&mutex);
    if (total_length <= MAX_OBJECT_SIZE) {
        /* Add the object into the cache */
        if (!in_Cache(cache, uri)) {
            Line *new_entry = newLine(uri, total_data, total_length);
            enq(cache, new_entry);
        }
    }
    pthread_mutex_unlock(&mutex);
}

/**
 * @brief Send request to server and get response to write back to client connfd
 * @param[in] connfd
 */
void parse_request(int connfd) {
    rio_t rp;
    bool use_cache = false;
    char cache_data[MAX_OBJECT_SIZE];
    int cache_size;
    char buf[MAXLINE];
    parser_t *parse = parser_new();
    rio_readinitb(&rp, connfd);
    if (rio_readlineb(&rp, buf, sizeof(buf)) <= 0) {
        fprintf(stderr, "Error reading line\n");
        return;
    }
    /* Parsing line and putting into buf */
    parser_state state = parser_parse_line(parse, buf);
    if (state == ERROR) {
        clienterror(connfd, "400", "Bad Request",
                    "Proxy could not parse the request URI");
        return;
    }
    if (state != REQUEST) {
        fprintf(stderr, "First line is not request line\n");
        return;
    }
    /* Retrieving host, path, method, port, and uri for future use */
    const char *host;
    const char *path;
    const char *method;
    const char *port;
    const char *uri;
    if (parser_retrieve(parse, HOST, &host) < 0) {
        fprintf(stderr, "Error retrieving host\n");
        return;
    }
    if (parser_retrieve(parse, PATH, &path) < 0) {
        fprintf(stderr, "Error retrieving path\n");
        return;
    }
    if (parser_retrieve(parse, METHOD, &method) < 0) {
        fprintf(stderr, "Error retrieving method\n");
        return;
    }
    if (parser_retrieve(parse, PORT, &port) < 0) {
        fprintf(stderr, "Error retrieving port\n");
        return;
    }
    if (parser_retrieve(parse, URI, &uri) < 0) {
        fprintf(stderr, "Error retrieving uri\n");
        return;
    }
    if (strcmp(method, "GET") != 0) {
        clienterror(connfd, "501", "Not Implemented",
                    "Proxy does not implement this method");
        return;
    }
    /* If uri is already key in cache, just retrieve data from cache and write
     * to client */
    pthread_mutex_lock(&mutex);
    Line *hit_or_miss = retrieveLine(cache, uri);
    if (hit_or_miss != NULL) {
        use_cache = true;
        enq(cache, hit_or_miss);
        cache_size = hit_or_miss->size;
        memcpy(cache_data, hit_or_miss->data, cache_size);
    }
    pthread_mutex_unlock(&mutex);

    if (use_cache) {
        int test = rio_writen(connfd, cache_data, cache_size);
        if (test < 0) {
            fprintf(stderr, "Error writing from cache to dest\n");
            return;
        }
    } else {
        /* Otherwise, send request to server */
        int clientfd = open_clientfd(host, port);
        if (clientfd < 0) {
            fprintf(stderr, "Failed to create fd for client: %s: %s\n", host,
                    port);
            return;
        }
        forward_request_line(clientfd, method, path);
        bool host_header = false;
        if (read_requesthdrs(connfd, &rp, clientfd, &host_header)) {
            fprintf(stderr, "Problem reading headers\n");
            return;
        }
        if (!host_header) {
            forward_header(clientfd, "Host", host);
        }
        forward_header(clientfd, "User-Agent", header_user_agent);
        forward_header(clientfd, "Connection", header_connection);
        forward_header(clientfd, "Proxy-Connection", header_proxy_connection);
        int test = rio_writen(clientfd, "\r\n", 2);
        if (test < 0) {
            fprintf(stderr, "Error forwarding carriage return\n");
            return;
        }
        server_to_client(clientfd, connfd, uri);
        close(clientfd);
    }
    parser_free(parse);
}

/* Runs request parsing on a thread and terminates when done */
void *thread(void *vargp) {
    int connfd = *((int *)vargp);
    pthread_detach(pthread_self());
    Free(vargp);
    parse_request(connfd);
    close(connfd);
    return NULL;
}

int main(int argc, char **argv) {
    pthread_mutex_init(&mutex, NULL);
    int listenfd;
    pthread_t tid;
    cache = createCache();

    /* Handle SIGPIPE Signal */
    Signal(SIGPIPE, SIG_IGN);

    /* Check command line args */
    if (argc != 2) {
        fprintf(stderr, "usage: %s <port>\n", argv[0]);
        exit(1);
    }

    listenfd = open_listenfd(argv[1]);
    if (listenfd < 0) {
        fprintf(stderr, "Failed to listen on port: %s\n", argv[1]);
        exit(1);
    }

    while (1) {
        /* Allocate space on the stack for client info */
        client_info client_data;
        client_info *client = &client_data;
        int *connfdp;
        connfdp = Malloc(sizeof(int));

        /* Initialize the length of the address */
        client->addrlen = sizeof(client->addr);

        /* accept() will block until a client connects to the port */
        *connfdp = accept(listenfd, (SA *)&client->addr, &client->addrlen);
        if (*connfdp < 0) {
            perror("accept");
            continue;
        }
        pthread_create(&tid, NULL, thread, connfdp);
    }
    return 0;
}
