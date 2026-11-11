/* The C library declarations curl's headers need to compile the target's seven source files for a
   freestanding i386 image. Not an upstream file. Every hosted header curl includes
   (the other files of this directory) is this one. Only `memchr` and `strncmp` (../libc.c) and
   the runtime's `memcpy`/`memset` are called by code in the image. */
#ifndef SUITE_LIBC_H
#define SUITE_LIBC_H
#include <stdarg.h>
#include <stddef.h>
#include <stdint.h>
#include <limits.h>

typedef int32_t ssize_t;
typedef int64_t off_t;
typedef int64_t time_t;
typedef int32_t pid_t;
typedef uint32_t socklen_t;
typedef uint16_t sa_family_t;
typedef uint16_t in_port_t;
typedef uint32_t in_addr_t;
typedef struct FILE FILE;
typedef int sig_atomic_t;

struct timeval { time_t tv_sec; int32_t tv_usec; };
struct tm { int tm_sec, tm_min, tm_hour, tm_mday, tm_mon, tm_year, tm_wday, tm_yday, tm_isdst; };
struct stat { off_t st_size; time_t st_mtime; unsigned st_mode; };

#define AF_UNSPEC 0
#define AF_INET 2
#define AF_INET6 10
#define PF_INET AF_INET
#define PF_INET6 AF_INET6
#define SOCK_STREAM 1
#define SOCK_DGRAM 2
#define IPPROTO_TCP 6
#define IPPROTO_UDP 17
#define INET_ADDRSTRLEN 16
#define INET6_ADDRSTRLEN 46
struct in_addr { in_addr_t s_addr; };
struct in6_addr { uint8_t s6_addr[16]; };
struct sockaddr { sa_family_t sa_family; char sa_data[14]; };
struct sockaddr_in { sa_family_t sin_family; in_port_t sin_port; struct in_addr sin_addr; uint8_t sin_zero[8]; };
struct sockaddr_in6 { sa_family_t sin6_family; in_port_t sin6_port; uint32_t sin6_flowinfo;
                      struct in6_addr sin6_addr; uint32_t sin6_scope_id; };
struct sockaddr_storage { sa_family_t ss_family; char ss_data[126]; };

extern int errno;
#define EINTR 4
#define EAGAIN 11
#define ENOMEM 12
#define EACCES 13
#define EEXIST 17
#define EINVAL 22
#define ERANGE 34
#define ENOSPC 28
#define EAFNOSUPPORT 97
#define EWOULDBLOCK EAGAIN
#define EINPROGRESS 115

void *memcpy(void *, const void *, size_t);
void *memmove(void *, const void *, size_t);
void *memset(void *, int, size_t);
int memcmp(const void *, const void *, size_t);
void *memchr(const void *, int, size_t);
size_t strlen(const char *);
int strcmp(const char *, const char *);
int strncmp(const char *, const char *, size_t);
char *strchr(const char *, int);
char *strrchr(const char *, int);
char *strstr(const char *, const char *);
char *strdup(const char *);
char *strerror(int);
size_t strcspn(const char *, const char *);
typedef struct { uint32_t fds_bits[32]; } fd_set;
int socket(int, int, int);
int close(int);
ssize_t recv(int, void *, size_t, int);
ssize_t send(int, const void *, size_t, int);
uint16_t htons(uint16_t);
uint16_t ntohs(uint16_t);
uint32_t htonl(uint32_t);
uint32_t ntohl(uint32_t);
void *malloc(size_t);
void *calloc(size_t, size_t);
void *realloc(void *, size_t);
void free(void *);
#endif
