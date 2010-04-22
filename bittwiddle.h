#ifndef _BITTWIDDLE_H
#define _BITTWIDDLE_H

#include <stdint.h>
#include <closure.h>
#include <sys/types.h>
#include <sys/socket.h>
#include <netinet/in.h>
#include <arpa/inet.h>
#include <unistd.h>
#include <fcntl.h>
#include <errno.h>

// Use pointers to an int, because an Idris Int is only 31 bits!
// void* is just what Idris wants.
typedef void* INT32;

// FIXME: not always, but it is on this machine...
typedef uint32_t word32;

// Create a new Int32 with the given value
INT32 mkInt32(word32 v);

// Convert an Int32 to a normal Int
word32 getInt(INT32 v);

// Take the most significant bits from startbit to endbit inclusive, and
// return a new int32
INT32 getBits(INT32 num, word32 startbit, word32 endbit);

// Set the most signifcant bits from startbit to endbit inclusive, with
// the value 'newval', and return a new int32.
INT32 setBits(INT32 num, word32 startbit, word32 endbit, word32 newval);

///////// Packet data

typedef word32* PACKET;

PACKET newPacket(int length);
void dumpPacket(PACKET p, int length);

void setPacketByte(PACKET p, int b, int data);
void setPacketBits(PACKET p, int start, int end, int data);

void setPacketString(PACKET p, int start, char* string);

int getPacketByte(PACKET p, int b);
int getPacketBits(PACKET p, int start, int end);

//// Code for sending packets across a wire

// Anything waiting on a socket?
int isReadable(int sd, int timeOut);

typedef struct {
    int sock;
    struct sockaddr_in addr;
} Connection;

typedef struct {
    VAL buf;
    unsigned port;
    char* server;
} Recv;

// Open sockets
void* net_UDP_serverSocket(int port);
void* net_UDP_clientSocket(char* server, int port);
void* net_TCP_socket(char* server, int port);
void* net_TCP_listen(int port, int maxcon);
void* net_TCP_accept(void* s_in);
void  net_closeSocket(void* s);

int net_sendUDP(void* conn, char* server, int port, VAL stuff);
void* net_recvUDP(void* conn);

int net_sendTCP(void* conn, VAL stuff);
void* net_recvTCP(void* conn);

VAL get_recvPacket(void* recv);
char* get_recvServer(void* recv);
int get_recvPort(void* recv);

int nullPtr(void *ptr);

#endif
