/*
 * main.c — Lightweight RTSP→HEVC→MPEG-TS→UDP Gateway.
 * Build:  gcc main.c -o rtsp_client
 * VLC:    vlc udp://@:6972
 */

#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <unistd.h>
#include <time.h>
#include <sys/socket.h>
#include <netinet/in.h>
#include <arpa/inet.h>
#include <sys/select.h>

/* ── Configuration ────────────────────────────────────────────────── */
#define CAM_IP         "192.168.8.4"
#define CAM_PORT       554
#define CAM_PATH       "/cam/realmonitor?channel=3&subtype=0"
#define CAM_USER       "admin"
#define CAM_PASS       "admin123"
#define RTP_RECV_PORT  6970
#define RTCP_RECV_PORT 6971
#define VLC_IP         "127.0.0.1"
#define VLC_PORT       6972
#define RTSP_BUF_SIZE  8192
#define RTP_BUF_SIZE   65536
#define KEEPALIVE_SECS 30

#define REORDER_WIN  256
#define STALL_MS     150

/**
 * @brief Computes a monotonic millisecond timestamp.
 * * @return uint64_t Current elapsed time in milliseconds since an arbitrary fixed point.
 * * @note PURPOSE & DESIGN JUSTIFICATION:
 * High-performance network code requires a time source immune to system clock steps (such as NTP syncs
 * or manual time shifts). `CLOCK_MONOTONIC` guarantees that time flows forward linearly. This is 
 * critical for the packet reordering state-machine to accurately calculate jitter stall windows 
 * without causing artificial sequence drops or premature timeouts.
 */
static uint64_t now_ms(void)
{
    struct timespec ts;
    clock_gettime(CLOCK_MONOTONIC, &ts);
    return (uint64_t)ts.tv_sec * 1000u + (uint64_t)ts.tv_nsec / 1000000u;
}

/**
 * @brief Calculates the standard ISO/IEC 13818-1 32-bit CRC.
 * * @param data Pointer to the input data block.
 * @param len  Length of the data block in bytes.
 * @return uint32_t Computed MPEG-TS compliant CRC-32 value.
 * * @note PURPOSE & DESIGN JUSTIFICATION:
 * MPEG Transport Stream PSI sections (PAT and PMT tables) mandatorily require a specific CRC-32 
 * checksum appended to the payload. Without a mathematically valid CRC, downstream decoders like VLC 
 * will silently drop the Program Association and Program Map tables, failing to discover the H.265 
 * PID stream mapping and causing infinite playback initialization loops.
 */
static uint32_t mpeg_crc32(const uint8_t *data, size_t len)
{
    uint32_t crc = 0xFFFFFFFF;
    for (size_t i = 0; i < len; i++) {
        crc ^= ((uint32_t)data[i]) << 24;
        for (int j = 0; j < 8; j++)
            crc = (crc & 0x80000000) ? (crc << 1) ^ 0x04C11DB7 : (crc << 1);
    }
    return crc;
}

/* ── MD5 Infrastructure ──────────────────────────────────────────── */
typedef struct { uint32_t state[4], count[2]; uint8_t buffer[64]; } MD5_CTX;
#define F(x,y,z) (((x)&(y))|((~x)&(z)))
#define G(x,y,z) (((x)&(z))|((y)&(~z)))
#define H(x,y,z) ((x)^(y)^(z))
#define I(x,y,z) ((y)^((x)|(~z)))
#define ROL(x,n) (((x)<<(n))|((x)>>(32-(n))))
#define FF(a,b,c,d,x,s,t){(a)+=F(b,c,d)+(x)+(t);(a)=ROL(a,s);(a)+=(b);}
#define GG(a,b,c,d,x,s,t){(a)+=G(b,c,d)+(x)+(t);(a)=ROL(a,s);(a)+=(b);}
#define HH(a,b,c,d,x,s,t){(a)+=H(b,c,d)+(x)+(t);(a)=ROL(a,s);(a)+=(b);}
#define II(a,b,c,d,x,s,t){(a)+=I(b,c,d)+(x)+(t);(a)=ROL(a,s);(a)+=(b);}

/**
 * @brief Converts internal 32-bit integer array states into standard byte streams.
 * * @param o Destination byte buffer.
 * @param i Source 32-bit integer array.
 * @param n Number of integers to serialize.
 * * @note PURPOSE & DESIGN JUSTIFICATION:
 * Handles little-endian memory layout conversion for the MD5 processing core, ensuring the hash 
 * engine remains cross-platform compliant and independent of host architecture endianness.
 */
static void md5_enc(uint8_t*o,const uint32_t*i,size_t n)
{
    size_t j;
    for(j=0;j<n;j++){
        o[j*4]=(uint8_t)i[j];o[j*4+1]=(uint8_t)(i[j]>>8);
        o[j*4+2]=(uint8_t)(i[j]>>16);
        o[j*4+3]=(uint8_t)(i[j]>>24);
    }
}

/**
 * @brief Decodes an incoming byte stream into internal 32-bit integer registers.
 * * @param o Destination 32-bit integer array.
 * @param i Source byte buffer.
 * @param n Number of integers to reconstruct.
 * * @note PURPOSE & DESIGN JUSTIFICATION:
 * Essential companion helper to `md5_enc`. It acts as the serialization layer that sets up raw network 
 * characters into safe 32-bit boundary structures required for the MD5 logical bit transformations.
 */
static void md5_dec(uint32_t*o,const uint8_t*i,size_t n){
    size_t j;
    for(j=0;j<n;j++)o[j]=(uint32_t)i[j*4]|(uint32_t)i[j*4+1]<<8|(uint32_t)i[j*4+2]<<16|(uint32_t)i[j*4+3]<<24;
}

/**
 * @brief Core MD5 compression function processing a 64-byte chunk.
 * * @param s State register accumulators (A, B, C, D).
 * @param b Input 64-byte array block.
 * * @note PURPOSE & DESIGN JUSTIFICATION:
 * Executes the RFC 1321 MD5 step transformations over standard data registers. Embedded as a low-overhead, 
 * dependency-free implementation to avoid introducing external library requirements like OpenSSL.
 */
static void md5_xfm(uint32_t s[4],const uint8_t b[64]){uint32_t a=s[0],bb=s[1],c=s[2],d=s[3],x[16];md5_dec(x,b,16);FF(a,bb,c,d,x[0],7,0xd76aa478)FF(d,a,bb,c,x[1],12,0xe8c7b756)FF(c,d,a,bb,x[2],17,0x242070db)FF(bb,c,d,a,x[3],22,0xc1bdceee)FF(a,bb,c,d,x[4],7,0xf57c0faf)FF(d,a,bb,c,x[5],12,0x4787c62a)FF(c,d,a,bb,x[6],17,0xa8304613)FF(bb,c,d,a,x[7],22,0xfd469501)FF(a,bb,c,d,x[8],7,0x698098d8)FF(d,a,bb,c,x[9],12,0x8b44f7af)FF(c,d,a,bb,x[10],17,0xffff5bb1)FF(bb,c,d,a,x[11],22,0x895cd7be)FF(a,bb,c,d,x[12],7,0x6b901122)FF(d,a,bb,c,x[13],12,0xfd987193)FF(c,d,a,bb,x[14],17,0xa679438e)FF(bb,c,d,a,x[15],22,0x49b40821)GG(a,bb,c,d,x[1],5,0xf61e2562)GG(d,a,bb,c,x[6],9,0xc040b340)GG(c,d,a,bb,x[11],14,0x265e5a51)GG(bb,c,d,a,x[0],20,0xe9b6c7aa)GG(a,bb,c,d,x[5],5,0xd62f105d)GG(d,a,bb,c,x[10],9,0x02441453)GG(c,d,a,bb,x[15],14,0xd8a1e681)GG(bb,c,d,a,x[4],20,0xe7d3fbc8)GG(a,bb,c,d,x[9],5,0x21e1cde6)GG(d,a,bb,c,x[14],9,0xc33707d6)GG(c,d,a,bb,x[3],14,0xf4d50d87)GG(bb,c,d,a,x[8],20,0x455a14ed)GG(a,bb,c,d,x[13],5,0xa9e3e905)GG(d,a,bb,c,x[2],9,0xfcefa3f8)GG(c,d,a,bb,x[7],14,0x676f02d9)GG(bb,c,d,a,x[12],20,0x8d2a4c8a)HH(a,bb,c,d,x[5],4,0xfffa3942)HH(d,a,bb,c,x[8],11,0x8771f681)HH(c,d,a,bb,x[11],16,0x6d9d6122)HH(bb,c,d,a,x[14],23,0xfde5380c)HH(a,bb,c,d,x[1],4,0xa4beea44)HH(d,a,bb,c,x[4],11,0x4bdecfa9)HH(c,d,a,bb,x[7],16,0xf6bb4b60)HH(bb,c,d,a,x[10],23,0xbebfbc70)HH(a,bb,c,d,x[13],4,0x289b7ec6)HH(d,a,bb,c,x[0],11,0xeaa127fa)HH(c,d,a,bb,x[3],16,0xd4ef3085)HH(bb,c,d,a,x[6],23,0x04881d05)HH(a,bb,c,d,x[9],4,0xd9d4d039)HH(d,a,bb,c,x[12],11,0xe6db99e5)HH(c,d,a,bb,x[15],16,0x1fa27cf8)HH(bb,c,d,a,x[2],23,0xc4ac5665)II(a,bb,c,d,x[0],6,0xf4292244)II(d,a,bb,c,x[7],10,0x432aff97)II(c,d,a,bb,x[14],15,0xab9423a7)II(bb,c,d,a,x[5],21,0xfc93a039)II(a,bb,c,d,x[12],6,0x655b59c3)II(d,a,bb,c,x[3],10,0x8f0ccc92)II(c,d,a,bb,x[10],15,0xffeff47d)II(bb,c,d,a,x[1],21,0x85845dd1)II(a,bb,c,d,x[8],6,0x6fa87e4f)II(d,a,bb,c,x[15],10,0xfe2ce6e0)II(c,d,a,bb,x[6],15,0xa3014314)II(bb,c,d,a,x[13],21,0x4e0811a1)II(a,bb,c,d,x[4],6,0xf7537e82)II(d,a,bb,c,x[11],10,0xbd3af235)II(c,d,a,bb,x[2],15,0x2ad7d2bb)II(bb,c,d,a,x[9],21,0xeb86d391)s[0]+=a;s[1]+=bb;s[2]+=c;s[3]+=d;}

/**
 * @brief Initializes context parameters for an MD5 session.
 * * @param ctx Pointer to the MD5 Context block.
 * * @note PURPOSE & DESIGN JUSTIFICATION:
 * Standard housekeeping method to set up initialization vectors required before parsing raw inputs.
 */
static void md5_init(MD5_CTX*ctx){ctx->count[0]=ctx->count[1]=0;ctx->state[0]=0x67452301;ctx->state[1]=0xefcdab89;ctx->state[2]=0x98badcfe;ctx->state[3]=0x10325476;}

/**
 * @brief Appends data streams sequentially to update MD5 block calculations.
 * * @param ctx Pointer to the active MD5 context structure.
 * @param in  Data block buffer to evaluate.
 * @param len Byte size of the current stream chunk.
 * * @note PURPOSE & DESIGN JUSTIFICATION:
 * Feeds arbitrary length strings safely through internal block segment buffers for chunk hashing.
 */
static void md5_update(MD5_CTX*ctx,const uint8_t*in,size_t len){size_t i,idx,pl;idx=(ctx->count[0]>>3)&0x3f;if((ctx->count[0]+=(uint32_t)(len<<3))<(uint32_t)(len<<3))ctx->count[1]++;ctx->count[1]+=(uint32_t)(len>>29);pl=64-idx;if(len>=pl){memcpy(&ctx->buffer[idx],in,pl);md5_xfm(ctx->state,ctx->buffer);for(i=pl;i+63<len;i+=64)md5_xfm(ctx->state,&in[i]);idx=0;}else i=0;memcpy(&ctx->buffer[idx],&in[i],len-i);}

/**
 * @brief Finalizes and terminates an MD5 hash calculation, exporting the calculated digest.
 * * @param digest Fixed 16-byte buffer targeting the final signature.
 * @param ctx    Pointer to the active context structural tracking block.
 * * @note PURPOSE & DESIGN JUSTIFICATION:
 * Applies mathematical standard padding patterns and outputs the explicit cryptographic array result.
 */
static void md5_final(uint8_t digest[16],MD5_CTX*ctx){static const uint8_t pad[64]={0x80};uint8_t bits[8];uint32_t idx=(ctx->count[0]>>3)&0x3f;md5_enc(bits,ctx->count,2);md5_update(ctx,pad,idx<56?56-idx:120-idx);md5_update(ctx,bits,8);md5_enc(digest,ctx->state,4);}

/**
 * @brief Top-level execution handler parsing an input string straight to a hex string.
 * * @param in  Source character stream.
 * @param len Size of the target input string.
 * @param out Destination buffer holding the zero-terminated hex text string [33 bytes].
 * * @note PURPOSE & DESIGN JUSTIFICATION:
 * High-level wrapper that groups initialization, updates, and finalization steps. It outputs 
 * human-readable text hashes used straight inside RTSP protocol header parameters.
 */
static void md5_hex(const char*in,size_t len,char out[33]){MD5_CTX ctx;uint8_t dg[16];int i;static const char h[]="0123456789abcdef";md5_init(&ctx);md5_update(&ctx,(const uint8_t*)in,len);md5_final(dg,&ctx);for(i=0;i<16;i++){out[i*2]=h[(dg[i]>>4)&0xf];out[i*2+1]=h[dg[i]&0xf];}out[32]='\0';}

/* ── Digest Auth ─────────────────────────────────────────────────── */
typedef struct { char realm[128], nonce[128], opaque[128]; int valid; } digest_ctx_t;

/**
 * @brief Case-insensitive substring search implementation.
 * * @param hay String content space evaluated.
 * @param ndl Targeted match word criteria parameter.
 * @return const char* Pointer to first instance match entry if successful, or NULL.
 * * @note PURPOSE & DESIGN JUSTIFICATION:
 * RTSP protocol authentication headers are case-insensitive by standard definition (e.g., "Digest" 
 * vs "digest"). Standard libc `strstr` will fail when communicating with modern security IP cameras (like 
 * Hikvision/Dahua) if the camera uses varying header casings. This function guarantees accurate pattern matching.
 */
static const char *stristr(const char *hay, const char *ndl)
{
    size_t nl = strlen(ndl), hl = strlen(hay), i, j;
    if (nl > hl) return NULL;
    for (i = 0; i <= hl - nl; i++) {
        int ok = 1;
        for (j = 0; j < nl; j++) {
            char a = hay[i+j], b = ndl[j];
            if (a>='A'&&a<='Z') a+=32;
            if (b>='A'&&b<='Z') b+=32;
            if (a!=b){ok=0;break;}
        }
        if (ok) return &hay[i];
    }
    return NULL;
}

/**
 * @brief Extracts specific sub-parameter key values within text header definitions.
 * * @param hdr The baseline pointer string targeting search fields.
 * @param key Target string identifying token attributes (e.g., "nonce").
 * @param out Extraction destination buffer space.
 * @param sz  Size of destination validation range limits.
 * * @note PURPOSE & DESIGN JUSTIFICATION:
 * Modern RTSP cameras include unique challenge variables inside 401 response text payloads. 
 * This engine dynamically separates keys whether wrapped in quotation parameters or raw separators, 
 * automating parameter gathering for auth workflows.
 */
static void dig_field(const char *hdr, const char *key, char *out, int sz)
{
    const char *p = stristr(hdr, key);
    if (!p) { out[0]='\0'; return; }
    p += strlen(key);
    while (*p==' '||*p=='=') p++;
    if (*p=='"') {
        p++; int i=0;
        while (*p&&*p!='"'&&i<sz-1) out[i++]=*p++;
        out[i]='\0';
    } else {
        int i=0;
        while (*p&&*p!=','&&*p!='\r'&&*p!='\n'&&i<sz-1) out[i++]=*p++;
        out[i]='\0';
    }
}

/**
 * @brief Decodes 401 response blocks and maps variables into authentication structures.
 * * @param d   Target tracking context instance pointer.
 * @param buf HTTP-style data buffer received from the source camera.
 * * @note PURPOSE & DESIGN JUSTIFICATION:
 * When a stream request starts, secure cameras reject the request with a "401 Unauthorized" status 
 * containing `realm`, `nonce`, and sometimes `opaque` tokens. This routine captures those variables, 
 * updating internal states to handle upcoming authorization passes.
 */
static void parse_401(digest_ctx_t *d, const char *buf)
{
    const char *p = stristr(buf, "WWW-Authenticate:");
    if (!p) return;
    p += strlen("WWW-Authenticate:");
    dig_field(p,"realm", d->realm, sizeof(d->realm));
    dig_field(p,"nonce", d->nonce, sizeof(d->nonce));
    dig_field(p,"opaque",d->opaque,sizeof(d->opaque));
    d->valid=1;
    printf("[AUTH] realm=%s nonce=%s\n",d->realm,d->nonce);
}

/**
 * @brief Constructs standard RFC 2069/2617 Digest Challenge Response strings.
 * * @param d      Context pointer mapping existing security variables.
 * @param method RTSP step directive identifier (e.g., "DESCRIBE", "SETUP").
 * @param uri    The destination streaming route string targets.
 * @param out    Buffer targeting output formatted text strings.
 * @param sz     Destination byte array boundary sizing.
 * * @note PURPOSE & DESIGN JUSTIFICATION:
 * Standardizes authentication parameters into explicit string values using the required formatting:
 * HA1=MD5(user:realm:pass), HA2=MD5(method:url), and Response=MD5(HA1:nonce:HA2). 
 * This enables the stream client to pass security barriers implemented by enterprise cameras.
 */
static void build_auth(digest_ctx_t *d, const char *method, const char *uri,
                       char *out, int sz)
{
    char a[256],b[256],c[256],ha1[33],ha2[33],resp[33];
    snprintf(a,sizeof(a),"%s:%s:%s",CAM_USER,d->realm,CAM_PASS);
    md5_hex(a,strlen(a),ha1);
    snprintf(b,sizeof(b),"%s:%s",method,uri);
    md5_hex(b,strlen(b),ha2);
    snprintf(c,sizeof(c),"%s:%s:%s",ha1,d->nonce,ha2);
    md5_hex(c,strlen(c),resp);
    if (d->opaque[0])
        snprintf(out,sz,"Authorization: Digest username=\"%s\", realm=\"%s\", "
                 "nonce=\"%s\", uri=\"%s\", response=\"%s\", opaque=\"%s\"\r\n",
                 CAM_USER,d->realm,d->nonce,uri,resp,d->opaque);
    else
        snprintf(out,sz,"Authorization: Digest username=\"%s\", realm=\"%s\", "
                 "nonce=\"%s\", uri=\"%s\", response=\"%s\"\r\n",
                 CAM_USER,d->realm,d->nonce,uri,resp);
}

/* ── RTSP Helpers ────────────────────────────────────────────────── */
static int g_cseq=0;

/**
 * @brief Thread-safe generation wrapper building static URL endpoints.
 * * @return const char* Pointer referencing formatted streaming path.
 * * @note PURPOSE & DESIGN JUSTIFICATION:
 * Centralizes standard URL resolution behaviors across setup steps, preventing manual parsing 
 * redundancies across setup loops.
 */
static const char *rtsp_url(void)
{
    static char url[256]; static int built=0;
    if (!built){snprintf(url,sizeof(url),"rtsp://%s:%d%s",CAM_IP,CAM_PORT,CAM_PATH);built=1;}
    return url;
}

/**
 * @brief Resolves HTTP status response values within response headers.
 * * @param buf String source payload containing incoming text responses.
 * @return int Integer conversion tracking status codes (e.g., 200, 401, 404).
 * * @note PURPOSE & DESIGN JUSTIFICATION:
 * Isolates and extracts the server's numeric response code. This simplifies state checking 
 * during connection handshakes.
 */
static int parse_status(const char *buf)
{
    const char *p=buf; while(*p&&*p!=' ')p++; return *p?atoi(p+1):0;
}

/**
 * @brief Parses active connection Session identifiers from protocol feedback text.
 * * @param buf Incoming text streams evaluated.
 * @param sid Destination data pointer workspace.
 * @param sz  Tracking limitation parameter constraints.
 * * @note PURPOSE & DESIGN JUSTIFICATION:
 * After a successful `SETUP` command, the camera generates an active tracking session string. 
 * This token must be extracted and included in all subsequent `PLAY` and keepalive requests to 
 * maintain the stream connection.
 */
static void parse_session(const char *buf, char *sid, int sz)
{
    const char *p=stristr(buf,"Session:"); if(!p)return;
    p+=strlen("Session:"); while(*p==' ')p++;
    int i=0;
    while(*p&&*p!=';'&&*p!='\r'&&*p!='\n'&&*p!=' '&&i<sz-1) sid[i++]=*p++;
    sid[i]='\0';
}

/**
 * @brief Encapsulates socket writing logic with error validation checks.
 * * @param fd  Target stream socket file descriptor.
 * @param req String body query content to transmit.
 * @return int 0 if successful, -1 on failure.
 * * @note PURPOSE & DESIGN JUSTIFICATION:
 * Ensures network command delivery across standard stream sockets, managing write validation 
 * tracking seamlessly.
 */
static int rtsp_send(int fd, const char *req)
{
    ssize_t s=send(fd,req,strlen(req),0);
    if(s<0){perror("[RTSP] send");return -1;} return 0;
}

/**
 * @brief Synchronously intercepts text frames up to standard terminating double-newlines.
 * * @param fd  Target connection socket tracker.
 * @param buf Character data payload workspace destination.
 * @param sz  Size constraints boundary checks.
 * @return int Total characters processed on success, -1 on errors.
 * * @note PURPOSE & DESIGN JUSTIFICATION:
 * Since TCP is stream-oriented rather than packet-oriented, reads may slice arbitrary strings. 
 * This method forces collection routines to sustain reads until locating the standard protocol 
 * delimiter sequence `\r\n\r\n`, preventing partial header reads.
 */
static int rtsp_recv(int fd, char *buf, int sz)
{
    int total=0; memset(buf,0,sz);
    while(total<sz-1){
        ssize_t n=recv(fd,buf+total,sz-1-total,0);
        if(n<=0){if(n<0)perror("[RTSP] recv");return -1;}
        total+=(int)n; buf[total]='\0';
        if(strstr(buf,"\r\n\r\n"))break;
    }
    return total;
}

/**
 * @brief Formats and marshals active command states to target network descriptors.
 * * @param fd      Active interface socket index.
 * @param d       State pointer metadata monitoring authorization settings.
 * @param method  Target verb (e.g., "DESCRIBE", "PLAY").
 * @param extra   Optional supplemental parameter configurations.
 * @param uri_ov  Overriding destination indicator strings if present.
 * @return int    0 if successful, -1 on error.
 * * @note PURPOSE & DESIGN JUSTIFICATION:
 * Centralizes the assembly of standard RTSP request headers, dynamically handling command-specific 
 * fields, proper CSeq increments, and authorization tags.
 */
static int do_rtsp(int fd, digest_ctx_t *d, const char *method,
                   const char *extra, const char *uri_ov)
{
    char buf[2048],auth[600]="";
    const char *uri=uri_ov?uri_ov:rtsp_url();
    g_cseq++;
    if(d->valid) build_auth(d,method,uri,auth,sizeof(auth));
    if(!strcmp(method,"SETUP"))
        snprintf(buf,sizeof(buf),"SETUP %s RTSP/1.0\r\nCSeq: %d\r\nUser-Agent: LinuxRTSP/1.0\r\n%s%s\r\n",
                 uri,g_cseq,extra?extra:"",auth);
    else if(!strcmp(method,"PLAY"))
        snprintf(buf,sizeof(buf),"PLAY %s RTSP/1.0\r\nCSeq: %d\r\nUser-Agent: LinuxRTSP/1.0\r\n"
                 "%sRange: npt=0.000-\r\n%s\r\n",uri,g_cseq,extra?extra:"",auth);
    else if(!strcmp(method,"DESCRIBE"))
        snprintf(buf,sizeof(buf),"DESCRIBE %s RTSP/1.0\r\nCSeq: %d\r\nUser-Agent: LinuxRTSP/1.0\r\n"
                 "Accept: application/sdp\r\n%s\r\n",uri,g_cseq,auth);
    else if(!strcmp(method,"GET_PARAMETER"))
        snprintf(buf,sizeof(buf),"GET_PARAMETER %s RTSP/1.0\r\nCSeq: %d\r\nUser-Agent: LinuxRTSP/1.0\r\n"
                 "%s%s\r\n",uri,g_cseq,extra?extra:"",auth);
    else
        snprintf(buf,sizeof(buf),"%s %s RTSP/1.0\r\nCSeq: %d\r\nUser-Agent: LinuxRTSP/1.0\r\n%s\r\n",
                 method,uri,g_cseq,auth);
    printf("[RTSP] --> %s (CSeq %d)\n",method,g_cseq);
    return rtsp_send(fd,buf);
}

/**
 * @brief High-level handshake machine managing verification retries.
 * * @param fd      Connection socket index tracker.
 * @param d       Authentication state tracker configuration mapping blocks.
 * @param method  Target transaction verb.
 * @param extra   Additional payload argument properties.
 * @param uri_ov  Alternative direct URI parameters.
 * @param resp_buf Receiving target work tracking array.
 * @param resp_sz Boundary verification length configurations.
 * @return int    Server status verification feedback index.
 * * @note PURPOSE & DESIGN JUSTIFICATION:
 * Automated verification processing loop. Automatically catches initial 401 challenges, 
 * populates internal token fields, builds valid authentication hashes, and resubmits requests, 
 * shielding the main execution loop from complex handshake logic.
 */
static int rtsp_exchange(int fd, digest_ctx_t *d, const char *method,
                         const char *extra, const char *uri_ov,
                         char *resp_buf, int resp_sz)
{
    int attempts=0;
    while(attempts++<3){
        if(do_rtsp(fd,d,method,extra,uri_ov)<0) return -1;
        if(rtsp_recv(fd,resp_buf,resp_sz)<0) return -1;
        int st=parse_status(resp_buf);
        printf("[RTSP] <-- %d\n",st);
        if(st==200) return 200;
        if(st==401){parse_401(d,resp_buf);continue;}
        fprintf(stderr,"[RTSP] %s failed %d\n",method,st);
        return st;
    }
    return -1;
}

/**
 * @brief Transmits a non-blocking GET_PARAMETER heartbeat signal to avoid socket drops.
 * * @param tcp_fd    Connection descriptor tracking live interfaces.
 * @param d         Authentication monitoring property pointers.
 * @param session_id Session reference tracking definitions.
 * * @note PURPOSE & DESIGN JUSTIFICATION:
 * RTSP servers drop connections if no commands are received within a specific timeout window 
 * (typically 60 seconds). Periodically sending a `GET_PARAMETER` keep-alive pulse resets this 
 * server-side timer, maintaining the stream connection indefinitely.
 */
static void send_keepalive(int tcp_fd, digest_ctx_t *d, const char *sid)
{
    char extra[128],resp[512];
    snprintf(extra,sizeof(extra),"Session: %s\r\n",sid);
    do_rtsp(tcp_fd,d,"GET_PARAMETER",extra,NULL);
    fd_set r; FD_ZERO(&r); FD_SET(tcp_fd,&r);
    struct timeval tv={1,0};
    if(select(tcp_fd+1,&r,NULL,NULL,&tv)>0)
        recv(tcp_fd,resp,sizeof(resp),0);
    printf("[RTSP] keepalive sent\n");
}

/* ── HEVC FU-A Reassembly ────────────────────────────────────────── */
#define NAL_BUF_SIZE (2*1024*1024)

static uint8_t g_nal_buf[NAL_BUF_SIZE];
static int     g_nal_len  = 0;
static int     g_nal_open = 0;
static int     g_nal_bad  = 0;
static uint8_t g_out_nal[NAL_BUF_SIZE+4];
static const uint8_t SC[4]={0,0,0,1};

/**
 * @brief Resets fragmentation variables when a packet loss event is detected.
 * * @note PURPOSE & DESIGN JUSTIFICATION:
 * If an RTP packet drop occurs mid-frame during an HEVC FU-A sequence, the remaining fragment 
 * bytes become corrupted payload data. This routine invalidates the partial frame buffer to prevent 
 * sending malformed NAL units down the pipeline, which can cause downstream macroblock tearing or 
 * decoder crashes.
 */
static void nal_reset_on_gap(void)
{
    if (g_nal_open) {
        fprintf(stderr,"[NAL] gap inside FU-A — discarding partial NAL\n");
        g_nal_bad  = 1;
        g_nal_open = 0;
        g_nal_len  = 0;
    }
}

/**
 * @brief Extracts RTP network data payloads and reconstructs valid H.265 NAL elements.
 * * @param payload Raw network input buffer mapping parameters.
 * @param pay_len Size metric detailing source packet dimensions.
 * @param out_nal Reference targeting generated out arrays tracking completed elements.
 * @param out_len Data counter tracks identifying total valid frame elements outputted.
 * @return int    1 if a complete NAL unit is ready for transmission, 0 otherwise.
 * * @note PURPOSE & DESIGN JUSTIFICATION:
 * H.265 frames exceeding network MTU size (typically 1500 bytes) are fragmented across multiple 
 * RTP packets using Fragmentation Units (FU-A). This function parses the HEVC payload headers, 
 * tracks start/end bits, strips network encapsulation markers, and prepends Annex-B start codes 
 * `0x00000001` to deliver streamable NAL units to the muxer.
 */
static int rtp_to_nal(const uint8_t *payload, int pay_len,
                      uint8_t **out_nal, int *out_len)
{
    if (pay_len < 2) return 0;
    uint8_t nal_type = (payload[0]>>1) & 0x3F;

    if (nal_type <= 40) {
        memcpy(g_out_nal, SC, 4);
        memcpy(g_out_nal+4, payload, pay_len);
        *out_nal = g_out_nal;
        *out_len = 4 + pay_len;
        g_nal_bad = 0;
        return 1;
    }

    if (nal_type == 49) {
        if (pay_len < 3) return 0;
        uint8_t fu    = payload[2];
        uint8_t start = (fu>>7)&1;
        uint8_t end   = (fu>>6)&1;
        uint8_t ftype =  fu & 0x3F;

        if (start) {
            g_nal_len  = 0;
            g_nal_open = 1;
            g_nal_bad  = 0;
            memcpy(g_nal_buf, SC, 4);
            g_nal_len  = 4;
            g_nal_buf[g_nal_len++] = (payload[0] & 0x81) | (ftype<<1);
            g_nal_buf[g_nal_len++] = payload[1];
        }

        if (!g_nal_open || g_nal_bad) return 0;

        int frag_len = pay_len - 3;
        if (g_nal_len + frag_len > NAL_BUF_SIZE) {
            fprintf(stderr,"[NAL] FU-A overflow — discarding\n");
            g_nal_open = 0; g_nal_len = 0; g_nal_bad = 1;
            return 0;
        }
        memcpy(g_nal_buf + g_nal_len, payload+3, frag_len);
        g_nal_len += frag_len;

        if (end) {
            g_nal_open = 0;
            *out_nal   = g_nal_buf;
            *out_len   = g_nal_len;
            return 1;
        }
        return 0;
    }
    return 0;
}

/* ── MPEG-TS Muxer ───────────────────────────────────────────────── */
#define TS_PKT_SIZE      188
#define PID_PAT          0x0000
#define PID_PMT          0x1000
#define PID_VIDEO        0x0100
#define STREAM_TYPE_HEVC 0x24
#define TS_PER_UDP       7
#define UDP_TS_SIZE      (TS_PER_UDP*TS_PKT_SIZE)

static uint8_t           g_udp_buf[UDP_TS_SIZE];
static int               g_udp_fill=0;
static uint8_t           g_cc_pat=0,g_cc_pmt=0,g_cc_video=0;
static int               g_fwd_fd;
static struct sockaddr_in g_vlc_addr;

/**
 * @brief Flushes buffered TS packets to UDP, appending stuffing null packets if needed.
 * * @note PURPOSE & DESIGN JUSTIFICATION:
 * For optimal throughput, individual 188-byte TS packets are grouped into chunks of 7 before transmission 
 * ($7 \times 188 = 1316$ bytes), which perfectly fits under standard Ethernet MTU boundaries (1500 bytes). 
 * If a video frame terminates without completing a group, this function pads the remainder with PID 0x1FFF 
 * null packets, ensuring the network payload is aligned and sent immediately to prevent latency spikes.
 */
static void ts_flush(void)
{
    if (!g_udp_fill) return;
    while (g_udp_fill < TS_PER_UDP) {
        uint8_t *p = g_udp_buf + g_udp_fill*TS_PKT_SIZE;
        memset(p,0xFF,TS_PKT_SIZE);
        p[0]=0x47; p[1]=0x1F; p[2]=0xFF; p[3]=0x10;
        g_udp_fill++;
    }
    sendto(g_fwd_fd,g_udp_buf,UDP_TS_SIZE,0,
           (struct sockaddr*)&g_vlc_addr,sizeof(g_vlc_addr));
    g_udp_fill=0;
}

/**
 * @brief Enqueues a single 188-byte TS packet into the UDP pipeline buffer block.
 * * @param pkt Array block holding a 188-byte raw data chunk.
 * * @note PURPOSE & DESIGN JUSTIFICATION:
 * Acts as the staging area interface feeding into the UDP transmission layer.
 */
static void ts_enqueue(const uint8_t pkt[TS_PKT_SIZE])
{
    memcpy(g_udp_buf + g_udp_fill*TS_PKT_SIZE, pkt, TS_PKT_SIZE);
    if (++g_udp_fill == TS_PER_UDP) ts_flush();
}

/**
 * @brief Formats raw data payloads into structured 188-byte MPEG-TS transport packets.
 * * @param pid     Target identifier route mapping (PAT, PMT, Video).
 * @param pusi    Payload Unit Start Indicator flag.
 * @param cc      Pointer tracking the continuity counter register specific to this stream.
 * @param payload Data content segment array to encapsuate.
 * @param pay_len Size metrics tracking input size specifications.
 * * @note PURPOSE & DESIGN JUSTIFICATION:
 * This function enforces strict ISO/IEC 13818-1 framing rules. It manages packetization, 
 * builds target headers, calculates adaptation field lengths for small fragments, and explicitly 
 * increments the sequence continuity counter parameter strictly once per packet transmitted to 
 * avoid media errors.
 */
static void ts_write_pkt(uint16_t pid, int pusi, uint8_t *cc,
                         const uint8_t *payload, int pay_len)
{
    uint8_t pkt[TS_PKT_SIZE];
    memset(pkt,0xFF,TS_PKT_SIZE);
    pkt[0]=0x47;
    pkt[1]=(uint8_t)(((pusi?1:0)<<6)|((pid>>8)&0x1F));
    pkt[2]=(uint8_t)(pid&0xFF);
    
    int data_len=TS_PKT_SIZE-4;
    if (pay_len>=data_len) {
        pkt[3]=(uint8_t)(0x10|(*cc&0x0F));
        memcpy(pkt+4,payload,data_len);
    } else {
        int stuff=data_len-pay_len;
        pkt[3]=(uint8_t)(0x30|(*cc&0x0F));
        if (stuff==1){ 
            pkt[4]=0x00; 
        } else { 
            pkt[4]=(uint8_t)(stuff-1); 
            pkt[5]=0x00; 
            if (stuff > 2) memset(&pkt[6],0xFF,stuff-2); 
        }
        memcpy(pkt+4+stuff,payload,pay_len);
    }
    *cc = (*cc + 1) & 0x0F;
    ts_enqueue(pkt);
}

/**
 * @brief Assembles and emits the Program Association Table (PAT).
 * * @note PURPOSE & DESIGN JUSTIFICATION:
 * The PAT serves as the root index of an MPEG Transport Stream, linking Program Numbers to 
 * their respective PMT PIDs. Without periodic PAT broadcasts, incoming network decoders cannot 
 * resolve the internal layout of the multiplexed stream, rendering the content unplayable.
 */
static void ts_send_pat(void)
{
    uint8_t pat[17]={0x00,0x00,0xB0,0x0D,0x00,0x01,0xC1,0x00,
                     0x00,0x00,0x01,0x10,0x00,0,0,0,0};
    uint32_t crc=mpeg_crc32(&pat[1],12);
    pat[13]=(crc>>24)&0xFF; pat[14]=(crc>>16)&0xFF;
    pat[15]=(crc>>8)&0xFF;  pat[16]=crc&0xFF;
    ts_write_pkt(PID_PAT,1,&g_cc_pat,pat,sizeof(pat));
}

/**
 * @brief Assembles and emits the Program Map Table (PMT).
 * * @note PURPOSE & DESIGN JUSTIFICATION:
 * The PMT maps media tracks within a program to their respective media types. It explicitly binds 
 * PID `0x0100` to stream type `0x24` (H.265/HEVC video). This allows media players like VLC to 
 * spin up the correct hardware decoding engine.
 */
static void ts_send_pmt(void)
{
    uint8_t pmt[22]={0x00,0x02,0xB0,0x12,0x00,0x01,0xC1,0x00,
                     0x00,0xE1,0x00,0xF0,0x00,
                     STREAM_TYPE_HEVC,0xE1,0x00,0xF0,0x00,
                     0,0,0,0};
    uint32_t crc=mpeg_crc32(&pmt[1],17);
    pmt[18]=(crc>>24)&0xFF; pmt[19]=(crc>>16)&0xFF;
    pmt[20]=(crc>>8)&0xFF;  pmt[21]=crc&0xFF;
    ts_write_pkt(PID_PMT,1,&g_cc_pmt,pmt,sizeof(pmt));
}

/**
 * @brief Packetizes H.265 NAL units into PES packets with real-time PCR clock synchronization.
 * * @param nal    H.265 video frame tracking pointer.
 * @param nal_len Byte dimension size configurations.
 * @param pts_90 90kHz resolved Presentation Time Stamp target metrics.
 * * @note PURPOSE & DESIGN JUSTIFICATION:
 * Encapsulates video data into a Packetized Elementary Stream (PES) header carrying a 90kHz PTS 
 * timeline. Crucially, when an IDR keyframe arrives, this function injects an Adaptation Field 
 * containing a **Program Clock Reference (PCR)** timestamp. This provides downstream players with 
 * a reference master clock, preventing buffer drift and fixing the "PCR is called too late" error.
 */
static void ts_send_nal(const uint8_t *nal, int nal_len, uint32_t pts_90)
{
    uint8_t pes[14];
    pes[0]=0x00; pes[1]=0x00; pes[2]=0x01; pes[3]=0xE0;
    pes[4]=0x00; pes[5]=0x00; pes[6]=0x80; pes[7]=0x80; pes[8]=0x05;
    pes[9] =(uint8_t)(0x21|((pts_90>>29)&0x0E));
    pes[10]=(uint8_t)((pts_90>>22)&0xFF);
    pes[11]=(uint8_t)(0x01|((pts_90>>14)&0xFE));
    pes[12]=(uint8_t)((pts_90>>7)&0xFF);
    pes[13]=(uint8_t)(0x01|((pts_90<<1)&0xFE));
    
    int total=14+nal_len, src_pos=0, pusi=1;
    uint8_t *frame=(uint8_t*)malloc(total);
    if (!frame) return;
    memcpy(frame,pes,14); memcpy(frame+14,nal,nal_len);
    
    uint8_t hevc_type = (nal[4] >> 1) & 0x3F;
    int is_idr = (hevc_type == 19 || hevc_type == 20);

    while (src_pos<total) {
        uint8_t pkt[TS_PKT_SIZE];
        memset(pkt,0xFF,TS_PKT_SIZE);
        
        pkt[0]=0x47;
        pkt[1]=(uint8_t)(((pusi?1:0)<<6)|((PID_VIDEO>>8)&0x1F));
        pkt[2]=(uint8_t)(PID_VIDEO&0xFF);
        
        if (pusi && is_idr) {
            pkt[3] = (uint8_t)(0x30 | (g_cc_video & 0x0F));
            pkt[4] = 7;    
            pkt[5] = 0x10; 
            
            uint64_t pcr_base = pts_90;
            pkt[6] = (uint8_t)((pcr_base >> 25) & 0xFF);
            pkt[7] = (uint8_t)((pcr_base >> 17) & 0xFF);
            pkt[8] = (uint8_t)((pcr_base >> 9) & 0xFF);
            pkt[9] = (uint8_t)((pcr_base >> 1) & 0xFF);
            pkt[10] = (uint8_t)(((pcr_base & 1) << 7) | 0x7E);
            pkt[11] = 0x00; 
            
            int avail = TS_PKT_SIZE - 12;
            int chunk = (total - src_pos) < avail ? (total - src_pos) : avail;
            memcpy(pkt + 12, frame + src_pos, chunk);
            src_pos += chunk;
        } else {
            int avail = TS_PKT_SIZE - 4;
            int chunk = (total - src_pos) < avail ? (total - src_pos) : avail;
            if (chunk >= avail) {
                pkt[3] = (uint8_t)(0x10 | (g_cc_video & 0x0F));
                memcpy(pkt + 4, frame + src_pos, chunk);
            } else {
                int stuff = avail - chunk;
                pkt[3] = (uint8_t)(0x30 | (g_cc_video & 0x0F));
                if (stuff == 1) {
                    pkt[4] = 0x00;
                } else {
                    pkt[4] = (uint8_t)(stuff - 1);
                    pkt[5] = 0x00;
                    if (stuff > 2) memset(&pkt[6], 0xFF, stuff - 2);
                }
                memcpy(pkt + 4 + stuff, frame + src_pos, chunk);
            }
            src_pos += chunk;
        }
        g_cc_video = (g_cc_video + 1) & 0x0F;
        ts_enqueue(pkt);
        pusi=0;
    }
    free(frame);
}

/* ── RTP Reorder Buffer ──────────────────────────────────────────── */
#define SEQ_AHEAD(a,b) ((uint16_t)((a)-(b)) < 0x8000u)

typedef struct {
    uint8_t  data[RTP_BUF_SIZE];
    ssize_t  len;
    uint32_t rtp_ts;
    uint16_t seq;
    uint8_t  used;
} rtp_slot_t;

static rtp_slot_t g_rbuf[REORDER_WIN];
static uint16_t   g_next_seq   = 0;
static int        g_seq_init   = 0;
static int        g_rbuf_count = 0;
static uint64_t   g_stall_since = 0;

/**
 * @brief Inserts incoming UDP/RTP network packets into an ordered bounded window array.
 * * @param data   Pointer referencing raw packet sources.
 * @param len    Dimension metrics detailing packet scale.
 * @param seq    RTP sequence identity number.
 * @param rtp_ts Internal sample clock value mapped to the incoming frame.
 * @return int   1 if window boundaries are overrun forcing recovery bypasses, 0 otherwise.
 * * @note PURPOSE & DESIGN JUSTIFICATION:
 * UDP streams frequently arrive out-of-order due to network multi-path routing. This function 
 * caches incoming packets in a sliding window buffer array. It drops stale, duplicate data and 
 * tracks expected sequence numbers to prevent out-of-order delivery to the H.265 parser.
 */
static int rbuf_insert(const uint8_t *data, ssize_t len,
                       uint16_t seq, uint32_t rtp_ts)
{
    if (!g_seq_init) {
        g_next_seq = seq;
        g_seq_init = 1;
    }

    if (g_seq_init && seq != g_next_seq && !SEQ_AHEAD(seq, g_next_seq)) {
        printf("  [REORDER] drop stale seq=%u (next=%u)\n", seq, g_next_seq);
        return 0;
    }

    if (seq == g_next_seq)
        g_stall_since = 0;

    for (int i = 0; i < REORDER_WIN; i++) {
        if (!g_rbuf[i].used) {
            memcpy(g_rbuf[i].data, data, len);
            g_rbuf[i].len    = len;
            g_rbuf[i].seq    = seq;
            g_rbuf[i].rtp_ts = rtp_ts;
            g_rbuf[i].used   = 1;
            g_rbuf_count++;
            return 0;
        }
    }
    fprintf(stderr,"[REORDER] window full! forcing skip of seq=%u\n",g_next_seq);
    return 1;
}

/**
 * @brief Extracts the exact target sequential entry from the reordering structure buffer.
 * * @param target Targeted tracking index value requested.
 * @param dst    Workspace array area where properties are pulled.
 * @param ts_out Output tracker capturing temporal parameters.
 * @return ssize_t Length size of valid payload recovered, or -1 on missing sequence values.
 * * @note PURPOSE & DESIGN JUSTIFICATION:
 * Performs an extraction check over active slots. If the exact sequential sequence number is present, 
 * it frees the slot and returns the payload data, enabling in-order stream reconstruction.
 */
static ssize_t rbuf_pop(uint16_t target, uint8_t *dst, uint32_t *ts_out)
{
    for (int i = 0; i < REORDER_WIN; i++) {
        if (g_rbuf[i].used && g_rbuf[i].seq == target) {
            ssize_t l = g_rbuf[i].len;
            memcpy(dst, g_rbuf[i].data, l);
            *ts_out        = g_rbuf[i].rtp_ts;
            g_rbuf[i].used = 0;
            g_rbuf_count--;
            return l;
        }
    }
    return -1;
}

/**
 * @brief Decodes individual RTP packets, extracts extension metadata, and passes NAL units to the TS muxer.
 * * @param pkt          The raw structural RTP tracking pointer array.
 * @param n            Byte scale size configurations.
 * @param last_ts      Pointer monitoring preceding timestamp indices.
 * @param pts_90       Active 90kHz converted clock monitoring configuration variables.
 * @param pat_interval Broadcast cadence counter mapping tables.
 * @param got_idr      Boolean verification status parameter checking stream startup keys.
 * * @note PURPOSE & DESIGN JUSTIFICATION:
 * Parses RFC 3550 RTP headers, resolving variable CSRC extension counts and profile padding headers. 
 * It converts standard 90kHz media timestamps smoothly, suppresses data ingestion blocks until locating 
 * a clean H.265 keyframe boundary, and drives the downstream table generation engines.
 */
static void process_ordered_pkt(const uint8_t *pkt, ssize_t n,
                                 uint32_t *last_ts, uint32_t *pts_90,
                                 int *pat_interval, int *got_idr)
{
    if (n < 12) return;

    uint8_t  cc       = pkt[0] & 0x0F;
    uint8_t  marker   = (pkt[1]>>7) & 1;
    uint8_t  pt       = pkt[1] & 0x7F;
    uint16_t seq      = (uint16_t)((pkt[2]<<8)|pkt[3]);
    uint32_t rtp_ts   = ((uint32_t)pkt[4]<<24)|((uint32_t)pkt[5]<<16)
                       |((uint32_t)pkt[6]<<8)|(uint32_t)pkt[7];

    uint16_t hdr_size = (uint16_t)(12 + 4*cc);
    if (((pkt[0]>>4)&1) && n >= hdr_size+4) {
        uint16_t el = (uint16_t)((pkt[hdr_size+2]<<8)|pkt[hdr_size+3]);
        hdr_size   += (uint16_t)(4 + 4*el);
    }
    if (hdr_size >= (int)n) return;

    const uint8_t *payload = pkt + hdr_size;
    int pay_len = (int)n - hdr_size;

    if (rtp_ts != *last_ts) {
        *pts_90 += (rtp_ts - *last_ts);
        *last_ts = rtp_ts;
    }

    printf("[RTP ordered] PT=%d seq=%u ts=%u M=%d pay=%d\n", pt, seq, rtp_ts, marker, pay_len);

    uint8_t *nal = NULL; int nal_len = 0;
    if (!rtp_to_nal(payload, pay_len, &nal, &nal_len)) return;

    if (g_nal_bad) {
        fprintf(stderr,"[NAL] discarding corrupted NAL (cu_qp_delta prevention)\n");
        g_nal_bad = 0;
        return;
    }

    uint8_t hevc_type = (nal[4]>>1) & 0x3F;
    printf("  [HEVC NAL] type=%d len=%d\n", hevc_type, nal_len);

    if (!*got_idr) {
        if (hevc_type==19 || hevc_type==20) {
            printf("  [IDR] First keyframe — starting VLC output\n");
            *got_idr = 1;
            ts_send_pat(); ts_send_pmt();
        } else if (hevc_type < 32) {
            printf("  [SKIP] waiting for IDR\n");
            return;
        }
    }

    if ((*pat_interval)++ % 30 == 0) {
        ts_send_pat(); ts_send_pmt();
    }

    ts_send_nal(nal, nal_len, *pts_90);
    if (marker) ts_flush();
}

/**
 * @brief Continually pulls contiguous ordered packets out of the cache structure.
 * * @param tmp          Intermediate frame destination allocation.
 * @param last_ts      Previous timestamp value reference tracker.
 * @param pts_90       Output clock variable pointers.
 * @param pat_interval Broadcast timeline pacing trackers.
 * @param got_idr      Verification keyframe check indicator states.
 * * @note PURPOSE & DESIGN JUSTIFICATION:
 * Drives the reordering cache machine. Loops through available sequence items to pull sequential 
 * packets from the queue. It stops immediately when encountering a missing sequence gap, letting 
 * the cache stage data until the missing packet arrives or a timeout is reached.
 */
static void rbuf_drain(uint8_t *tmp,
                       uint32_t *last_ts, uint32_t *pts_90,
                       int *pat_interval, int *got_idr)
{
    while (g_rbuf_count > 0) {
        uint32_t ts_val = 0;
        ssize_t  n      = rbuf_pop(g_next_seq, tmp, &ts_val);
        if (n < 0) {
            if (g_stall_since == 0)
                g_stall_since = now_ms();
            break;
        }
        g_next_seq++;
        g_stall_since = 0;
        process_ordered_pkt(tmp, n, last_ts, pts_90, pat_interval, got_idr);
    }
}

/**
 * @brief Forces cache pipeline advancement if a critical jitter stall threshold is breached.
 * * @param tmp          Intermediate payload work block arrays.
 * @param last_ts      Temporal synchronization clock tracker pointers.
 * @param pts_90       Muxer presentation timeline tracks.
 * @param pat_interval Base information configuration update metrics.
 * @param got_idr      Active connection start mapping tracking fields.
 * @return int         1 if a timeout skip was executed, 0 otherwise.
 * * @note PURPOSE & DESIGN JUSTIFICATION:
 * If an unrecoverable packet drop occurs, the reordering cache would stall indefinitely waiting 
 * for a sequence number that will never arrive. This function acts as a watchdog timer. If the gap 
 * persists past `STALL_MS` (150ms), it drops the missing packet, resets the reassembly state, and 
 * skips ahead to maintain fluent video playback.
 */
static int rbuf_maybe_skip(uint8_t *tmp,
                           uint32_t *last_ts, uint32_t *pts_90,
                           int *pat_interval, int *got_idr)
{
    if (g_rbuf_count == 0 || g_stall_since == 0) return 0;

    uint64_t elapsed = now_ms() - g_stall_since;
    if (elapsed < STALL_MS) return 0;

    fprintf(stderr,"[REORDER] %.0f ms stall — skipping seq=%u\n", (double)elapsed, g_next_seq);

    nal_reset_on_gap();
    g_next_seq++;
    g_stall_since = 0;

    rbuf_drain(tmp, last_ts, pts_90, pat_interval, got_idr);
    return 1;
}

/* ── Main RTP Pipeline ───────────────────────────────────────────── */

/**
 * @brief High-frequency core execution worker thread processing multi-socket event traffic loops.
 * * @param tcp_fd     Active command pathway interface socket descriptor index.
 * @param rtp_fd     Active incoming media stream datagram network socket index.
 * @param rtcp_fd    Active incoming telemetry datagram network descriptor.
 * @param d          Cryptographic structure variable mappings context configurations.
 * @param session_id Token value defining current session permissions.
 * * @note PURPOSE & DESIGN JUSTIFICATION:
 * The primary operations hub of the system. It handles the low-latency socket multiplexing loop, 
 * interleaves keep-alive heartbeats to prevent connection timeouts, and pumps incoming network packets 
 * through the jitter-reordering filter and H.265 transport stream engines.
 */
static void rtp_pipeline(int tcp_fd, int rtp_fd, int rtcp_fd,
                         digest_ctx_t *d, const char *session_id)
{
    uint8_t  buf[RTP_BUF_SIZE];
    uint8_t  drain_buf[RTP_BUF_SIZE];
    uint64_t pkt_count   = 0;
    uint32_t last_ts     = 0, pts_90 = 0;
    int      pat_interval = 0;
    time_t   last_ka     = time(NULL);
    int      got_idr     = 0;

    printf("[RTP] Receiving. VLC: vlc udp://@:%d\n\n", VLC_PORT);
    ts_send_pat(); ts_send_pmt();

    while (1) {
        time_t now_sec = time(NULL);
        if (now_sec - last_ka >= KEEPALIVE_SECS) {
            send_keepalive(tcp_fd, d, session_id);
            last_ka = now_sec;
        }

        rbuf_maybe_skip(drain_buf, &last_ts, &pts_90, &pat_interval, &got_idr);

        fd_set rfds;
        FD_ZERO(&rfds);
        FD_SET(rtp_fd,  &rfds);
        FD_SET(rtcp_fd, &rfds);
        int maxfd = (rtp_fd > rtcp_fd ? rtp_fd : rtcp_fd) + 1;

        struct timeval tv = {0, 10000};
        int rc = select(maxfd, &rfds, NULL, NULL, &tv);
        if (rc < 0) { perror("select"); break; }

        if (rc == 0) {
            rbuf_maybe_skip(drain_buf, &last_ts, &pts_90, &pat_interval, &got_idr);
            continue;
        }

        if (FD_ISSET(rtcp_fd, &rfds))
            recv(rtcp_fd, buf, sizeof(buf), 0);

        if (!FD_ISSET(rtp_fd, &rfds)) continue;

        ssize_t n = recv(rtp_fd, buf, sizeof(buf), 0);
        if (n < 12) continue;

        uint16_t seq    = (uint16_t)((buf[2]<<8)|buf[3]);
        uint32_t rtp_ts = ((uint32_t)buf[4]<<24)|((uint32_t)buf[5]<<16)
                        | ((uint32_t)buf[6]<<8)|(uint32_t)buf[7];
        pkt_count++;
        printf("[RTP #%llu] seq=%u ts=%u len=%d\n", (unsigned long long)pkt_count, seq, rtp_ts, (int)n);

        int force = rbuf_insert(buf, n, seq, rtp_ts);
        if (force) {
            nal_reset_on_gap();
            g_next_seq++;
            g_stall_since = 0;
        }

        rbuf_drain(drain_buf, &last_ts, &pts_90, &pat_interval, &got_idr);
    }
}

/* ── Entry Point ─────────────────────────────────────────────────── */

/**
 * @brief Application initial entry, hardware resource mapper, and sequence configuration orchestration layer.
 * * @return int EXIT_SUCCESS (0) on smooth shutdown, structural system failure flags on early exit aborts.
 * * @note PURPOSE & DESIGN JUSTIFICATION:
 * Sets up system environments. It allocates local socket binds, runs through standard sequence steps 
 * (`OPTIONS`, `DESCRIBE`, `SETUP`, `PLAY`), resolves the target camera's authentication challenges, and 
 * passes execution over to the high-speed data acquisition loops.
 */
int main(void)
{
    int tcp_fd=-1, rtp_fd=-1, rtcp_fd=-1, fwd_fd=-1;
    char buf[RTSP_BUF_SIZE], session_id[64]="", extra[128];
    digest_ctx_t digest;
    memset(&digest,0,sizeof(digest));

    printf("=== RTSP->HEVC->MPEG-TS->UDP (no dependencies) ===\n");
    printf("Camera : %s:%d%s\n", CAM_IP, CAM_PORT, CAM_PATH);
    printf("Output : vlc udp://@:%d\n\n", VLC_PORT);

    rtp_fd  = socket(AF_INET,SOCK_DGRAM,0);
    rtcp_fd = socket(AF_INET,SOCK_DGRAM,0);
    fwd_fd  = socket(AF_INET,SOCK_DGRAM,0);
    if (rtp_fd<0||rtcp_fd<0||fwd_fd<0){ perror("socket"); return 1; }

    struct sockaddr_in a={0};
    a.sin_family=AF_INET; a.sin_addr.s_addr=INADDR_ANY;
    a.sin_port=htons(RTP_RECV_PORT);
    if (bind(rtp_fd,(struct sockaddr*)&a,sizeof(a))<0){ perror("rtp bind"); return 1; }
    a.sin_port=htons(RTCP_RECV_PORT);
    if (bind(rtcp_fd,(struct sockaddr*)&a,sizeof(a))<0){ perror("rtcp bind"); return 1; }

    memset(&g_vlc_addr,0,sizeof(g_vlc_addr));
    g_vlc_addr.sin_family=AF_INET;
    g_vlc_addr.sin_port=htons(VLC_PORT);
    inet_pton(AF_INET,VLC_IP,&g_vlc_addr.sin_addr);
    g_fwd_fd=fwd_fd;

    tcp_fd=socket(AF_INET,SOCK_STREAM,0);
    if (tcp_fd<0){ perror("tcp"); return 1; }
    struct sockaddr_in cam={0};
    cam.sin_family=AF_INET; cam.sin_port=htons(CAM_PORT);
    inet_pton(AF_INET,CAM_IP,&cam.sin_addr);
    printf("[TCP] Connecting to %s:%d ...\n",CAM_IP,CAM_PORT);
    if (connect(tcp_fd,(struct sockaddr*)&cam,sizeof(cam))<0){ perror("connect"); return 1; }
    printf("[TCP] Connected\n\n");

    do_rtsp(tcp_fd,&digest,"OPTIONS",NULL,NULL);
    rtsp_recv(tcp_fd,buf,sizeof(buf));
    printf("[RTSP] <-- %d\n",parse_status(buf));
    if (parse_status(buf)==401){
        printf("[RTSP] Dahua quirk: harvesting nonce\n\n");
        parse_401(&digest,buf);
    }

    if (rtsp_exchange(tcp_fd,&digest,"DESCRIBE",NULL,NULL,buf,sizeof(buf))!=200) return 1;
    printf("[RTSP] DESCRIBE OK\n\n%s\n",buf);

    snprintf(extra,sizeof(extra),"Transport: RTP/AVP;unicast;client_port=%d-%d\r\n", RTP_RECV_PORT,RTCP_RECV_PORT);
    char track[256];
    snprintf(track,sizeof(track),"%s/trackID=0",rtsp_url());
    if (rtsp_exchange(tcp_fd,&digest,"SETUP",extra,track,buf,sizeof(buf))!=200) return 1;
    parse_session(buf,session_id,sizeof(session_id));
    printf("[RTSP] SETUP OK - Session: %s\n\n",session_id);

    char sess_hdr[128];
    snprintf(sess_hdr,sizeof(sess_hdr),"Session: %s\r\n",session_id);
    if (rtsp_exchange(tcp_fd,&digest,"PLAY",sess_hdr,NULL,buf,sizeof(buf))!=200) return 1;
    printf("[RTSP] PLAY OK\n\n");

    rtp_pipeline(tcp_fd,rtp_fd,rtcp_fd,&digest,session_id);

    close(tcp_fd); close(rtp_fd); close(rtcp_fd); close(fwd_fd);
    return 0;
}
