RTSP Client (No Dependencies)

A high-performance, standalone RTSP client implemented entirely in ANSI C without external libraries. The project establishes an RTSP session with IP cameras, performs Digest Authentication, receives H.265/HEVC video over RTP, reassembles fragmented NAL units, packetizes them into MPEG Transport Stream (MPEG-TS), and forwards the stream over UDP for playback in applications such as VLC. The implementation includes RTP packet reordering, MPEG-TS multiplexing, keep-alive handling, and low-latency streaming, making it suitable for embedded Linux and resource-constrained systems.

## Build

Compile the source code using GCC.

```bash
gcc rtsp_connect.c -o rtsp_client
```

## Run

Execute the application.

```bash
./rtsp_client
```

## View the Stream

Open VLC and play the UDP stream.

```bash
vlc udp://@:6972
```

Or in VLC:

**Media → Open Network Stream**

Enter:

```
udp://@:6972
```

Click **Play**.

## Source Code

The complete implementation is available in:

```
rtsp_connect.c
```
