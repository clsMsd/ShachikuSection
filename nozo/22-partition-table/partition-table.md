
```
$ dd if=/dev/zero of=./disk.img bs=1M count=32
32+0 records in
32+0 records out
33554432 bytes (34 MB, 32 MiB) copied, 0.890647 s, 37.7 MB/s
$ fdisk disk.img 

Welcome to fdisk (util-linux 2.32.1).
Changes will remain in memory only, until you decide to write them.
Be careful before using the write command.

Device does not contain a recognized partition table.
Created a new DOS disklabel with disk identifier 0x840d6133.

Command (m for help): n
Partition type
   p   primary (0 primary, 0 extended, 4 free)
   e   extended (container for logical partitions)
Select (default p): 

Using default response p.
Partition number (1-4, default 1): 
First sector (2048-65535, default 2048): 
Last sector, +sectors or +size{K,M,G,T,P} (2048-65535, default 65535): 

Created a new partition 1 of type 'Linux' and of size 31 MiB.

Command (m for help): w
The partition table has been altered.
Syncing disks.
```

```
$ hexdump disk.img 
0000000 0000 0000 0000 0000 0000 0000 0000 0000
*
00001b0 0000 0000 0000 0000 6133 840d 0000 2000
00001c0 0021 1483 0410 0800 0000 f800 0000 0000
00001d0 0000 0000 0000 0000 0000 0000 0000 0000
*
00001f0 0000 0000 0000 0000 0000 0000 0000 aa55
0000200 0000 0000 0000 0000 0000 0000 0000 0000
*
2000000
```
