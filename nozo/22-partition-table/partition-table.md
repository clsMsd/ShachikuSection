# パーティションテーブルについて調査

ディスクを論理的に分割することをパーティショニングといい、パーティション情報はパーティションテーブルに書き込まれる。

パーティション形式には次の２つの種類がある。
旧来のMBRを置き換える目的でGPTが登場した。

- MBR (Master Boot Record)
- GPT (GUID Partition Table)

## MBRパーティションテーブル

空のブロックデバイスにMBRパーティションを作成して中身を見てみる。

```
$ dd if=/dev/zero of=./disk.img bs=1M count=32
32+0 records in
32+0 records out
33554432 bytes (34 MB, 32 MiB) copied, 0.884599 s, 37.9 MB/s
$ sudo losetup -Pf disk.img
$ lsblk
NAME   MAJ:MIN RM  SIZE RO TYPE MOUNTPOINT
loop0    7:0    0   32M  0 loop              # 空のブロックデバイス
sda      8:0    0   10G  0 disk 
├─sda1   8:1    0  200M  0 part /boot/efi
└─sda2   8:2    0  9.8G  0 part /
sdb      8:16   0   10G  0 disk 
└─sdb1   8:17   0   10G  0 part /mnt
```

MBRパーティションを作成する。
ここでは`fdisk`というツールを使って、１つのパーティションを作成した。

```
$ sudo fdisk /dev/loop0 

Welcome to fdisk (util-linux 2.32.1).
Changes will remain in memory only, until you decide to write them.
Be careful before using the write command.

Device does not contain a recognized partition table.
Created a new DOS disklabel with disk identifier 0xb24a0fb6.

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
Calling ioctl() to re-read partition table.
$ sudo fdisk -l /dev/loop0
Disk /dev/loop0: 32 MiB, 33554432 bytes, 65536 sectors
Units: sectors of 1 * 512 = 512 bytes
Sector size (logical/physical): 512 bytes / 512 bytes
I/O size (minimum/optimal): 512 bytes / 512 bytes
Disklabel type: dos
Disk identifier: 0xb24a0fb6

Device       Boot Start   End Sectors Size Id Type
/dev/loop0p1       2048 65535   63488  31M 83 Linux
```

ブロックデバイスのバイナリ出力を見る。
MBRのパーティションテーブルはディスクの先頭512バイト領域に作成される。

```
$ sudo hexdump -C /dev/loop0
00000000  00 00 00 00 00 00 00 00  00 00 00 00 00 00 00 00  |................|
*
000001b0  00 00 00 00 00 00 00 00  b6 0f 4a b2 00 00 00 20  |..........J.... |
000001c0  21 00 83 14 10 04 00 08  00 00 00 f8 00 00 00 00  |!...............|
000001d0  00 00 00 00 00 00 00 00  00 00 00 00 00 00 00 00  |................|
*
000001f0  00 00 00 00 00 00 00 00  00 00 00 00 00 00 55 aa  |..............U.|
00000200  00 00 00 00 00 00 00 00  00 00 00 00 00 00 00 00  |................|
*
02000000
```

MBRパーティションテーブルのレイアウトを以下に示す。

|アドレス|サイズ<br>(byte)|詳細|
|----|----|----|
|0x000|446|ブートストラップコードエリア(ディスクシグニチャを含む)|
|0x1BE|16|パーティションエントリ１|
|0x1CE|16|パーティションエントリ２|
|0x1DE|16|パーティションエントリ３|
|0x1EE|16|パーティションエントリ４|
|0x1FE|2|ブートシグニチャ(0x55,0xAA)|

パーティションエントリのレイアウトを以下に示す。

|オフセット|サイズ<br>(byte)|詳細|今回の値|
|----|----|----|----|
|0x0|1|パーティションステータス(0x80=ブート可)|0x 00|
|0x1|3|パーティションの最初のCHSアドレス|0x 20 21 00|
|0x4|1|パーティションタイプ|0x 83|
|0x5|3|パーティションの最後のCHSアドレス|0x 14 10 04|
|0x8|4|パーティションの最初のLBAアドレス|0x 00 08 00 00|
|0xC|4|パーティションのセクター数|0x 00 F8 00 00|

パーティションエントリは、それぞれのパーティションが占有するディスク内の領域のアドレス(とセクタ数)を示している。

ディスク内のアドレスの表現方法には次の２つがある。

- CHS(Cylinder head sector) : アドレスをシリンダ・ヘッド・セクタの３要素で指定する
- LBA(Logical Block Addressing) : アドレスをディスクの先頭から何番目のセクタかで指定する

例えば、オフセット`0x8`はパーティションの最初のLBAアドレスを4バイト(リトルエンディアン)で示していて、今回の場合は`2048 (=0x00000800)`番目のセクタを指している。
オフセット`0xC`はパーティションのセクタ数を4バイト（リトルエンディアン）で示していて、今回の場合は`‭63488‬ (=0x0000F800)`個のセクタであることを示している。

```
$ sudo fdisk -l /dev/loop0
Disk /dev/loop0: 32 MiB, 33554432 bytes, 65536 sectors
Units: sectors of 1 * 512 = 512 bytes
Sector size (logical/physical): 512 bytes / 512 bytes
I/O size (minimum/optimal): 512 bytes / 512 bytes
Disklabel type: dos
Disk identifier: 0xb24a0fb6

Device       Boot Start   End Sectors Size Id Type
/dev/loop0p1       2048 65535   63488  31M 83 Linux
```

# 参考
- Master boot record, https://en.wikipedia.org/wiki/Master_boot_record
