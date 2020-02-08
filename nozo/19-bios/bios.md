# qemuでBIOSをデバッグする

ブートプロセスの挙動を追うために、qemuでBIOSをデバッグする手法を調査する。

## 実験環境

```
$ uname -a
Linux instance-1 4.9.0-11-amd64 #1 SMP Debian 4.9.189-3+deb9u2 (2019-11-11) x86_64 GNU/Linux
$ qemu-system-i386 --version
QEMU emulator version 2.8.1(Debian 1:2.8+dfsg-6+deb9u9)
Copyright (c) 2003-2016 Fabrice Bellard and the QEMU Project developers
$ gdb --version
GNU gdb (Debian 7.12-6) 7.12.0.20161007-git
Copyright (C) 2016 Free Software Foundation, Inc.
License GPLv3+: GNU GPL version 3 or later <http://gnu.org/licenses/gpl.html>
This is free software: you are free to change and redistribute it.
There is NO WARRANTY, to the extent permitted by law.  Type "show copying"
and "show warranty" for details.
This GDB was configured as "x86_64-linux-gnu".
Type "show configuration" for configuration details.
For bug reporting instructions, please see:
<http://www.gnu.org/software/gdb/bugs/>.
Find the GDB manual and other documentation resources online at:
<http://www.gnu.org/software/gdb/documentation/>.
For help, type "help".
Type "apropos word" to search for commands related to "word".
```

## qemuとgdb

qemuはgdbserverという機能を持っていて、qemuの上で動作するプログラムをリモートからgdbでデバッグすることができる。

次のように`-s`を指定することで`localhost:1234`でgdbserverへの接続を待ち受ける。
また、`-S`を指定するとqemuの起動直後でプログラムの実行を停止する。

```
$ qemu-system-i386 -s -S -nographic

```

ここで、別の端末からgdbを起動して`target remote localhost:1234`コマンドを実行することでリモートからqemu上のプログラムをデバッグできる。

```
$ gdb
...
(gdb) target remote localhost:1234
Remote debugging using localhost:1234
warning: No executable has been specified and target does not support
determining executable automatically.  Try using the "file" command.
0x0000fff0 in ?? ()
(gdb) info registers 
eax            0x0                 0
ecx            0x0                 0
edx            0x663               1635
ebx            0x0                 0
esp            0x0                 0x0
ebp            0x0                 0x0
esi            0x0                 0
edi            0x0                 0
eip            0xfff0              0xfff0
eflags         0x2                 [ IOPL=0 ]
cs             0xf000              61440
ss             0x0                 0
ds             0x0                 0
es             0x0                 0
fs             0x0                 0
gs             0x0                 0
fs_base        0x0                 0
gs_base        0x0                 0
k_gs_base      0x0                 0
cr0            0x60000010          [ CD NW ET ]
cr2            0x0                 0
cr3            0x0                 [ PDBR=0 PCID=0 ]
cr4            0x0                 [ ]
cr8            0x0                 0
```

## リアルモード

qemuを起動した直後(コンピュータの電源をONにした直後)のCPUはリアルモードと呼ばれる8086互換環境(16bit CPU)として動作する。
BIOSとブートローダの最初の部分はこのモードで実行され、ハードウェアの初期化などを実行したあとプロテクトモード(32bit CPU)へ移行する。

8086のアドレスバスは20bitだったので、リアルモードのアドレス空間は`0x00000`から`0xfffff`までの1MBの大きさになる。
CPUからのメモリへのアクセスは下に示すように、セグメントベースにオフセット値を加えたリニアアドレスによって指定される。

```
  リニアアドレス = セグメントベース + オフセット
```

8086ではセグメントベースをセグメントレジスタ(CS,DSなど)によって指し示す。
しかし、8086のレジスタは16bitなのでそのままだと20bitのアドレス空間のすべてにアクセスすることはできない。
そこで、8086ではセグメントレジスタを4bit左にシフトしてからオフセットを加算する。

```
  リニアアドレス = セグメントベース << 4 + オフセット
```

例えば、先程のqemuを起動した直後のレジスタ状態を見ると`EIP`と`CS`レジスタは以下の値になっている。

```
eip            0xfff0
cs             0xf000
```

そのため、このときのCPUが実行する命令のアドレスは`0xffff0`になる。

```
  0xffff0 = 0xf000 << 4 + 0xfff0
```

## リセットベクタ

コンピュータの電源をONにした直後のCPUは先程示したように決められたアドレス(`0xffff0`)から命令を実行しようとする。
このアドレスをリセットベクタと呼びCPUアーキテクチャごとに異なる。

例：https://en.wikipedia.org/wiki/Reset_vector

リセットベクタが指すアドレスはROMの領域にあり、BIOSのコードの先頭へジャンプする命令が置かれている。

実際にqemu+gdbを使ってリセットベクタの位置の命令を見てみる。
ただ、gdbはリアルモードのアドレス指定(4bit左シフト)に対応していないみたいで若干使いづらいので以下のgdbスクリプトを使う。

gdbスクリプト：
https://github.com/mhugo/gdb_init_real_mode

gdb起動時に`-ix`でスクリプトを指定してあげるとリアルモード向けの見やすい表示がされるようになる。

```
$ gdb -ix gdb_init_real_mode/gdbinit_real_mode.txt 
...
warning: A handler for the OS ABI "GNU/Linux" is not built into this configuration
of GDB.  Attempting to continue with the default i8086 settings.

The target architecture is assumed to be i8086
real-mode-gdb$ targe remote localhost:1234  # gdbserverに接続
Remote debugging using localhost:1234
warning: No executable has been specified and target does not support
determining executable automatically.  Try using the "file" command.
---------------------------[ STACK ]---
0000 0000 0000 0000 0000 0000 0000 0000 
0000 0000 0000 0000 0000 0000 0000 0000 
---------------------------[ DS:SI ]---
00000000: 00 00 00 00 00 00 00 00 00 00 00 00 00 00 00 00  ................
00000010: 00 00 00 00 00 00 00 00 00 00 00 00 00 00 00 00  ................
00000020: 00 00 00 00 00 00 00 00 00 00 00 00 00 00 00 00  ................
00000030: 00 00 00 00 00 00 00 00 00 00 00 00 00 00 00 00  ................
---------------------------[ ES:DI ]---
00000000: 00 00 00 00 00 00 00 00 00 00 00 00 00 00 00 00  ................
00000010: 00 00 00 00 00 00 00 00 00 00 00 00 00 00 00 00  ................
00000020: 00 00 00 00 00 00 00 00 00 00 00 00 00 00 00 00  ................
00000030: 00 00 00 00 00 00 00 00 00 00 00 00 00 00 00 00  ................
----------------------------[ CPU ]----
AX: 0000 BX: 0000 CX: 0000 DX: 0663
SI: 0000 DI: 0000 SP: 0000 BP: 0000
CS: F000 DS: 0000 ES: 0000 SS: 0000

IP: FFF0 EIP:0000FFF0
CS:IP: F000:FFF0 (0xFFFF0)
SS:SP: 0000:0000 (0x00000)
SS:BP: 0000:0000 (0x00000)
OF <0>  DF <0>  IF <0>  TF <0>  SF <0>  ZF <0>  AF <0>  PF <0>  CF <0>
ID <0>  VIP <0> VIF <0> AC <0>  VM <0>  RF <0>  NT <0>  IOPL <0>
---------------------------[ CODE ]----
   0xffff0:     jmp    0xf000:0xe05b
   0xffff5:     xor    BYTE PTR ds:0x322f,dh
   0xffff9:     xor    bp,WORD PTR [bx]
   0xffffb:     cmp    WORD PTR [bx+di],di
   0xffffd:     add    ah,bh
   0xfffff:     add    BYTE PTR [bx+si],al
   0x100001:    add    BYTE PTR [bx+si],al
   0x100003:    add    BYTE PTR [bx+si],al
   0x100005:    add    BYTE PTR [bx+si],al
   0x100007:    add    BYTE PTR [bx+si],al
0x0000fff0 in ?? ()
real-mode-gdb$ 
```

リセットベクタ(`0xffff0`)の命令は以下のように`0xfe05b`へジャンプすることがわかる。

```
---------------------------[ CODE ]----
   0xffff0:     jmp    0xf000:0xe05b
```

`ni`コマンドで１命令実行した結果は以下のようになる。

```
real-mode-gdb$ ni
---------------------------[ STACK ]---
0000 0000 0000 0000 0000 0000 0000 0000 
0000 0000 0000 0000 0000 0000 0000 0000 
---------------------------[ DS:SI ]---
00000000: 00 00 00 00 00 00 00 00 00 00 00 00 00 00 00 00  ................
00000010: 00 00 00 00 00 00 00 00 00 00 00 00 00 00 00 00  ................
00000020: 00 00 00 00 00 00 00 00 00 00 00 00 00 00 00 00  ................
00000030: 00 00 00 00 00 00 00 00 00 00 00 00 00 00 00 00  ................
---------------------------[ ES:DI ]---
00000000: 00 00 00 00 00 00 00 00 00 00 00 00 00 00 00 00  ................
00000010: 00 00 00 00 00 00 00 00 00 00 00 00 00 00 00 00  ................
00000020: 00 00 00 00 00 00 00 00 00 00 00 00 00 00 00 00  ................
00000030: 00 00 00 00 00 00 00 00 00 00 00 00 00 00 00 00  ................
----------------------------[ CPU ]----
AX: 0000 BX: 0000 CX: 0000 DX: 0663
SI: 0000 DI: 0000 SP: 0000 BP: 0000
CS: F000 DS: 0000 ES: 0000 SS: 0000

IP: E05B EIP:0000E05B
CS:IP: F000:E05B (0xFE05B)
SS:SP: 0000:0000 (0x00000)
SS:BP: 0000:0000 (0x00000)
OF <0>  DF <0>  IF <0>  TF <0>  SF <0>  ZF <0>  AF <0>  PF <0>  CF <0>
ID <0>  VIP <0> VIF <0> AC <0>  VM <0>  RF <0>  NT <0>  IOPL <0>
---------------------------[ CODE ]----
   0xfe05b:     cmp    DWORD PTR cs:0x70c8,0x0
   0xfe062:     jne    0xfd414
   0xfe066:     xor    dx,dx
   0xfe068:     mov    ss,dx
   0xfe06a:     mov    esp,0x7000
   0xfe070:     mov    edx,0xf2d4e
   0xfe076:     jmp    0xfff00
   0xfe079:     push   ebp
   0xfe07b:     push   edi
   0xfe07d:     push   esi
0x0000e05b in ?? ()
real-mode-gdb$ 
```

qemuがリセットベクタに配置しているBIOSプログラムファイルは`info roms`で調べることができる。
デフォルトだと`bios-256k.bin`を読み込んでいるように見える。（アドレスの位置が`0xfffc0000`なのは何故？）

```
$ qemu-system-i386 -s -S -nographic
QEMU 2.8.1 monitor - type 'help' for more information
(qemu) info roms
fw=genroms/kvmvapic.bin size=0x002400 name="kvmvapic.bin"
addr=00000000fffc0000 size=0x040000 mem=rom name="bios-256k.bin"
/rom@etc/acpi/tables size=0x200000 name="etc/acpi/tables"
/rom@etc/table-loader size=0x001000 name="etc/table-loader"
/rom@etc/acpi/rsdp size=0x000024 name="etc/acpi/rsdp"
(qemu) 
```

qemuが読み込むBIOSプログラムファイルの場所は`-L help`で調べることができる。

```
$ qemu-system-i386 -L help
/usr/share/qemu
/usr/share/seabios
/usr/lib/ipxe/qemu
$ qemu-system-i386 -L help | xargs ls
/usr/lib/ipxe/qemu:
efi-e1000.rom     efi-ne2k_pci.rom  efi-rtl8139.rom  pxe-e1000.rom     pxe-ne2k_pci.rom  pxe-rtl8139.rom
efi-eepro100.rom  efi-pcnet.rom     efi-virtio.rom   pxe-eepro100.rom  pxe-pcnet.rom     pxe-virtio.rom

/usr/share/qemu:
keymaps  qemu-icon.bmp  qemu_logo_no_text.svg  trace-events-all

/usr/share/seabios:
acpi-dsdt.aml  extboot.bin    linuxboot_dma.bin  q35-acpi-dsdt.aml   vgabios-isavga.bin  vgabios-virtio.bin
bios-256k.bin  kvmvapic.bin   multiboot.bin      vapic.bin           vgabios-qxl.bin     vgabios-vmware.bin
bios.bin       linuxboot.bin  optionrom          vgabios-cirrus.bin  vgabios-stdvga.bin
```

`bios-256k.bin`の中身はobjdumpで見ることができる。

```
$ objdump -D -b binary -m i8086 /usr/share/seabios/bios-256k.bin | less

/usr/share/seabios/bios-256k.bin:     file format binary


Disassembly of section .data:

00000000 <.data>:
        ...
   18ae0:       f1                      icebp  
   18ae1:       02 00                   add    (%bx,%si),%al
   18ae3:       00 4b 03                add    %cl,0x3(%bp,%di)
   18ae6:       00 00                   add    %al,(%bx,%si)
   18ae8:       52                      push   %dx
...
```

リセットベクタの位置に当たる命令は以下の場所にあった。
（`0xffff0`と異なる位置にあるのでqemuがこのファイルをロードするときによしなにしてくれるのだと思う）

```
   3fff0:       ea 5b e0 00 f0          ljmp   $0xf000,$0xe05b
   3fff5:       30 36 2f 32             xor    %dh,0x322f
   3fff9:       33 2f                   xor    (%bx),%bp
   3fffb:       39 39                   cmp    %di,(%bx,%di)
   3fffd:       00 fc                   add    %bh,%ah
```

# 参考文献
- 新装改訂版　Linuxのブートプロセスをみる (アスキー書籍), 白崎 博生 
- linux-insides, https://0xax.gitbooks.io/linux-insides/
- stackoverflow - How to disassemble 16-bit x86 boot sector code in GDB with “x/i $pc”? It gets treated as 32-bit, https://stackoverflow.com/questions/32955887/how-to-disassemble-16-bit-x86-boot-sector-code-in-gdb-with-x-i-pc-it-gets-tr
