# qemuでBIOSをデバッグする

ブートプロセスの挙動を追うために、qemuでBIOSをデバッグする手法を調査する。

## 実験環境

```
$ uname -r
5.5.2-arch1-1
$ qemu-system-x86_64 --version
QEMU emulator version 4.2.0
Copyright (c) 2003-2019 Fabrice Bellard and the QEMU Project developers
$ gdb --version
GNU gdb (GDB) 8.3.1
Copyright (C) 2019 Free Software Foundation, Inc.
License GPLv3+: GNU GPL version 3 or later <http://gnu.org/licenses/gpl.html>
This is free software: you are free to change and redistribute it.
There is NO WARRANTY, to the extent permitted by law.
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

例えば、qemuを起動した直後のレジスタ状態を見ると`EIP`と`CS`レジスタは以下の値になっている。

```
eip            0xfff0
cs             0xf000
```

そのため、このときのCPUが実行する命令のアドレスは`0xffff0`になる。

```
  0xffff0 = 0xf000 << 4 + 0xfff0
```


gdbスクリプト：
https://github.com/mhugo/gdb_init_real_mode


```
# qemu-system-i386 -s -S -nographic
```

```
# gdb -ix gdbinit_real_mode.txt
GNU gdb (GDB; SUSE Linux Enterprise 15) 8.3.1
Copyright (C) 2019 Free Software Foundation, Inc.
License GPLv3+: GNU GPL version 3 or later <http://gnu.org/licenses/gpl.html>
This is free software: you are free to change and redistribute it.
There is NO WARRANTY, to the extent permitted by law.
Type "show copying" and "show warranty" for details.
This GDB was configured as "x86_64-suse-linux".
Type "show configuration" for configuration details.
For bug reporting instructions, please see:
<http://bugs.opensuse.org/>.
Find the GDB manual and other documentation resources online at:
    <http://www.gnu.org/software/gdb/documentation/>.

For help, type "help".
Type "apropos word" to search for commands related to "word".

warning: A handler for the OS ABI "GNU/Linux" is not built into this configuration
of GDB.  Attempting to continue with the default i8086 settings.

The target architecture is assumed to be i8086
real-mode-gdb$ target remote localhost:1234
Remote debugging using localhost:1234
warning: Remote gdbserver does not support determining executable automatically.
RHEL <=6.8 and <=7.2 versions of gdbserver do not support such automatic executable detection.
The following versions of gdbserver support it:
- Upstream version of gdbserver (unsupported) 7.10 or later
- Red Hat Developer Toolset (DTS) version of gdbserver from DTS 4.0 or later (only on x86_64)
- RHEL-7.3 versions of gdbserver (on any architecture)
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
   0xffff0:     jmp    0x3630:0xf000e05b
   0xffff7:     das
   0xffff8:     xor    dh,BYTE PTR [ebx]
   0xffffa:     das
   0xffffb:     cmp    DWORD PTR [ecx],edi
   0xffffd:     add    ah,bh
   0xfffff:     add    BYTE PTR [eax],al
   0x100001:    add    BYTE PTR [eax],al
   0x100003:    add    BYTE PTR [eax],al
   0x100005:    add    BYTE PTR [eax],al
0x0000fff0 in ?? ()
real-mode-gdb$
```


```
$ qemu-system-x86_64 -L help
/usr/share/qemu-firmware
/usr/share/qemu
```

# 参考文献
- 新装改訂版　Linuxのブートプロセスをみる (アスキー書籍), 白崎 博生 
- linux-insides, https://0xax.gitbooks.io/linux-insides/

- stackoverflow - How to disassemble 16-bit x86 boot sector code in GDB with “x/i $pc”? It gets treated as 32-bit
https://stackoverflow.com/questions/32955887/how-to-disassemble-16-bit-x86-boot-sector-code-in-gdb-with-x-i-pc-it-gets-tr


