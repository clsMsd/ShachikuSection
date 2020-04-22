# L4カーネル

[Getting Started with L4Ka::Pistachio on x86-x32](https://www.l4ka.org/120.php)

```
$ git clone https://github.com/l4ka/pistachio.git
$ ls pistachio/
AUTHORS  README  contrib  doc  kernel  tools  user
```

```
$ cd pistachio/kernel/
$ make BUILDDIR=$(pwd)/../x86-kernel-build
$ cd ../x86-kernel-build/
$ make menuconfig  # デフォルト設定で保存
$ make
-snip-
/home/nozo/pistachio/kernel/src/api/v4/kernelinterface.cc: At global scope:
/home/nozo/pistachio/kernel/src/api/v4/kernelinterface.cc:131:1: error: narrowing conversion of ‘230’ from ‘int’ to ‘char’ inside { } [-Wnarrowing]
 };
 ^
make[1]: *** [/home/nozo/pistachio/kernel/Mk/Makeconf:208: src/api/v4/kernelinterface.o] Error 1
make[1]: Leaving directory '/home/nozo/pistachio/x86-kernel-build'
make: *** [Makefile:38: all] Error 2
```

# 参考
- L4Ka Project, https://www.l4ka.org/
- L4Ka::Pistachio micro-kernel -github-, https://github.com/l4ka/pistachio
