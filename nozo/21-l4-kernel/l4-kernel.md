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

暗黙の型変換(narrowing conversion)でエラーが出たので、`-Wno-narrowing`を追加する。

```diff
diff --git a/kernel/Mk/Makeconf b/kernel/Mk/Makeconf
index 9f899a8..754a5d8 100644
--- a/kernel/Mk/Makeconf
+++ b/kernel/Mk/Makeconf
@@ -169,7 +169,7 @@ VFLAGS =
 
 # use optimization level of at least 1 - otherwise inlining will fail
 CCFLAGS += -fno-rtti -fno-builtin  -fomit-frame-pointer -fno-exceptions \
-         -Wall -Wno-non-virtual-dtor -Wno-format   \
+         -Wall -Wno-non-virtual-dtor -Wno-format -Wno-narrowing \
          $(CFLAGS_$(ARCH)) $(CFLAGS_$(CPU)) $(CFLAGS_$(PLATFORM)) 
 
 ifeq ("$(CC_VERSION)", "4")
```

```
$ make
-snip-
===> Linking x86-kernel
ld  -static -O2 -melf_i386  -L/usr/lib/gcc/x86_64-linux-gnu/8/ -static -O2 -melf_i386  -L/usr/lib/gcc/x86_64-linux-gnu/8/   -Tlds.tmp -o x86-kernel  src/glue/v4-x86/x32/init.o  src/glue/v4-x86/x32/exception.o  src/glue/v4-x86/x32/space.o  src/glue/v4-x86/x32/user.o  src/glue/v4-x86/x32/thread.o src/glue/v4-x86/x32/trap.o src/glue/v4-x86/x32/trampoline.o  src/glue/v4-x86/x32/memcontrol.o  src/generic/linear_ptab_walker.o  src/generic/mapping_alloc.o  src/generic/mapping.o  kdb/arch/x86/x32/x86.o  kdb/generic/linear_ptab_dump.o  kdb/generic/mapping.o  kdb/glue/v4-x86/x32/space.o  src/generic/lib.o  src/generic/kmemory.o src/platform/pc99/startup.o  src/platform/generic/intctrl-pic.o  src/api/v4/exregs.o  src/api/v4/ipc.o  src/api/v4/ipcx.o  src/api/v4/kernelinterface.o  src/api/v4/thread.o  src/api/v4/schedule.o  src/api/v4/space.o  src/api/v4/interrupt.o  src/api/v4/smp.o  src/api/v4/processor.o  src/api/v4/sched-rr/schedule.o  src/glue/v4-x86/ctors.o  src/glue/v4-x86/exception.o  src/glue/v4-x86/space.o  src/glue/v4-x86/init.o  src/glue/v4-x86/resources.o  src/glue/v4-x86/idt.o  src/glue/v4-x86/debug.o  src/glue/v4-x86/cpu.o  src/glue/v4-x86/thread.o  src/glue/v4-x86/timer.o  kdb/generic/bootinfo.o  kdb/generic/cmd.o  kdb/generic/console.o  kdb/generic/entry.o  kdb/generic/init.o  kdb/generic/input.o  kdb/generic/kmemory.o  kdb/generic/linker_set.o  kdb/generic/memdump.o  kdb/generic/print.o  kdb/generic/tid_format.o  kdb/generic/tracepoints.o  kdb/platform/pc99/io.o  kdb/platform/pc99/intctrl.o  kdb/api/v4/input.o  kdb/api/v4/kernelinterface.o  kdb/api/v4/tcb.o  kdb/api/v4/thread.o  kdb/api/v4/schedule-rr.o  kdb/api/v4/sigma0.o  kdb/arch/x86/breakpoints.o  kdb/arch/x86/stepping.o  kdb/arch/x86/x86.o  kdb/glue/v4-x86/thread.o  kdb/glue/v4-x86/prepost.o  kdb/glue/v4-x86/readmem.o  kdb/glue/v4-x86/resources.o  kdb/glue/v4-x86/addrtranslation.o -lgcc
ld: skipping incompatible /usr/lib/gcc/x86_64-linux-gnu/8//libgcc.a when searching for -lgcc
ld: skipping incompatible /usr/lib/gcc/x86_64-linux-gnu/8//libgcc.a when searching for -lgcc
ld: cannot find -lgcc
make[1]: *** [/home/nozo/pistachio/kernel/Mk/Makeconf:258: x86-kernel] Error 1
make[1]: Leaving directory '/home/nozo/pistachio/x86-kernel-build'
make: *** [Makefile:38: all] Error 2
```

# 参考
- L4Ka Project, https://www.l4ka.org/
- L4Ka::Pistachio micro-kernel -github-, https://github.com/l4ka/pistachio
