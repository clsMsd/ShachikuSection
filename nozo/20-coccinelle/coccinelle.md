# Coccinelleについて調査

[Development tools for the kernel](https://www.kernel.org/doc/html/latest/dev-tools/index.html)の一覧にあるツールについて調べる。

今回は一番上にあるCoccinelleというツールについて。

## 実験環境

```
$ uname -a
Linux instance-1 4.9.0-12-amd64 #1 SMP Debian 4.9.210-1 (2020-01-20) x86_64 GNU/Linux

$ apt install coccinelle
$ spatch --version
spatch version 1.0.4 with Python support and with PCRE support
```

## 概要

Coccinelleとは、SmPLという言語で書かれたスクリプトで

Cプログラムのバグを静的に解析するツールである。

> Coccinelle is a program matching and transformation engine which provides the language SmPL (Semantic Patch Language) for specifying desired matches and transformations in C code.
> 
> http://coccinelle.lip6.fr/

Coccinelleが見つけることができるバグの簡単な例を示す。

例：[wmi: (!x & y) strikes again](https://git.kernel.org/pub/scm/linux/kernel/git/torvalds/linux.git/commit/?id=e6bafba5b4765a5a252f1b8d31cbf6d2459da337)

このパッチは、～という問題を修正するものである。

```diff
diff --git a/drivers/acpi/wmi.c b/drivers/acpi/wmi.c
index 457ed3d..efacc9f 100644
--- a/drivers/acpi/wmi.c
+++ b/drivers/acpi/wmi.c
@@ -247,7 +247,7 @@ u32 method_id, const struct acpi_buffer *in, struct acpi_buffer *out)
 	block = &wblock->gblock;
 	handle = wblock->handle;
 
-	if (!block->flags & ACPI_WMI_METHOD)
+	if (!(block->flags & ACPI_WMI_METHOD))
 		return AE_BAD_DATA;
 
 	if (block->instance_count < instance)
```

同じように`(!x & y)`という形になってしまっているプログラムが他にないか調べようとしても、grepとかだと`!`や`&`という記号がプログラムのいたるところにあるため検索しづらい。

ConccilleではSmPLという記法を使って`(!x & y)`のようなパターンにマッチして書き換える記述が可能である。

```
@@
expression E;
constant C;
@@
- !E & C
+ !(E & C)
```

上のスクリプトを`ex1.cocci`として保存して次のように`spatch`を実行するとパッチが生成される。

※ 実験のためわざと`linux-5.5.8/drivers/platform/x86/wmi.c`にバグを仕込んだ。

```
$ spatch --sp-file ex1.cocci --dir ~/linux-5.5.8/drivers/platform/x86/wmi.c 
init_defs_builtins: /usr/lib/coccinelle/standard.h
HANDLING: /home/nozo/linux-5.5.8/drivers/platform/x86/wmi.c
diff = 
--- /home/nozo/linux-5.5.8/drivers/platform/x86/wmi.c
+++ /tmp/cocci-output-21639-0090f6-wmi.c
@@ -263,7 +263,7 @@ acpi_status wmidev_evaluate_method(struc
        block = &wblock->gblock;
        handle = wblock->acpi_device->handle;
 
-       if (!block->flags & ACPI_WMI_METHOD)
+       if (!(block->flags & ACPI_WMI_METHOD))
                return AE_BAD_DATA;
 
        if (block->instance_count <= instance)
```

- testing for unsigned variables for values less than zero or null pointer dereferencing
- double locks or using the iterator index after a loop
- API-specific errors (using free() on a devm allocation)
- API modernization (using kmemdup() rather than kmalloc() and memcpy())

```
$ ls linux-5.5.8/scripts/coccinelle/
api  free  iterators  locks  misc  null  tests
```

# 参考
- Development tools for the kernel » Coccinelle, https://www.kernel.org/doc/html/latest/dev-tools/coccinelle.html
- KernelNewbies: JuliaLawall, https://kernelnewbies.org/JuliaLawall
- Keynote: Inside the Mind of a Coccinelle Programmer by Julia Lawall, Developer of Coccinelle, https://youtu.be/xA5FBvuCvMs
- Inside the mind of a Coccinelle programmer, https://lwn.net/Articles/698724/
