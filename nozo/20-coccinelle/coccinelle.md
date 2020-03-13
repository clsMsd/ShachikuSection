# Coccinelleについて調査

[Development tools for the kernel](https://www.kernel.org/doc/html/latest/dev-tools/index.html)の一覧にあるツールについて調べる。
今回は一番上にあるCoccinelleというツールについて。

## 実験環境

```
$ uname -a
Linux instance-1 4.9.0-12-amd64 #1 SMP Debian 4.9.210-1 (2020-01-20) x86_64 GNU/Linux
$ spatch --version
spatch version 1.0.4 with Python support and with PCRE support
```

## 概要

Coccinelleとは、SmPLという言語で書かれたスクリプトで
Cプログラムのバグを静的に解析するツールである。

> Coccinelle is a program matching and transformation engine which provides the language SmPL (Semantic Patch Language) for specifying desired matches and transformations in C code.
> 
> http://coccinelle.lip6.fr/

例：

```
```

# 参考
- Development tools for the kernel » Coccinelle, https://www.kernel.org/doc/html/latest/dev-tools/coccinelle.html
- KernelNewbies: JuliaLawall, https://kernelnewbies.org/JuliaLawall
- Keynote: Inside the Mind of a Coccinelle Programmer by Julia Lawall, Developer of Coccinelle, https://youtu.be/xA5FBvuCvMs
- Inside the mind of a Coccinelle programmer, https://lwn.net/Articles/698724/
