# カーネル解析ツールSystemTapの紹介
SystemTapはアプリケーションを動的に解析することができるツールでLinuxカーネルの動作を詳しく観察したりすることができる。
用途としてはパフォーマンスの解析などに使われ、システムのボトルネックを特定したりする。

実行環境
```
$ uname -a
Linux fluorite 4.9.0-8-amd64 #1 SMP Debian 4.9.110-3+deb9u6 (2018-10-08) x86_64 GNU/Linux
$ stap --version
Systemtap translator/driver (version 3.1/0.168, Debian version 3.1-2)
Copyright (C) 2005-2017 Red Hat, Inc. and others
This is free software; see the source for copying conditions.
tested kernel versions: 2.6.18 ... 4.10-rc8
enabled features: AVAHI LIBSQLITE3 NLS NSS
```

## SystemTapスクリプト
SystemTapはユーザーが作成するスクリプトを実行するだけでカーネルの解析が可能で、カーネル本体のコードをいじったりして再コンパイルしなくてよい。

SystemTapのスクリプトは次のように書ける。
```
probe begin
{
  print ("hello world\n")
  exit ()
}
```
実行はstapコマンドを使う。
```
# stap hello.stp 
hello world
```

スクリプトはプローブと呼ばれるシステムのイベントと、そのイベントが発生したときに実行する処理を記述する。
プローブの例を以下に示す。
(詳細は[stapprobesのmanページ](https://sourceware.org/systemtap/man/stapprobes.3stap.html)を参照)

| Probe | 説明 |
| ---: | --- |
| begin | systemtapスクリプトの開始時 |
| end | systemtapスクリプトの終了時 |
| kernel.function("sys_open") | カーネル関数 sys_open が呼ばれたとき |
| syscall.close.return | システムコール close から return したとき |
| module("ext3").statement(0xdeadbeef) | ファイルシステムドライバ ext3 の指定したアドレスの命令が実行されたとき |
| timer.ms(200) | 200 ms ごとに |
| perf.hw.cache_misses | CPUのキャッシュミスが特定回数発生したとき |
| process("a.out").statement("*@main.c:200") | プログラム a.out の200行目が実行されたとき |

また、スクリプト中で使える関数などは`/usr/share/systemtap/tapset/`以下にtapsetライブラリとして提供されている。
tapsetの例を以下に示す。
(詳細は[manページ](https://sourceware.org/systemtap/man/)の`function::*`を参照)

| Function | 説明 |
| ---: | --- |
| tid() | スレッドID |
| pid() | プロセスID |
| uid() | ユーザーID |
| execname() | プロセスの名前 |
| cpu() | 実行しているCPUの番号 |
| gettimeofday_s() | エポック秒 |
| pp() | 現在のプローブポイントの文字列 |
| ppfunc() | 現在のプローブポイントが置かれた関数の名前 |
| $$vars | すべてのローカル変数のリストの表示 |
| print_backtrace() | カーネル空間バックトレースの表示 |
| print_ubacktrace() | ユーザー空間バックトレースの表示 |

例えば各プロセスが何回`syscall`を呼び出したか統計するスクリプトは以下のように書ける。
```
global counts

probe syscall.*
{
  counts[execname()] ++
}

probe end
{
  printf("==TOTAL==\n")
  foreach (name in counts)
    printf("%s : %d \n", name, counts[name])
}
```

実行結果は以下のようになる。
```
$ sudo stap -v count.stp 
Pass 1: parsed user script and 465 library scripts using 113932virt/46648res/6364shr/40580data kb, in 160usr/50sys/756real ms.
Pass 2: analyzed script: 535 probes, 28 functions, 102 embeds, 4 globals using 298140virt/232556res/7776shr/224788data kb, in 15500usr/440sys/21446real ms.
Pass 3: translated to C into "/tmp/stap0LYOZz/stap_03aca4461276e8e31c50da07ae0fdded_327031_src.c" using 298140virt/230292res/5508shr/224788data kb, in 50usr/240sys/2066real ms.
Pass 4: compiled C into "stap_03aca4461276e8e31c50da07ae0fdded_327031.ko" in 4840usr/480sys/12367real ms.
Pass 5: starting run.
^C==TOTAL==
stapio : 384 
google_network_ : 64 
ip : 68 
ntpd : 42 
google_clock_sk : 17 
sshd : 26 
stap : 5 
sudo : 2 
Pass 5: run completed in 0usr/2120sys/24243real ms.
```

## サンプルスクリプト
[Exampleページ](https://www.sourceware.org/systemtap/examples/keyword-index.html)にたくさんのSystemTapスクリプトがあるのでいくつか紹介する。

### 変数の監視
以下のプログラムは第１引数にプローブが渡され、第２引数で指定された種類の変数リストを表示するスクリプトである。
`$1`や`$2`はシェルスクリプトと同じようにスクリプトの引数を表す。
```
#! /usr/bin/env stap

global var, varerr

probe $1 {
  if (@defined($2)) {
     try {
         newvar = $2;
         if (var[tid()] != newvar) {
            printf("%s[%d] %s %s:\n", execname(), tid(), pp(), @2);
            println(newvar);
            var[tid()] = newvar;
         }
     } catch { varerr ++ }  # error during $2 resolution or perhaps var[] assignment
  }
}

probe kprocess.release { # if using per-thread checking
  delete var[$p->pid] # thread
}

probe never {
  var[0]=""  # assigns a type to var in case no probes match $1 above
}

probe error,end {
  if (varerr) printf("%s %s access errors: %d", @1, @2, varerr);
}
```

例えば第１引数に`'kernel.function("sys_*@fs/open.c:*")'`を、第２引数に`'$$parms'`を渡したときの実行結果は以下のようになる。
```
$ sudo stap -w varwatch.stp 'kernel.function("sys_*@fs/open.c:*")' '$$parms' -c "ls > /dev/null
sh[3870] kernel.function("SyS_access@./fs/open.c:431") $$parms:
filename=0x7f6bd24a35aa mode=0x0
sh[3870] kernel.function("SyS_access@./fs/open.c:431") $$parms:
filename=0x7f6bd24a5d30 mode=0x4
sh[3870] kernel.function("SyS_open@./fs/open.c:1074") $$parms:
filename=0x7f6bd24a3a49 flags=0x80000 mode=0x1
sh[3870] kernel.function("SyS_close@./fs/open.c:1135") $$parms:
fd=0x3
sh[3870] kernel.function("SyS_access@./fs/open.c:431") $$parms:
filename=0x7f6bd24a35aa mode=0x0
sh[3870] kernel.function("SyS_open@./fs/open.c:1074") $$parms:
filename=0x7f6bd26a74a0 flags=0x80000 mode=0x7f6bd26ab170
sh[3870] kernel.function("SyS_close@./fs/open.c:1135") $$parms:
fd=0x3
sh[3870] kernel.function("SyS_open@./fs/open.c:1074") $$parms:
filename=0x559c01b42b78 flags=0x241 mode=0x1b6
sh[3870] kernel.function("SyS_close@./fs/open.c:1135") $$parms:
fd=0x1
...
```

## 参考文献
- SystemTap, https://sourceware.org/systemtap/
- SYSTEMTAP ビギナーズガイド, https://access.redhat.com/documentation/ja-jp/red_hat_enterprise_linux/7/html-single/systemtap_beginners_guide/index
