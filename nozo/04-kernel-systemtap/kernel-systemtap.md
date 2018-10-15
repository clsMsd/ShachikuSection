# カーネル解析ツールSystemTapの紹介
SystemTapはアプリケーションを動的に解析することができるツールでLinuxカーネルの動作を詳しく観察したりすることができる。
用途としてはパフォーマンスの解析などに使われ、システムのボトルネックを特定したりする。

## SystemTapの仕組み
普通Linuxカーネルの動作を監視しようとするとカーネルの再コンパイルが必要となるが、SystemTapはユーザーが作成するスクリプトを実行するだけで解析が可能である。

| Probe | 説明 |
| ---: | --- |
| begin | The startup of the systemtap session. |
| end | The end of the systemtap session. |
| kernel.function("sys_open") | The entry to the function named sys_open in the kernel. |
| syscall.close.return | The return from the close system call. |
| module("ext3").statement(0xdeadbeef) | The addressed instruction in the ext3 filesystem driver. |
| timer.ms(200) | A timer that fires every 200 milliseconds. |
| timer.profile | A timer that fires periodically on every CPU. |
| perf.hw.cache_misses | A particular number of CPU cache misses have occurred. |
| procfs("status").read | A process trying to read a synthetic file. |
| process("a.out").statement("*@main.c:200") | Line 200 of the a.out program |

| Function | 説明 |
| ---: | --- |
| tid() | The id of the current thread. |
| pid() | The process (task group) id of the current thread. |
| uid() | The id of the current user. |
| execname() | The name of the current process. |
| cpu() | The current cpu number. |
| gettimeofday_s() | Number of seconds since epoch. |
| get_cycles() | Snapshot of hardware cycle counter. |
| pp() | A string describing the probe point being currently handled. |
| ppfunc() | If known, the the function name in which this probe was placed. |
| $$vars | If available, a pretty-printed listing of all local variables in scope. |
| print_backtrace() | If possible, print a kernel backtrace. |
| print_ubacktrace() | If possible, print a user-space backtrace. |

## 参考文献
- SystemTap, https://sourceware.org/systemtap/
