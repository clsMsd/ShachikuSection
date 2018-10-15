# カーネル解析ツールSystemTapの紹介
SystemTapはアプリケーションを動的に解析することができるツールでLinuxカーネルの動作を詳しく観察したりすることができる。
用途としてはパフォーマンスの解析などに使われ、システムのボトルネックを特定したりする。

## SystemTapの仕組み
普通Linuxカーネルの動作を監視しようとするとカーネルの再コンパイルが必要となるが、SystemTapはユーザーが作成するスクリプトを実行するだけで解析が可能である。

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

## 参考文献
- SystemTap, https://sourceware.org/systemtap/
