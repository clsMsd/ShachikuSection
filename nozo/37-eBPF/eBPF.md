# eBPF

> eBPFは、Linuxカーネルを起源とする、OSカーネルのような特権的なコンテキストでサンドボックス化されたプログラムを実行できる画期的な技術です。カーネルのソースコードを変更したり、カーネルモジュールをロードしたりすることなく、安全かつ効率的にカーネルの機能を拡張するために使用されます。
> 
> eBPF is a revolutionary technology with origins in the Linux kernel that can run sandboxed programs in a privileged context such as the operating system kernel. It is used to safely and efficiently extend the capabilities of the kernel without requiring to change kernel source code or load kernel modules.
> 
> https://ebpf.io/what-is-ebpf, What is eBPF?

eBPFは以下のような用途で使える。

* Security
: システムコールフィルタリング、ネットワークレベルフィルタリング
* Tracing & Profiling
: カーネル、ユーザーアプリケーションのトレース
* Networking
: 低オーバーヘッドなパケット処理
* Observability & Monitoring
: パフォーマンスモニタリング、トラブルシューティング

eBPFプログラムを作成・実行する流れは以下のようになる。
Cで記述したeBPFプログラムをバイトコードにコンパイルして、eBPFライブラリを通してカーネルにロードする。
ロードするとき検証機によってeBPFプログラムは安全性(クラッシュしたり、システムに損害を与えないこと)を検証される。
ロードされたeBPFプログラムは、システムコール、カーネル関数の入口/出口、トレースポイント、ネットワークイベントなどを起点にカーネルのeBPFラインタイム上で実行される。

> ![](./img/ebpf00.png)
> 
> https://ebpf.io/what-is-ebpf, Loader & Verification Architecture

eBPFプログラムの開発には以下のようなツール・ライブラリが使われる。

* bcc
* bpftrace
* libbpf/libbpfgo

例えばbccはeBPFプログラムを埋め込んだPythonプログラムを作成できるようにするフレームワークで、以下のようにeBPFプログラムを記述できる。

```python
#!/usr/bin/python
# Copyright (c) PLUMgrid, Inc.
# Licensed under the Apache License, Version 2.0 (the "License")

# run in project examples directory with:
# sudo ./hello_world.py"
# see trace_fields.py for a longer example

from bcc import BPF

# This may not work for 4.17 on x64, you need replace kprobe__sys_clone with kprobe____x64_sys_clone
BPF(text='int kprobe__sys_clone(void *ctx) { bpf_trace_printk("Hello, World!\\n"); return 0; }').trace_print()
```
https://github.com/iovisor/bcc/blob/master/examples/hello_world.py

このプログラムを実行すると、cloneシステムコールが呼ばれるたびに"Hello, World!"と出力する。

```
$ sudo python3 ./hello_world.py
b'            sshd-48936   [000] d...1 403756.493674: bpf_trace_printk: Hello, World!'
b''
b'            sshd-75740   [000] d...1 403756.505976: bpf_trace_printk: Hello, World!'
b''
b'            bash-75709   [001] d...1 403757.806359: bpf_trace_printk: Hello, World!'
b''
b'            bash-75742   [000] d...1 403757.809307: bpf_trace_printk: Hello, World!'
...
```


# 参考
- https://ebpf.io/
- bcc Tutorial, https://github.com/iovisor/bcc/blob/master/docs/tutorial.md
- eBPFに3日で入門した話, https://caddi.tech/archives/3880
- eBPF - 入門概要 編, https://zenn.dev/hidenori3/articles/e1352e8cfeb2af
- Berkeley Packet Filter（BPF）入門, https://atmarkit.itmedia.co.jp/ait/series/11804/
