# eBPF

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

# 参考
- https://ebpf.io/
- bcc Tutorial, https://github.com/iovisor/bcc/blob/master/docs/tutorial.md
- eBPFに3日で入門した話, https://caddi.tech/archives/3880
- eBPF - 入門概要 編, https://zenn.dev/hidenori3/articles/e1352e8cfeb2af
- Berkeley Packet Filter（BPF）入門, https://atmarkit.itmedia.co.jp/ait/series/11804/
