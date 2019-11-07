# PCIデバイスへのアクセス

PCIデバイスにデバイスドライバからアクセスする方法を調査する。
実験環境はArchLinuxで下記のkernelバージョンで実施した。

```
$ uname -r
5.3.8-arch1-1
```

PCに接続されているPCIデバイスの一覧は次のように表示できる。

```
$ lspci | head
00:00.0 Host bridge: Advanced Micro Devices, Inc. [AMD] Family 17h (Models 00h-0fh) Root Complex
00:00.2 IOMMU: Advanced Micro Devices, Inc. [AMD] Family 17h (Models 00h-0fh) I/O Memory Management Unit
00:01.0 Host bridge: Advanced Micro Devices, Inc. [AMD] Family 17h (Models 00h-1fh) PCIe Dummy Host Bridge
00:01.3 PCI bridge: Advanced Micro Devices, Inc. [AMD] Family 17h (Models 00h-0fh) PCIe GPP Bridge
00:02.0 Host bridge: Advanced Micro Devices, Inc. [AMD] Family 17h (Models 00h-1fh) PCIe Dummy Host Bridge
00:03.0 Host bridge: Advanced Micro Devices, Inc. [AMD] Family 17h (Models 00h-1fh) PCIe Dummy Host Bridge
00:03.1 PCI bridge: Advanced Micro Devices, Inc. [AMD] Family 17h (Models 00h-0fh) PCIe GPP Bridge
00:04.0 Host bridge: Advanced Micro Devices, Inc. [AMD] Family 17h (Models 00h-1fh) PCIe Dummy Host Bridge
00:07.0 Host bridge: Advanced Micro Devices, Inc. [AMD] Family 17h (Models 00h-1fh) PCIe Dummy Host Bridge
00:07.1 PCI bridge: Advanced Micro Devices, Inc. [AMD] Family 17h (Models 00h-0fh) Internal PCIe GPP Bridge 0 to Bus B
```

あるいはカーネルが管理しているオブジェクトがマッピングされた疑似ファイルシステム sysfs からも一覧を見ることができる。

```
$ ls /sys/bus/pci/devices 
0000:00:00.0  0000:00:02.0  0000:00:07.0  0000:00:14.0  0000:00:18.2  0000:00:18.6  0000:03:00.2  0000:1d:06.0  0000:26:00.1  0000:28:00.0
0000:00:00.2  0000:00:03.0  0000:00:07.1  0000:00:14.3  0000:00:18.3  0000:00:18.7  0000:1d:00.0  0000:1d:07.0  0000:27:00.0  0000:28:00.2
0000:00:01.0  0000:00:03.1  0000:00:08.0  0000:00:18.0  0000:00:18.4  0000:03:00.0  0000:1d:01.0  0000:25:00.0  0000:27:00.2  0000:28:00.3
0000:00:01.3  0000:00:04.0  0000:00:08.1  0000:00:18.1  0000:00:18.5  0000:03:00.1  0000:1d:04.0  0000:26:00.0  0000:27:00.3
$ ls /sys/bus/pci/devices/0000:00:00.0/ 
ari_enabled           consistent_dma_mask_bits  dma_mask_bits    irq            msi_bus    rescan     subsystem_device
broken_parity_status  d3cold_allowed            driver_override  local_cpulist  numa_node  resource   subsystem_vendor
class                 device                    enable           local_cpus     power      revision   uevent
config                devspec                   firmware_node    modalias       remove     subsystem  vendor
```

PCIデバイスはドメインごとにバス番号、デバイス番号、ファンクション番号で識別される。

```
$ man lspci
...
   Options for selection of devices
       -s [[[[<domain>]:]<bus>]:][<device>][.[<func>]]
              Show only devices in the specified domain (in case your machine has several host bridges, they can either share a common bus
              number  space  or each of them can address a PCI domain of its own; domains are numbered from 0 to ffff), bus (0 to ff), de‐
              vice (0 to 1f) and function (0 to 7).  Each component of the device address can be omitted or set to "*", both meaning  "any
              value". All numbers are hexadecimal.  E.g., "0:" means all devices on bus 0, "0" means all functions of device 0 on any bus,
              "0.3" selects third function of device 0 on all buses and ".4" shows only the fourth function of each device.
...
```

デバイスドライバはPCIデバイスが持つレジスタへの読み書きによってデバイスを制御する。

図

カーネルがPCIにアクセスするために起動時にどんな関数を呼んでいるかftraceを使って調べてみる。
カーネルパラメータに`ftrace=function ftrace_filter=*pci*`を追加して起動すると以下のような結果になった。

```
# cat /sys/kernel/debug/tracing/trace
# tracer: function
#
# entries-in-buffer/entries-written: 57813/70138   #P:12
#
#                              _-----=> irqs-off
#                             / _----=> need-resched
#                            | / _---=> hardirq/softirq
#                            || / _--=> preempt-depth
#                            ||| /     delay
#           TASK-PID   CPU#  ||||    TIMESTAMP  FUNCTION
#              | |       |   ||||       |         |
          <idle>-0     [000] d..1     0.155635: pci_msi_create_irq_domain <-arch_init_msi_domain
          <idle>-0     [000] ...1     0.156933: pci_msi_create_irq_domain <-arch_create_remap_msi_irq_domain
##### CPU 2 buffer started ####
       swapper/0-1     [002] ....     0.853238: pci_realloc_setup_params <-do_one_initcall
       swapper/0-1     [002] ....     0.853854: pcibus_class_init <-do_one_initcall
       swapper/0-1     [002] ....     0.853855: pci_driver_init <-do_one_initcall
       swapper/0-1     [002] ....     0.853972: early_pci_allowed <-early_root_info_init
       swapper/0-1     [002] ....     0.853973: read_pci_config <-early_root_info_init
       swapper/0-1     [002] ....     0.853973: read_pci_config <-early_root_info_init
       swapper/0-1     [002] ....     0.853973: read_pci_config <-early_root_info_init
       swapper/0-1     [002] ....     0.853974: read_pci_config <-early_root_info_init
       swapper/0-1     [002] ....     0.853975: read_pci_config <-early_root_info_init
       swapper/0-1     [002] ....     0.853975: early_pci_allowed <-amd_postcore_init
...
```

`read_pci_config` という関数がコンフィグレーション空間にアクセスしていそうである。
実装は[arch/x86/pci/early.c](https://git.kernel.org/pub/scm/linux/kernel/git/torvalds/linux.git/tree/arch/x86/pci/early.c?h=v5.3#n11)にある。

```c
u32 read_pci_config(u8 bus, u8 slot, u8 func, u8 offset)
{
        u32 v;
        outl(0x80000000 | (bus<<16) | (slot<<11) | (func<<8) | offset, 0xcf8);
        v = inl(0xcfc);
        return v;
}
```

`outl`と`inl`はそれぞれIOポートへの読み書きの関数である。実装は[arch/x86/boot/boot.h](https://git.kernel.org/pub/scm/linux/kernel/git/torvalds/linux.git/tree/arch/x86/boot/boot.h?h=v5.3#n63)にある。

```c
static inline void outl(u32 v, u16 port)
{
        asm volatile("outl %0,%1" : : "a" (v), "dN" (port));
}
static inline u32 inl(u16 port)
{
        u32 v;
        asm volatile("inl %1,%0" : "=a" (v) : "dN" (port));
        return v;
}
```


# 参考
- Linuxデバイスドライバプログラミング, 平田豊
