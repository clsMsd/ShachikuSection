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

# 参考
- Linuxデバイスドライバプログラミング, 平田豊
