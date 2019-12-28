# 割込みについての調査

Intel® 64 and IA-32 Architectures Software Developer Manuals と Linux Kernel の実装をもとに割り込みのしくみを調査する。

## Local APIC と I/O APIC

x86 アーキテクチャでは Advanced Programmable Interrupt Controller (APIC) という割り込みコントローラによって割り込みを制御する。

![](./img/APIC.png)

## 割り込み処理

// 周辺デバイス→割り込みコントローラ→CPUへと割り込み信号を送信

// CPUがIRQ（割り込み要因番号）を割り込みコントローラから読み取る

// CPUがIRQに対応する割り込みハンドラのアドレスをIDTから読み取る

// CPUがモードレジスタ・プログラムカウンタを退避させて、モードレジスタ・プログラムカウンタを設定

# 参考
- Intel® 64 and IA-32 Architectures Software Developer Manuals, https://software.intel.com/en-us/articles/intel-sdm
  - Volume 3 : CHAPTER 6 INTERRUPT AND EXCEPTION HANDLING
  - Volume 3 : CHAPTER 10 ADVANCED PROGRAMMABLE INTERRUP  T CONTROLLER (APIC)
- Linux generic IRQ handling - Linux Kernel Documentation, https://www.kernel.org/doc/html/latest/core-api/genericirq.html
- デバイスドライバと割り込み処理、inb()とoutb() - 筑波大学 システム情報系 オペレーティングシステム II, http://www.coins.tsukuba.ac.jp/~yas/coins/os2-2018/2019-01-25/index.html
