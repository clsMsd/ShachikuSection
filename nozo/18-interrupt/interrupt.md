# 割込みについての調査

Intel® 64 and IA-32 Architectures Software Developer Manuals と Linux Kernel の実装をもとに割り込みのしくみを調査する。

## Local APIC と I/O APIC

x86 アーキテクチャでは Advanced Programmable Interrupt Controller (APIC) という割り込みコントローラによって割り込みを制御する。

![](./img/APIC.png)

## IDT

Interrupt Descriptor Table (IDT)

https://git.kernel.org/pub/scm/linux/kernel/git/torvalds/linux.git/tree/arch/x86/kernel/idt.c?h=v5.4#n168

```c
/* Must be page-aligned because the real IDT is used in a fixmap. */
gate_desc idt_table[IDT_ENTRIES] __page_aligned_bss;

struct desc_ptr idt_descr __ro_after_init = {
	.size		= (IDT_ENTRIES * 2 * sizeof(unsigned long)) - 1,
	.address	= (unsigned long) idt_table,
};
```

https://git.kernel.org/pub/scm/linux/kernel/git/torvalds/linux.git/tree/arch/x86/include/asm/desc.h?h=v5.4#n212

```c
static inline void native_load_idt(const struct desc_ptr *dtr)
{
	asm volatile("lidt %0"::"m" (*dtr));
}

static inline void store_idt(struct desc_ptr *dtr)
{
	asm volatile("sidt %0":"=m" (*dtr));
}
```

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
