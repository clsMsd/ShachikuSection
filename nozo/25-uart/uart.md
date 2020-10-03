# UART

Universal Asynchronous Receiver/Transmitter (UART)

![](./img/UART.PNG)

![](./img/UART-TIMING.PNG)

> ![](https://www.acri.c.titech.ac.jp/wordpress/wp-content/uploads/2020/03/20Q1_10A_1_shiftregister_ps-768x328.png)\
> ACRi, シリアル通信で Hello, FPGA (1), https://www.acri.c.titech.ac.jp/wordpress/archives/123

> ![](./img/SCI-BLK.PNG)\
> HD64F3069RF25データシート

> ![](./img/REG-ADDR.PNG)\
> HD64F3069RF25データシート

```c
struct sci_regs {
  volatile uint8 smr;
  volatile uint8 brr;
  volatile uint8 scr;
  volatile uint8 tdr;
  volatile uint8 ssr;
  volatile uint8 rdr;
  volatile uint8 scmr;
};

volatile struct sci_regs *sci = 0xffffb0;
```

```
int serial_init()
{
  sci->scr = 0;
  sci->smr = 0;
  sci->brr = 64;
  sci->scr = H8_3069F_SCI_SCR_RE | H8_3069F_SCI_SCR_TE;
  sci->ssr = 0;

  return 0;
}
```

# 参考
- 坂井 弘亮，12ステップで作る組込みOS自作入門，カットシステム
- 秋月電子, HD64F3069RF25 PDFデータシート, "13. SCI"
https://akizukidenshi.com/download/ds/renesas/hd64f3069r.pdf
- ACRi, シリアル通信で Hello, FPGA
https://www.acri.c.titech.ac.jp/wordpress/archives/category/20q1-10a
