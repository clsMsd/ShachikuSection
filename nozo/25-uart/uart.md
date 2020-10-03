# UART

Universal Asynchronous Receiver/Transmitter (UART)

![](./img/UART.PNG)

![](./img/UART-TIMING.PNG)

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

volatile struct sci_regs *sci0 = 0xffffb0;
```

# 参考

- 秋月電子, HD64F3069RF25 PDFデータシート, "13. SCI"
https://akizukidenshi.com/download/ds/renesas/hd64f3069r.pdf

- ACRi, シリアル通信で Hello, FPGA
https://www.acri.c.titech.ac.jp/wordpress/archives/category/20q1-10a
