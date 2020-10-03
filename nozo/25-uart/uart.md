# UART

Universal Asynchronous Receiver/Transmitter (UART) はデバイス間のシリアル通信方式で、下図のように送信(TX)と受信(RX)の2本の信号を使って通信する。

![](./img/UART.PNG)

シリアル通信にはデバイス間で同期をとる方法として、クロック同期式と調歩同期式と呼ばれる方式がある。

クロック同期方式では、デバイス間にデータ送受信信号線のほかにクロック信号線を持ち、クロックに合わせてデータの同期をとる。
一方、調歩同期式では、クロック信号線は持たず、送信するデータに同期をとるための情報(スタートビット、ストップビット)を含める。

UARTは調歩同期式である。下図に２つのキャラクタ'A'と'B'を送信する例を示す。

![](./img/UART-TIMING.PNG)

送信線(TX)は使われていないときは常に1にしておき、データを送るときに送信開始を表すスタートビット

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

```c
int serial_init()
{
  sci->scr = 0;
  sci->smr = 0;
  sci->brr = 64;
  sci->scr = SCI_SCR_RE | SCI_SCR_TE;
  sci->ssr = 0;

  return 0;
}
```

```c
int serial_is_send_enable()
{
  return (sci->ssr & SCI_SSR_TDRE);
}

int serial_send_byte(unsigned char c)
{
  while (!serial_is_send_enable(index)) ;
  sci->tdr = c;
  sci->ssr &= ~SCI_SSR_TDRE;

  return 0;
}
```

# 参考
- 坂井 弘亮，12ステップで作る組込みOS自作入門，カットシステム
- 秋月電子, HD64F3069RF25 PDFデータシート, "13. SCI"
https://akizukidenshi.com/download/ds/renesas/hd64f3069r.pdf
- ACRi, シリアル通信で Hello, FPGA
https://www.acri.c.titech.ac.jp/wordpress/archives/category/20q1-10a
