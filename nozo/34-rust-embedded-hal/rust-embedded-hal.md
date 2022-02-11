# Rustの組込みフレームワーク

Rustのembedded-hal(HAL: Hardware Abstraction Layer)の実装がどうなっているのか見てみる。

> ![](./img/rust_layers.svg)
>
> 移植性 - The Embedded Rust Book, https://tomoyuki-nakabayashi.github.io/book/assets/rust_layers.svg

Board Support Crateとしてwio_terminal-0.5.0をみてみる。

https://docs.rs/wio_terminal/0.5.0/wio_terminal/index.html

以下はLEDを点灯するだけのプログラム。

```rust
#![no_std]
#![no_main]

use panic_halt as _;
use wio_terminal as wio;

use wio::entry;
use wio::pac::Peripherals;
use wio::prelude::*;

#[entry]
fn main() -> ! {
    // 1. マイコンのペリフェラルを取得
    let peripherals = Peripherals::take().unwrap();
    
    // 2. I/Oピンを取得する
    let pins = wio::Pins::new(peripherals.PORT);
    // 3. LEDにつながったI/Oピンを出力設定にして取得する
    let mut user_led = pins.user_led.into_push_pull_output();
    // 4. LEDを点灯させる
    user_led.set_high().unwrap();

    loop {}
}
```

## 1. マイコンのペリフェラルを取得

`Peripherals::take()`はATSAMD51PというマイコンのPAC(一番下の層のクレート)で提供される関数。
マイコン上のすべてのペリフェラルにアクセスするためのデータ構造をまとめた`Peripherals`を返す。

https://docs.rs/atsamd51p/0.11.0/atsamd51p/struct.Peripherals.html

```rust
static mut DEVICE_PERIPHERALS: bool = false;

pub struct Peripherals {
    pub AC: AC,
    pub ADC0: ADC0,
    pub ADC1: ADC1,
    pub AES: AES,
...
}

impl Peripherals {
    pub fn take() -> Option<Self> {
        cortex_m::interrupt::free(|_| {
            if unsafe { DEVICE_PERIPHERALS } {
                None
            } else {
                Some(unsafe { Peripherals::steal() })
            }
        })
    }

    pub unsafe fn steal() -> Self {
        DEVICE_PERIPHERALS = true;
        Peripherals {
...
        }
    }
}
```

マイコン上のペリフェラルにはタイマやシリアル通信デバイスなどがあるが、それぞれ物理的に１つしかないものをプログラムのあちこちからアクセスされるとおかしな状態になってしまう。
そのため、上の`take`関数は1回目の呼び出しでは`Peripherals`を返しているが、2回目以降は`None`を返すように、グローバルな`DEVICE_PERIPHERALS`変数を使って実装されている。
(rust ではグローバルな変数へのアクセスは unsafe)


## 2. I/Oピンを取得する

`wio::Pins::new(peripherals.PORT)`はBSC(一番上の層のクレート)で提供される関数で、PACで取得したペリフェラルの`PORT`(マイコンのI/Oピンコントローラ)を受け取って、ボード上のLEDやボタンがそれぞれどのI/Oピンに割り当てられているかを表す`Pins`を返す。

https://docs.rs/wio_terminal/0.5.0/wio_terminal/struct.Pins.html

```rust
pub struct Pins {
    pub user_led: Pin<PA15, Reset>,
    pub button1: Pin<PC26, Reset>,
    pub button2: Pin<PC27, Reset>,
    pub button3: Pin<PC28, Reset>,
...
}
```

PACはあくまでマイコンに対するアクセス方法を提供するクレートで、マイコンのI/Oピンが実際にボード上のどのデバイスに接続されているかは知らない。
そのため、BSCでマイコンのI/Oピンとボード上のデバイスの関係を定義している。

以下はWio Terminalに搭載されているマイコンとボード上のデバイスの接続関係を示した回路図(回路の一部で全部ではない)。
PA15ピン(PortのAグループの15番ピン)がuser_ledに接続されていることがわかる。

> ![](./img/wio-terminal-cir.png)
> 
> https://files.seeedstudio.com/wiki/Wio-Terminal/res/ATSAMD51.pdf


## 3. LEDにつながったI/Oピンを出力設定にして取得する

`pins.user_led.into_push_pull_output()`は、`Pin<PA15, Disabled<Floating>>`型の`pins.user_led`に対して、`into_push_pull_output()`を実行することで`Pin<PA15, Output<PushPull>>`型のI/Oピンとして設定している。
`Pin`型は以下のように定義されていて、HAL(中間の層のクレート)で提供されている。

型引数`I`にはI/Oピンの番号が入り、今回の例だとLEDの`PA15`にあたる。
型引数`M`にはI/Oピンの状態が入り、`Disabled`, `Input`, `Output`などがある。

https://docs.rs/atsamd-hal/0.14.0/atsamd_hal/gpio/v2/pin/struct.Pin.html

```rust
/// A type-level GPIO pin, parameterized by [`PinId`] and [`PinMode`] types
pub struct Pin<I, M>
where
    I: PinId,
    M: PinMode,
{
    pub(in crate::gpio) regs: Registers<I>,
    mode: PhantomData<M>,
}
```

`Pin`型に`M: PinMode`があるおかげで、「入力設定にしたI/Oピンに対してhighレベルを出力する」というような誤った動作をコンパイル時にエラーとして検出することができる。
この仕組みは以下のようにして実現している。

任意の`I`, `M`が設定された`Pin`型は以下のメソッドを持つ。
`into_push_pull_output`などのI/Oピンの状態を変更するメソッドは公開されているが、`_is_low`や`_set_low`などのI/Oピンへの入出力のメソッドは公開されていない(create内のみに公開)ので使用することができない。

```rust
impl<I, M> Pin<I, M>
where
    I: PinId,
    M: PinMode,
{
...
　　// I/Oピンの状態を変更するメソッド
    pub fn into_push_pull_output(self) -> Pin<I, PushPullOutput> {
        self.into_mode()
    }
...
    // I/Oピンの入力を読み取るメソッド(ただしcrate内のみ公開)
    pub(crate) fn _is_low(&self) -> bool {
        self.regs.read_pin() == false
    }
    pub(crate) fn _is_high(&self) -> bool {
        self.regs.read_pin() == true
    }

    // I/Oピンに出力を書き込むメソッド(ただしcrate内のみ公開)
    pub(crate) fn _set_low(&mut self) {
        self.regs.write_pin(false);
    }
    pub(crate) fn _set_high(&mut self) {
        self.regs.write_pin(true);
    }
...
}
```

ではどうやって入出力をするのかというと、入出力のメソッドは以下のように`Pin`の状態が`Output`, `Input`の場合にのみ`set_high`や`is_high`が定義されるようになっていて、入力/出力設定がされたI/Oピンだけがそれらのメッソドを呼べるようになっている。

```rust
impl<I, C> InputPin for Pin<I, Input<C>>
where
    I: PinId,
    C: InputConfig,
{
    type Error = Infallible;
    #[inline]
    fn is_high(&self) -> Result<bool, Self::Error> {
        Ok(self._is_high())
    }
    #[inline]
    fn is_low(&self) -> Result<bool, Self::Error> {
        Ok(self._is_low())
    }
}
```

```rust
impl<I, C> OutputPin for Pin<I, Output<C>>
where
    I: PinId,
    C: OutputConfig,
{
    type Error = Infallible;
    #[inline]
    fn set_high(&mut self) -> Result<(), Self::Error> {
        self._set_high();
        Ok(())
    }
    #[inline]
    fn set_low(&mut self) -> Result<(), Self::Error> {
        self._set_low();
        Ok(())
    }
}
```

上記の定義によって、例えば`Pin<PA15, Disabled<Floating>>`型のI/Oピンに対して`set_high`メソッドを呼ぼうとするとコンパイルエラーになる。

プログラム：
```rust
    let peripherals = Peripherals::take().unwrap();
    
    let pins = wio::Pins::new(peripherals.PORT);
    pins.user_led.set_high().unwrap();
```

コンパイルエラー：
```
error[E0599]: the method `set_high` exists for struct `wio_terminal::atsamd_hal::gpio::v2::Pin<PA15, wio_terminal::atsamd_hal::gpio::v2::Disabled<wio_terminal::atsamd_hal::gpio::v2::Floating>>`, but its trait bounds were not satisfied
   --> src/main.rs:16:19
    |
16  |       pins.user_led.set_high().unwrap();
    |                     ^^^^^^^^ method cannot be called on `wio_terminal::atsamd_hal::gpio::v2::Pin<PA15, wio_terminal::atsamd_hal::gpio::v2::Disabled<wio_terminal::atsamd_hal::gpio::v2::Floating>>` due to unsatisfied trait bounds
    |
   ::: /root/.cargo/registry/src/github.com-1ecc6299db9ec823/atsamd-hal-0.14.0/src/gpio/v2/pin.rs:496:1
```

## 4. LEDを点灯させる

```rust
pub(super) unsafe trait RegisterInterface {
...
    /// Write the logic level of an output pin
    #[inline]
    fn write_pin(&mut self, bit: bool) {
        let mask = self.mask_32();
        // Safety: OUTSET & OUTCLR are "mask" registers, and we only write the
        // bit for this pin ID
        unsafe {
            if bit {
                self.group().outset.write(|w| w.bits(mask));
            } else {
                self.group().outclr.write(|w| w.bits(mask));
            }
        }
    }
...
}
```

# 参考
- 中林 智之／井田 健太，基礎から学ぶ 組込みRust，C&R研究所, https://www.c-r.com/book/detail/1403
- The Embedded Rust Book, https://tomoyuki-nakabayashi.github.io/book/
