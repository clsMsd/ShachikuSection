# Bitstreamについて調査

SystemVerilog, VHDLなどのHDL(Hardware Description Language)で書かれたRTL(レジスタ転送レベル)記述はツールによってバイナリ(Bitstream)に変換されFPGAに書き込まれる。
このBitstreamの中身は何なのか調査する。

## FPGAの内部構成

まずFPGAの内部構成について見てみる。

FPGAは下図のようなブロックの並びで構成されている。

> <img src="./img/FPGA.PNG" width="500">
> 
> 天野 英晴, FPGAの原理と構成, 図3.1 より

これらのブロックはそれぞれ次のような役割を持ち任意の回路を実現している。

- 論理ブロック(LB) ... 任意の論理回路を実現する要素
- I/Oブロック(IOB) ... 外部との信号の入出力を行う要素
- コネクションブロック(CB)、スイッチブロック(SB) ... LBやIOBを接続して任意の配線経路を形成する要素

LBはLook-Up-Table(LUT)とフリップフロップ(FF)で構成される。

LUTはメモリテーブルであり、組み合わせ回路の真理値表をLUTで表すことで任意の回路を実現する。

> <img src="./img/LUT.PNG" width="400">
> 
> 天野 英晴, FPGAの原理と構成, 図2.15 より

例えば`f = X・Y・Z`という２つのANDゲートによる組み合わせ回路の真理値表は次のように書ける。
この真理値表のX,Y,Zをアドレス、fを出力とみればLUTとして表現することができる。

| X | Y | Z | f |
|---|---|---|---|
| 0	| 0	| 0	| 0	|
| 0	| 0	| 1	| 0	|
| 0	| 1	| 0	| 0	|
| 0	| 1	| 1	| 0	|
| 1	| 0	| 0	| 0	|
| 1	| 0	| 1	| 0	|
| 1	| 1	| 0	| 0	|
| 1	| 1	| 1	| 1	|

また、LUTの出力をFFで保持するか選択することで任意の順序回路を実現することができる。

## RTL記述からBitstreamが生成されるまでの流れ

SystemVerilog, VHDLなどのHDLで書かれたRTL記述は次のような流れでBitstreamに変換される。

- 論理合成(Logic Synthesis)
  - RLT記述からAND/ORやFFなどの論理素子の集合とその接続関係を表すネットリストに変換する
- テクノロジーマッピング(Technology mapping)
  - ネットリストで表される論理回路をLUTを用いた回路に変換する
- 配置配線(Place & Route)
  - LUTレベルの回路をチップ上の論理資源や配線資源に割り当てる

こうして得られたFPGA上の論理素子や配線スイッチをプログラムするためのデータをコンフィギュレーションデータやBitstreamと呼ぶ。
BitstreamはプログラムツールによってFPGAデバイスに書き込まれる。

ここで例としてXilinxのツールであるvivadoを使ってRLT記述がBitstreamに変換される流れを見てみる。

まずSystemVerilogでボード上の３つのスイッチを入力`x, y, z`、１つのLEDを出力`f`とした`f = x & y & z`という回路を記述する。

 ```verilog
 module top(
    input  logic x, y, z, 
    output logic f
    );
    
    assign f = x & y & z;
    
endmodule
 ```
 
外部I/Oはボードごとに異なるので次のような制約ファイルで割り当てを記述する。
ArtyS7-50の制約ファイルのテンプレートは以下にある。

https://github.com/Digilent/digilent-xdc/blob/master/Arty-S7-50-Master.xdc
 
 ```
 ## Switches
set_property -dict { PACKAGE_PIN H14   IOSTANDARD LVCMOS33 } [get_ports { x }];
set_property -dict { PACKAGE_PIN H18   IOSTANDARD LVCMOS33 } [get_ports { y }];
set_property -dict { PACKAGE_PIN G18   IOSTANDARD LVCMOS33 } [get_ports { z }];

## LEDs
set_property -dict { PACKAGE_PIN E18   IOSTANDARD LVCMOS33 } [get_ports { f }];
 ```

このRTL記述を論理合成すると次のようなネットリストが得られる。

<img src="./img/vivado00.PNG" width="500">

そしてテクノロジーマッピングと配置配線まで実行すると次のようなチップ上の配線情報が得られる。
今回の回路はFPGAチップ規模に比べてかなり小さいので、ほんの一部のブロックしか利用されていない。（画面左真ん中の白く光っている部分）

<img src="./img/vivado01.PNG" width="500">

拡大してみると、ボード上のスイッチがIOBとして接続されている。

<img src="./img/vivado02.PNG" width="500">

また、`x & y & z`を表すLBは次のようになっていて、LBの中の１つのLUTが使われている。
今回は値を保持するような回路ではないので右側にあるFFは使われていない。

<img src="./img/vivado03.PNG" width="500">

さらにLUTを選択すると`x & y & z`を表す真理値表が保持されていることがわかる。（画面左下のCell Propertiesの部分）

<img src="./img/vivado04.PNG" width="500">

## Bitstreamファイルのフォーマット

XilinxのArityS7のスペック
ヘッダとコンフィグレーションデータ

## オープンソースなFPGAツール

> ![](https://symbiflow.readthedocs.io/en/latest/_images/toolchain-flow.svg)
> https://symbiflow.readthedocs.io/en/latest/toolchain-desc/design-flow.html より

# 参考
- 天野 英晴, FPGAの原理と構成, https://www.ohmsha.co.jp/book/9784274218644/
- Xilinx - 7 シリーズ FPGA コンフィギュレーション ユーザー ガイド (日本語版) (v1.9), https://japan.xilinx.com/support/documentation/user_guides/j_ug470_7Series_Config.pdf
- Lattice - iCE40 LP/HX/LM シリーズ, https://www.latticesemi.com/ja-JP/Products/FPGAandCPLD/iCE40
