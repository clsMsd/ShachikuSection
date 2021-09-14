# NEURON Simulator

NEURONは神経細胞・神経回路モデルのシミュレーションをするためのツールのひとつ。
ニューロン（神経細胞）は細胞の一種で、核が存在する細胞体、他のニューロンから情報を受け取る樹状突起、ほかのニューロンへ情報を伝える軸索からなる。ニューロン間の接続部分をシナプスという。

> ![](https://upload.wikimedia.org/wikipedia/commons/3/36/Components_of_neuron.jpg)
> 
> https://en.wikipedia.org/wiki/Neuron, Diagram of the components of a neuron

細胞膜の内外には電位差(膜電位)があり、通常時は約-75mVで（静止電位という）、信号を伝えるときインパルスのように一瞬電位差が正の方向に大きく変化する(活動電位という)。
この活動電位が軸索に沿って伝導して次のニューロンに信号を伝達する。

膜電位は細胞内外のイオン濃度差によって生じる。

![](https://upload.wikimedia.org/wikipedia/commons/6/6a/Membrane_Permeability_of_a_Neuron_During_an_Action_Potential.svg)

Hodgkin-Huxleyモデル

> ![](https://upload.wikimedia.org/wikipedia/commons/1/1f/MembraneCircuit.svg)
> 
> https://en.wikipedia.org/wiki/Action_potential, Ion movement during an action potential.

NEURONのプログラム

```
load_file("nrngui.hoc")

create cell
objref stim

cell{
    diam=20.0
    L=20.0
    insert hh
    gnabar_hh=0.12
    gkbar_hh=0.04

    stim=new IClamp(0.5)
    stim.del=100
    stim.dur=100
    stim.amp=0.05
}
tstop=300
printf("Inited.\n")
```

# 参考文献
- 神崎亮平, 昆虫の脳をつくる ─君のパソコンに脳をつくってみよう─, https://www.asakura.co.jp/books/isbn/978-4-254-10277-2/
- NEURON, https://www.neuron.yale.edu/neuron/
