# Petri Netsの紹介
## Petri Nets とは？
[Petri Nets World, FAQ](http://www.informatik.uni-hamburg.de/TGI/PetriNets/faq/)より

> Petri Nets is a formal and graphical appealing language which is appropriate for modelling systems with concurrency and resource sharing.

Petri Nets は並行システムをグラフィカルにモデリングするためのモデル記述言語である。
モデリングした並行システムについてツールを用いてシミュレートや解析をすることによってシステムの検証を行う。

### Petri Nets の構成
Petri Nets は２種類のノード Place/Transition と，それらを接続する Arc によって構成される。
また、Place は０個以上の token を持つ。

![](./img/pn0.PNG)

### Petri Nets の計算
Petri Nets は次の１つのルールに従って Place 上の token が移動することで計算が進む。

- Transition のすべての入力側の Place に１個以上の token があるとき、それらの token を１個消費してTransition のすべての出力側の Place に１個 token を生成する

![](./img/pn1.PNG)

このような token の移動を繰り返すことで Petri Nets の状態が変化していく。

## 例題
### 生産者 / 消費者モデル
![](./img/prod-cons.PNG)

### 通信モデル
Murata, Tadao. "Petri nets: Properties, analysis and applications." Proceedings of the IEEE 77.4 (1989): 541-580. Fig. 9.より

![](./img/simpl-com.PNG)

### 食事する哲学者
[食事する哲学者の問題(Wikipedia)](https://ja.wikipedia.org/wiki/%E9%A3%9F%E4%BA%8B%E3%81%99%E3%82%8B%E5%93%B2%E5%AD%A6%E8%80%85%E3%81%AE%E5%95%8F%E9%A1%8C)

![](./img/phi.PNG)

## 非決定実行による検証
Petri Netsの特徴のひとつとして計算の非決定性が挙げられる。
token を移動させるルールを適用できる箇所が複数あるとき、それらのすべての箇所がルールを適用する選択肢となり得るという性質である。

そうした Petri Nets の非決定的な実行経路についてすべて網羅したグラフ構造を状態遷移図と呼ぶ。
例えば次は通信モデルの状態遷移図である。

![](./img/statespace.PNG)

状態遷移図の各ノードは Petri Nets のある時点での状態(tokenの配置状態)を表し、その時点の状態において適用できるルールの数だけ遷移先のノードが存在する。

状態遷移図からはそのモデルがとりうるすべての状態を知ることができ、行き詰った状態（例えばデッドロック）の検証や起きてはならない状態の検出などに用いることができる。

## Petri Netsの派生
- Coloured Petri net
- Timed Petri net

## 参考文献
- Petri Nets World, http://www.informatik.uni-hamburg.de/TGI/PetriNets/
- Murata, Tadao. "Petri nets: Properties, analysis and applications." Proceedings of the IEEE 77.4 (1989): 541-580.
- Oris Tool - Analysis of Timed and Stochastic Petri Nets, https://www.oris-tool.org/
