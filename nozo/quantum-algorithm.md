# 量子計算の紹介
量子ビットと量子ゲートによって構成される量子回路による量子計算について紹介する。
参考:[IBM Quantum Computing で計算してみよう](https://www.ibm.com/developerworks/jp/cloud/library/cl-quantum-computing/index.html)

## 量子ビット
量子ビットはブロッホ球と呼ばれる表現で状態を表す。
Z軸は0と1の重み(確率)を、XY平面は位相を表す。

![ブロッホ球](./takeuchi-4-16.png)

球面を指す矢印がZ軸正の端のとき`|0>`、Z軸負の端のとき`|1>`と書く。

![重ね合わせ](./takeuchi-4-19.png)

## 量子ゲート
- Xゲート
- Hゲート
- 制御ノットゲート

## IBM Quantum Computing
IBMがクラウド上で量子計算を実行することができるサービスを提供している。
ビギナー向けにグラフィカルなインターフェースで量子回路を設計できる[Composer](https://quantumexperience.ng.bluemix.net/qx/editor)がある。

## 量子計算
- 量子回路における足し算

## Groverのアルゴリズム
データベースの探索問題
