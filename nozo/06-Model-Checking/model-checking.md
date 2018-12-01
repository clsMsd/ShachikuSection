# モデル検査の紹介

## モデル検査とは？

## SPIN model checker
モデル記述言語Promela(Process Meta Language)で記述された並行システムを検証するツール。

下のプログラムは変数`x`をインクリメント・デクリメント・リセットする３つのプロセスが並行に動作するモデルを記述したものである。
```
#define N 5
int x = 0;

active proctype inc() {
  do
    :: x < N -> x++
  od
}

active proctype dec() {
  do
    :: x > 0 -> x--
  od
}

active proctype reset() {
  do
    :: x == N -> x = 0
  od
}
```
> http://www.ueda.info.waseda.ac.jp/oess/RS2018/Html/class_rsc/materials/RS2018-spin1-e.pdf より引用

20ステップだけ実行をシミュレーションしてみると、プロセス0, 1, 2が生成されてそれぞれが入り混じって処理されていることがわかる。
```
$ spin -p -g -u20 incdec.pml
  0:    proc  - (:root:) creates proc  0 (inc)
  0:    proc  - (:root:) creates proc  1 (dec)
  0:    proc  - (:root:) creates proc  2 (reset)
  1:    proc  0 (inc:1) test.pml:6 (state 1)    [((x<5))]
  2:    proc  0 (inc:1) test.pml:6 (state 2)    [x = (x+1)]
                x = 1
  3:    proc  1 (dec:1) test.pml:12 (state 1)   [((x>0))]
  4:    proc  0 (inc:1) test.pml:8 (state 4)    [.(goto)]
  5:    proc  0 (inc:1) test.pml:6 (state 1)    [((x<5))]
  6:    proc  0 (inc:1) test.pml:6 (state 2)    [x = (x+1)]
                x = 2
  7:    proc  0 (inc:1) test.pml:8 (state 4)    [.(goto)]
  8:    proc  1 (dec:1) test.pml:12 (state 2)   [x = (x-1)]
                x = 1
  9:    proc  1 (dec:1) test.pml:14 (state 4)   [.(goto)]
 10:    proc  1 (dec:1) test.pml:12 (state 1)   [((x>0))]
 11:    proc  1 (dec:1) test.pml:12 (state 2)   [x = (x-1)]
                x = 0
 12:    proc  0 (inc:1) test.pml:6 (state 1)    [((x<5))]
 13:    proc  0 (inc:1) test.pml:6 (state 2)    [x = (x+1)]
                x = 1
 14:    proc  0 (inc:1) test.pml:8 (state 4)    [.(goto)]
 15:    proc  1 (dec:1) test.pml:14 (state 4)   [.(goto)]
 16:    proc  1 (dec:1) test.pml:12 (state 1)   [((x>0))]
 17:    proc  0 (inc:1) test.pml:6 (state 1)    [((x<5))]
 18:    proc  1 (dec:1) test.pml:12 (state 2)   [x = (x-1)]
                x = 0
 19:    proc  1 (dec:1) test.pml:14 (state 4)   [.(goto)]
 20:    proc  0 (inc:1) test.pml:6 (state 2)    [x = (x+1)]
                x = 1
-------------
depth-limit (-u20 steps) reached
#processes: 3
                x = 1
 20:    proc  2 (reset:1) test.pml:17 (state 3)
 20:    proc  1 (dec:1) test.pml:11 (state 3)
 20:    proc  0 (inc:1) test.pml:8 (state 4)
3 processes created
```

このモデルにおいて、変数`x`がとる値は常に`0 <= x <= N`の範囲内であるように見える。
この性質を検証するために以下のプロセスを追加する。

```
active proctype check() {
  assert (x >= 0 && x <= N)
}
```

```
$ spin -v -search incdec.pml 
cmd01: gcc -std=gnu99  -O  -DSAFETY -o pan pan.c
cmd02: ./pan 
pan:1: assertion violated ((x>=0)&&(x<=5)) (at depth 22)
pan: wrote incdec.pml.trail

(Spin Version 6.4.5 -- 1 January 2016)
Warning: Search not completed
        + Partial Order Reduction

Full statespace search for:
        never claim             - (none specified)
        assertion violations    +
        cycle checks            - (disabled by -DSAFETY)
        invalid end states      +

State-vector 44 byte, depth reached 32, errors: 1
       89 states, stored
       91 states, matched
      180 transitions (= stored+matched)
        0 atomic steps
hash conflicts:         0 (resolved)

Stats on memory usage (in Megabytes):
    0.006       equivalent memory usage for states (stored*(State-vector + overhead))
    0.291       actual memory usage for states
  128.000       memory used for hash table (-w24)
    0.534       memory used for DFS stack (-m10000)
  128.730       total actual memory usage



pan: elapsed time 0 seconds
```


## 線形時相論理
LTL(Linear-time Temporal Logic)とは、時間の概念が取り入れられた論理である。
LTLの構文をいかに示す。
命題論理に`[]`, `<>`, `X`, `U`という論理演算子が加わっている。
```
φ,Ψ ::= ¬ φ | φ ∧ Ψ | φ ∨ Ψ | φ ⇒ Ψ
      | [] φ  (always φ)
      | <> φ  (eventually φ)
      | X  φ  (φ holds next)
      | φ U Ψ (φ until Ψ)
```

|LTL式|意味|
----|---- 
| `[] φ` | 現時点から常に`φ`が成り立つ |
| `<> φ` | いつか`φ`が成り立つ |
| `X  φ` | 次に`φ`が成り立つ |
| `φ U Ψ` | `Ψ`が成り立つまで`φ`が成り立つ |

## 参考文献
- 早稲田大学 高信頼ソフトウェア, http://www.ueda.info.waseda.ac.jp/oess/RS2018/
- SPIN model checker, http://spinroot.com/spin/whatispin.html
