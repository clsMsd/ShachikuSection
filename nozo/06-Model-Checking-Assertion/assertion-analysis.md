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

assertは引数に与えられた条件を満たさなくなったときにエラーを出す。
このassert文を追加して、本当に変数`x`がとる値が常に`0 <= x <= N`の範囲内であるかを検証できる。

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

検証結果は`pan:1: assertion violated ((x>=0)&&(x<=5)) (at depth 22)`とassertのエラーが表示されてしまった。
エラーが起きた場所を見てみる。

```
$ spin -p -g -t incdec.pml
using statement merging
  1:    proc  0 (inc:1) incdec.pml:6 (state 1)  [((x<5))]
  2:    proc  0 (inc:1) incdec.pml:6 (state 2)  [x = (x+1)]
                x = 1
  3:    proc  1 (dec:1) incdec.pml:12 (state 1) [((x>0))]
  4:    proc  0 (inc:1) incdec.pml:6 (state 1)  [((x<5))]
  5:    proc  0 (inc:1) incdec.pml:6 (state 2)  [x = (x+1)]
                x = 2
  6:    proc  0 (inc:1) incdec.pml:6 (state 1)  [((x<5))]
  7:    proc  1 (dec:1) incdec.pml:12 (state 2) [x = (x-1)]
                x = 1
  8:    proc  0 (inc:1) incdec.pml:6 (state 2)  [x = (x+1)]
                x = 2
  9:    proc  0 (inc:1) incdec.pml:6 (state 1)  [((x<5))]
 10:    proc  0 (inc:1) incdec.pml:6 (state 2)  [x = (x+1)]
                x = 3
 11:    proc  1 (dec:1) incdec.pml:12 (state 1) [((x>0))]
 12:    proc  0 (inc:1) incdec.pml:6 (state 1)  [((x<5))]
 13:    proc  0 (inc:1) incdec.pml:6 (state 2)  [x = (x+1)]
                x = 4
 14:    proc  0 (inc:1) incdec.pml:6 (state 1)  [((x<5))]
 15:    proc  1 (dec:1) incdec.pml:12 (state 2) [x = (x-1)]
                x = 3
 16:    proc  0 (inc:1) incdec.pml:6 (state 2)  [x = (x+1)]
                x = 4
 17:    proc  0 (inc:1) incdec.pml:6 (state 1)  [((x<5))]
 18:    proc  0 (inc:1) incdec.pml:6 (state 2)  [x = (x+1)]
                x = 5
 19:    proc  2 (reset:1) incdec.pml:18 (state 1)       [((x==5))]
 20:    proc  1 (dec:1) incdec.pml:12 (state 1) [((x>0))]
 21:    proc  2 (reset:1) incdec.pml:18 (state 2)       [x = 0]
                x = 0
 22:    proc  1 (dec:1) incdec.pml:12 (state 2) [x = (x-1)]
                x = -1
spin: incdec.pml:23, Error: assertion violated
spin: text of failed assertion: assert(((x>=0)&&(x<=5)))
 23:    proc  3 (check:1) incdec.pml:23 (state 1)       [assert(((x>=0)&&(x<=5)))]
spin: trail ends after 23 steps
#processes: 4
                x = -1
 23:    proc  3 (check:1) incdec.pml:24 (state 2) <valid end state>
 23:    proc  2 (reset:1) incdec.pml:17 (state 3)
 23:    proc  1 (dec:1) incdec.pml:11 (state 3)
 23:    proc  0 (inc:1) incdec.pml:5 (state 3)
4 processes created
```

ログを見ると22ステップ目で`x = -1`となってしまっている。

本来であれば19ステップ目で`reset`プロセスの条件式`x==5`が実行された直後に`x = 0`が実行されるのが望ましい。
しかし、20ステップ目で`dec`プロセスの条件式`x>0`が実行されてしまっている。
そのため、21ステップ目で`reset`プロセスの代入文`x = 0`が実行されたあとに22ステップ目で`dec`プロセスの代入文`x = (x - 1)`が実行されてしまい`x = -1`という結果になってしまった。

これは、あるプロセスの処理中にほかのプロセスの処理が挟まってしまったために発生したエラーである。
これを回避するためには条件式判定と変数代入の処理をひと塊であるように明示するatomicという構文を使う。

```
#define N 5
int x = 0;

active proctype inc() {
  do
    :: atomic{x < N -> x++}
  od
}

active proctype dec() {
  do
    :: atomic{x > 0 -> x--}
  od
}

active proctype reset() {
  do
    :: atomic{x == N -> x = 0}
  od
}

active proctype check() {
  assert (x >= 0 && x <= N)
}
```

このプログラムの検証結果をみるとerrorは0となっていることがわかる。
```
$ spin -v -search incdec-atomic.pml
cmd01: gcc -std=gnu99  -O  -DSAFETY -o pan pan.c
cmd02: ./pan 

(Spin Version 6.4.5 -- 1 January 2016)
        + Partial Order Reduction

Full statespace search for:
        never claim             - (none specified)
        assertion violations    +
        cycle checks            - (disabled by -DSAFETY)
        invalid end states      +

State-vector 44 byte, depth reached 7, errors: 0
       18 states, stored
       17 states, matched
       35 transitions (= stored+matched)
        0 atomic steps
hash conflicts:         0 (resolved)

Stats on memory usage (in Megabytes):
    0.001       equivalent memory usage for states (stored*(State-vector + overhead))
    0.290       actual memory usage for states
  128.000       memory used for hash table (-w24)
    0.534       memory used for DFS stack (-m10000)
  128.730       total actual memory usage


unreached in proctype inc
        incdec-atomic.pml:8, state 7, "-end-"
        (1 of 7 states)
unreached in proctype dec
        incdec-atomic.pml:14, state 7, "-end-"
        (1 of 7 states)
unreached in proctype reset
        incdec-atomic.pml:20, state 7, "-end-"
        (1 of 7 states)
unreached in proctype check
        (0 of 2 states)

pan: elapsed time 0.01 seconds
```

## 参考文献
- 早稲田大学 高信頼ソフトウェア, http://www.ueda.info.waseda.ac.jp/oess/RS2018/
- SPIN model checker, http://spinroot.com/spin/whatispin.html
