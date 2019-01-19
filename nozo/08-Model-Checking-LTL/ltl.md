前回のPromelaによるModel Checkingの話の続き

```
$ spin -V
Spin Version 6.4.5 -- 1 January 2016
```

前回は、プログラムに無限ループがあるかどうかを検証する手法を紹介した。

今回は、プログラムがあるオートマトンに受理されるかどうかを検証する手法を紹介する。

## 信号機のモデル
今回の検証対象のモデルを以下に示す。
```
mtype = {BLUE, RED, LOCKED, UNLOCKED};
mtype mutex1 = LOCKED;
mtype mutex2 = LOCKED;
mtype state1 = BLUE, state2 = RED;

inline lock(m) {
  d_step{m == UNLOCKED -> m = LOCKED}
}

inline unlock(m){
  m = UNLOCKED
}

active proctype signal1(){
  do
    :: state1 = RED;
       unlock(mutex2);
       lock(mutex1);
       state1 = BLUE
  od
}

active proctype signal2(){
  do
    :: lock(mutex2);
       state2 = BLUE;
       state2 = RED;
       unlock(mutex1)
  od
}
```
吉岡信和; 青木利晃; 田原康之. SPIN による設計モデル検証―モデル検査の実践ソフトウェア検証 (トップエスイー実践講座). 2008. pp86. 図4.19

これは２つの信号機（２色）を交互に切り替えるモデルである。
このモデルは次のように定義されている。
- 信号機の状態は`BLUE`と`RED`で表され、プロセス`signal1`, `signal2`はそれぞれの信号機の状態変数`state1`, `state2`の切り替えを繰り返す。
- 信号機の切り替えにおいて２つの信号機が互い違いの状態となるようにそれぞれに対して`mutex1`と`mutex2`によってロックがかけられている。


```
$ spin -p -g -u10 signal.pml 
  0:    proc  - (:root:) creates proc  0 (signal1)
  0:    proc  - (:root:) creates proc  1 (signal2)
warning: never claim not used in random simulation
  1:    proc  0 (signal1:1) signal.pml:16 (state 1)     [state1 = RED]
                state1 = RED
  2:    proc  0 (signal1:1) signal.pml:11 (state 2)     [mutex2 = UNLOCKED]
                mutex2 = UNLOCKED
  4:    proc  1 (signal2:1) signal.pml:7 (state 2)      [mutex2 = LOCKED]
                mutex2 = LOCKED
  5:    proc  1 (signal2:1) signal.pml:26 (state 5)     [state2 = BLUE]
                state2 = BLUE
  6:    proc  1 (signal2:1) signal.pml:27 (state 6)     [state2 = RED]
                state2 = RED
  7:    proc  1 (signal2:1) signal.pml:11 (state 7)     [mutex1 = UNLOCKED]
                mutex1 = UNLOCKED
  8:    proc  1 (signal2:1) signal.pml:30 (state 10)    [.(goto)]
 10:    proc  0 (signal1:1) signal.pml:7 (state 5)      [mutex1 = LOCKED]
                mutex1 = LOCKED
-------------
depth-limit (-u10 steps) reached
#processes: 2
                mutex1 = LOCKED
                mutex2 = LOCKED
                state1 = RED
                state2 = RED
 10:    proc  1 (signal2:1) signal.pml:24 (state 9)
 10:    proc  0 (signal1:1) signal.pml:19 (state 8)
2 processes created
```

## Never claims
never claimは「決して起きてはいけない挙動」をオートマトンとして記述し、検証したい性質を表現する。
このnever claimによってプログラムが受理されてしまった場合、そのプログラムは満たしてほしくない性質を持つことがわかる。

never claimの例を以下に示す。
```
never{
BLUE_RED:
  if
    :: state1 == BLUE && state2 == RED  -> goto BLUE_RED
    :: state1 == RED  && state2 == RED  -> goto RED_RED
    :: else -> goto accept
  fi;

RED_RED:
  if
    :: state1 == RED  && state2 == RED  -> goto RED_RED
    :: state1 == RED  && state2 == BLUE -> goto RED_BLUE
    :: else -> goto accept
  fi;

RED_BLUE:
  if
    :: state1 == RED  && state2 == BLUE -> goto RED_BLUE
    :: state1 == RED  && state2 == RED  -> goto RED_RED2
    :: else -> goto accept
  fi;

RED_RED2:
  if
    :: state1 == RED  && state2 == RED  -> goto RED_RED2
    :: state1 == BLUE && state2 == RED  -> goto BLUE_RED
    :: else -> goto accept
  fi;

accept:
  skip;
  goto accept
}
```
吉岡信和; 青木利晃; 田原康之. SPIN による設計モデル検証―モデル検査の実践ソフトウェア検証 (トップエスイー実践講座). 2008. pp89. 図4.21

このnever claimは以下のようなオートマトンを表している。
![](./img/never.png)

## 線形時相論理
LTL(Linear-time Temporal Logic)とは、時間の概念が取り入れられた論理である。
`[]`, `<>`, `X`, `U`という論理演算子がある。
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

### LTL式とBüchi Automata
![](./img/Gp.png)
![](./img/Fp.png)
![](./img/Xp.png)
![](./img/p1Up2.png)

### LTL式で書ける性質
|性質|LTL式|
----|----
|応答性|`[](req -> <> ack)`|
|進行性|`[]<>myTurn`|

## 参考文献
- 早稲田大学 高信頼ソフトウェア, http://www.ueda.info.waseda.ac.jp/oess/RS2018/
- 吉岡信和; 青木利晃; 田原康之. SPIN による設計モデル検証―モデル検査の実践ソフトウェア検証 (トップエスイー実践講座). 2008.
- SPIN model checker, http://spinroot.com/spin/whatispin.html
- LTL2BA, http://www.lsv.fr/~gastin/ltl2ba/index.php

