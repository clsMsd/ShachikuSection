前回のPromelaによるModel Checkingの話の続き

## Channel Communication
Channel Communicationは並行処理においてプロセス間でデータの受け渡しをする仕組みである。

Promelaでは`chan name=[n] of {T1, T2, ...}`でチャネルを生成して使う。`n`はバッファ数、`T`はチャネルで受け渡すデータの型を指定する。

チャネルを`c`、受け渡すデータ(メッセージ)を`m`とすると、
- `c!m`でチャネル`c`へメッセージ`m`を送る
- `c?m`でチャネル`c`からメッセージ`m`を受け取る

と書ける。

チャネルを使った送受信をする２つのプロセスのモデル。
```
chan c=[0] of {int}

active proctype snd() {
  int sn=0;
  do
    :: c!sn; sn++
  od
}

active proctype rec() {
  int rn;
  do
    :: c?rn; printf("rec : %d\n", rn)
  od
}
```

実行結果。
```
$ spin -p -l -u10 channel.pml 
  0:    proc  - (:root:) creates proc  0 (snd)
  0:    proc  - (:root:) creates proc  1 (rec)
  1:    proc  0 (snd:1) channel.pml:6 (state 1) [c!sn]
  1:    proc  1 (rec:1) channel.pml:13 (state 1)        [c?rn]
                rec(1):rn = 0
  2:    proc  0 (snd:1) channel.pml:6 (state 2) [sn = (sn+1)]
                snd(0):sn = 1
          rec : 0
  3:    proc  1 (rec:1) channel.pml:13 (state 2)        [printf('rec : %d\\n',rn)]
  4:    proc  1 (rec:1) channel.pml:15 (state 4)        [.(goto)]
  5:    proc  0 (snd:1) channel.pml:8 (state 4) [.(goto)]
  6:    proc  0 (snd:1) channel.pml:6 (state 1) [c!sn]
  6:    proc  1 (rec:1) channel.pml:13 (state 1)        [c?rn]
                rec(1):rn = 1
  7:    proc  0 (snd:1) channel.pml:6 (state 2) [sn = (sn+1)]
                snd(0):sn = 2
          rec : 1
  8:    proc  1 (rec:1) channel.pml:13 (state 2)        [printf('rec : %d\\n',rn)]
  9:    proc  1 (rec:1) channel.pml:15 (state 4)        [.(goto)]
 10:    proc  0 (snd:1) channel.pml:8 (state 4) [.(goto)]
-------------
depth-limit (-u10 steps) reached
#processes: 2
 10:    proc  1 (rec:1) channel.pml:12 (state 3)
 10:    proc  0 (snd:1) channel.pml:5 (state 3)
2 processes created
```

## Path property
「Pを満たす状態からQを満たす状態へ到達可能である」を検証しようとするにはどうしたらよいか？

例えば次のような「Pが成り立ったあとQが成り立たない状態が繰り返される」ことが検出されたら上の性質は成り立たないことが検証できそうである。
⇒ しかし、「Pが成り立ったあとQと!Qを繰り返す」でもこのmonitorに引っかかってしまう。
```
active proctype monitor () {
        (P) ->
accept: do
        :: !(Q)
        od
}
```
### Never claims
SPINには決して起きない挙動を記述するためにNever Claimsと呼ばれる記法がある。

A never claim causes an error if a model completely matches the finite or infinite behavior specified in the claim {...}.

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
