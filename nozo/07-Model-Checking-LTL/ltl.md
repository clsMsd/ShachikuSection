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
