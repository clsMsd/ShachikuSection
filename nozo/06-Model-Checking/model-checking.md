# モデル検査の紹介

## モデル検査とは？

## SPIN model checker
モデル記述言語Promela(Process Meta Language)で記述された並行システムを検証するツール。

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
| `φ U Ψ` | `φ`が成り立つまで`Ψ`が成り立つ |

## 参考文献
- 早稲田大学 高信頼ソフトウェア, http://www.ueda.info.waseda.ac.jp/oess/RS2018/
- SPIN model checker, http://spinroot.com/spin/whatispin.html
