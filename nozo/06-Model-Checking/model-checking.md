# モデル検査の紹介

## モデル検査とは？

## SPIN model checker
モデル記述言語Promela(Process Meta Language)で記述された並行システムを検証するツール。

## 線形時相論理
LTL(Linear-time Temporal Logic)

LTLの構文
```
AP  ::= atomic formula (including true & false)

φ,Ψ ::= AP
      | ¬ φ | φ ∧ Ψ | φ ∨ Ψ | φ ⇒ Ψ
      | [] φ  (always φ)
      | <> φ  (eventually φ)
      | X  φ  (φ holds next)
      | φ U Ψ (φ until Ψ)
      | φ W Ψ (weak version of until)
      | φ R Ψ (φ releases Ψ)
```

## 参考文献
- 早稲田大学 高信頼ソフトウェア, http://www.ueda.info.waseda.ac.jp/oess/RS2018/
- SPIN model checker, http://spinroot.com/spin/whatispin.html
