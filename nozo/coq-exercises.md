# coq演習問題
## destruct Tactic
次の定理は「全ての`bool`型の値b,cについて、b ∧ c = c ∧ bが成り立つ」という意味の定理である。
```
Theorem andb_commutative : ∀ b c : bool, andb b c = andb c b.
```
この定理は`andb`関数について簡約できる部分がないため`simpl`Tacticは使えない。
また、この定理から得られる仮定は`∀ b c : bool`であり`rewrite`Tacticを使った変換もできない。

こういった場合、`destruct`Tacticを使う。
証明は次のように書ける。
```
Theorem andb_commutative : ∀ b c : bool, andb b c = andb c b.
Proof.
  intros b c. destruct b.
  - destruct c.
    + simpl. reflexivity.
    + simpl. reflexivity.
  - destruct c.
    + simpl. reflexivity.
    + simpl. reflexivity.
Qed.
```

`destruct`Tacticは場合分けのためのコマンドで、ある値についてその値の型を構成する要素について場合分けを行う。
上の証明では`bool`型の値`b`と`c`についてそれぞれ`destruct b`で「`b`がTrueの場合」と「`b`がFalseの場合」に、`destruct c`で「`c`がTrueの場合」と「`c`がFalseの場合」に場合分けしている。

場合分けされた値はそれぞれの場合の具体値が割り当てられ、場合毎のサブゴールが生成される。
```
destruct 変数
  - 変数に具体値が入ったサブゴール
  - 変数に具体値が入ったサブゴール
  ...
```

上の証明では例えば１つ目の場合は「`b`と`c`がTrue」であり、サブゴールは`andb True True = andb True True`となる。
このサブゴールは`simpl`すると`True = True`となり`reflexivity`で示せる。

他の場合も`simpl`と`reflexivity`で示すことができ、すべてのサブゴールが示せたら証明終了めある。

### 演習
```
Theorem plus_1_neq_0 : ∀ n : nat, beq_nat (n + 1) 0 = false.
```

## induction Tactic
`destruct`でも証明できないものもある。
次の定理は「全ての自然数`n`についてn = n + 0が成り立つ」という意味の定理である。
```
Theorem plus_n_O_secondtry : ∀ n:nat, n = n + 0.
```

```
Theorem plus_comm : ∀ n m : nat, n + m = m + n.
```

# 参考文献
- Software Foundations, https://softwarefoundations.cis.upenn.edu/
