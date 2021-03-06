# coq演習問題
## destruct Tactic
次の定理は「全ての`bool`型の値`b`,`c`について、`andb b c = andb c b`が成り立つ」という意味の定理である。
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
次の定理は「全ての自然数`n`について`n = n + 0`が成り立つ」という意味の定理である。
```
Theorem plus_n_O_secondtry : ∀ n:nat, n = n + 0.
```

この定理は`destruct`を使っても下の証明のように行き詰まる。
```
Theorem plus_n_O_secondtry : ∀ n:nat,
  n = n + 0.
Proof.
  intros n. destruct n as [| n'].
  - (* n = 0 の場合 *)
    reflexivity.
  - (* n = S n' の場合 *)
    simpl. (* ここで行き詰まる *)
Abort.
```
`n = 0`の場合のサブゴールは`0 = 0 + 0`であり自明。
`n = S n'`の場合のサブゴールは`S n' = S n' + 0`であり、`simpl`によって`S n' = S (n' + 0)`という式に簡約できる。
しかし、`n' + 0`という部分が残ってしまい行き詰まってしまう。

こういった場合、`induction`Tcaticを使う。
`induction`は帰納法による証明を適用するコマンドである。
自然数における帰納法は次のように定義される。

次の２つが成り立つとき、任意の自然数`n`について`P(n)`が成り立つ
- `P(0)`が成り立つ
- 任意の自然数`n'`について`P(n') -> P(S n')`が成り立つ

`induction`を使うと次のように証明できる。

```
Theorem plus_n_O : ∀ n:nat, n = n + 0.
Proof.
  intros n. induction n as [| n' IHn'].
  - (* 第１ケース *)
    reflexivity.
  - (* 第２ケース *)
    simpl.
    rewrite <- IHn'.
    reflexivity.
Qed.
```

帰納法の第１ケースは`0 = 0 + 0`が成り立つことを示せば良くてこれは`destruct`と同様に示せる。
第２ケースは`n' = n' + 0 -> S n' = S n' + 0`が成り立つことを示せば良い。
第２ケースに入ると仮定として`n' = n' + 0`が得られて、それを元に`S n' = S n' + 0`に示すことができる。

### 演習
```
Theorem plus_comm : ∀ n m : nat, n + m = m + n.
```

# 参考文献
- Software Foundations, https://softwarefoundations.cis.upenn.edu/

