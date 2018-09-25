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
    + reflexivity.
    + reflexivity.
  - destruct c.
    + reflexivity.
    + reflexivity.
Qed.
```

`destruct`Tacticは場合分けのためのコマンドで、

```
Theorem plus_1_neq_0 : ∀ n : nat, beq_nat (n + 1) 0 = false.
```

## induction Tactic

```
Theorem plus_n_O_secondtry : ∀ n:nat, n = n + 0.
```

```
Theorem plus_comm : ∀ n m : nat, n + m = m + n.
```
