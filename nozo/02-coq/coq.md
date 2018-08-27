# 定理証明支援系Coqの紹介
$$
\frac{\frac{\displaystyle \frac{P \land Q}{P} \qquad \frac{P \land Q}{Q}}{\displaystyle Q \land P} \qquad Q \land P \to R}{R}
$$

## データ型と関数の定義
データ型と関数は一般的な関数型言語と同様に定義することができる。

### データ型
次の定義は`bool`型の定義で、値`true`と`false`が`bool`型に属することを示す。
```
Inductive bool : Type :=
  | true : bool
  | false : bool.
```
次の定義は自然数`nat`型の定義である。
```
Inductive nat : Type :=
  | O : nat
  | S : nat → nat.
```
値`O`が0を表し、1以降を次のように表す。
```
1 := S O
2 := S (S O)
3 := S (S (S O))
...
```

### 関数
```
Definition negb (b:bool) : bool :=
  match b with
  | true ⇒ false
  | false ⇒ true
  end.

Definition andb (b1:bool) (b2:bool) : bool :=
  match b1 with
  | true ⇒ b2
  | false ⇒ false
  end.
```
```
Fixpoint plus (n : nat) (m : nat) : nat :=
  match n with
    | O ⇒ m
    | S n' ⇒ S (plus n' m)
  end.
```
## 定理の証明
Coqでは定義したデータ型と関数によって定理をつくり、それを証明する。

### intro tactic
### simpl tactic
### rewrite tactic
### destruct tactic
## 例題：自然数の加算における交換則の証明
### induction tactic
# 参考文献
- Software Foundations, https://softwarefoundations.cis.upenn.edu/
