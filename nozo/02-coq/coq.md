# 定理証明支援系Coqの紹介
$$
\frac{\frac{\displaystyle \frac{P \land Q}{P} \qquad \frac{P \land Q}{Q}}{\displaystyle Q \land P} \qquad Q \land P \to R}{R}
$$

## データ型と関数の定義

```
Inductive bool : Type :=
  | true : bool
  | false : bool.
```
```
Inductive nat : Type :=
  | O : nat
  | S : nat → nat.
```
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
### intro tactic
### simpl tactic
### rewrite tactic
### destruct tactic
## 例題：自然数の加算における交換則の証明
### induction tactic
# 参考文献
- Software Foundations, https://softwarefoundations.cis.upenn.edu/
