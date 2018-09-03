# 定理証明支援系Coqの紹介
プログラムを検証する手法は大きく分けてテストと証明の2つがある。Coqはプログラムの証明を対話的に行う事ができる証明の支援ツールのひとつである。

テストはプログラムへの入力のうちいくつかをピックアップしてその出力が期待したものであることを検証する手法であることに対して、証明は例えば「任意の自然数を入力したとき出力はある性質を満たす」といった検証が可能である。

Coq(https://coq.inria.fr)

## データ型と関数の定義
Coqでは、データ型と関数を一般的な関数型言語と同様に定義することができる。

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
`bool`型の関数の定義
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

`nat`型の加算の定義
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
