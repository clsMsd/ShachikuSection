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

`nat`型の加算の定義。`plus`のように再帰的な定義の場合`Fixpoint`という宣言で定義する。
```
Fixpoint plus (n : nat) (m : nat) : nat :=
  match n with
    | O ⇒ m
    | S n' ⇒ S (plus n' m)
  end.
```

## 定理の証明
Coqでは定義したデータ型と関数によって定理を設定して、それを証明する。
例えば、「任意の自然数nについて0+n=nが成り立つ」という定理は次のように書ける。
```
Theorem plus_O_n : ∀ n : nat, plus 0 n = n.
```
`∀`は全称量化子と呼ばれ、全ての`∀ n : nat`は「任意の自然数n」という意味になる。

定理が書けたら次は証明を行う。
```
Theorem plus_O_n : ∀ n : nat, plus 0 n = n.
Proof.
  intros n.
  simpl.
  reflexivity.
Qed.
```
証明は`Proof`と`Qed`の間にあるTacticと呼ばれるコマンド列によって表される。
ユーザーはこのTacticコマンドを使ってCoqと対話的に証明を進める。

上の例のTacticコマンドについて1ステップずつ見ていく。
### intro Tactic
`intros`は量化子や仮定を前提条件として取り出すTacticである。
ここでは`∀ n : nat`から「nを任意の自然数とする」という前提条件が得られる。

### simpl Tactic
`simpl`は関数定義に基づいて式を簡約するTacticである。
ここで簡約する式は`plus 0 n`で、これは`plus`の関数定義より`n`に書き換えることができる。

### reflexivity Tactic
`reflexivity`は等式の両辺が同値であることをチェックするTacticである。
ここでは`n = n`について`reflexivity`を適用するのでチェックが通る。

以上の3ステップで定理plus_O_nの証明が完了した。この証明を言葉で書くと「nを任意の自然数であると仮定したとき、0+n=nという式はn=nに簡約され、n=nの両辺は同値であることから任意の自然数nについて0+n=nが成り立つ」となる。

## (rewrite Tactic)
次は「任意の自然数n, mについて、n = mが成り立つならばn + n = m + mが成り立つ」という定理である。
`→`は「ならば」を表し左の式が成り立つとき右の式が成り立つことを示す。
```
Theorem plus_id_example : ∀ n m:nat,
  n = m →
  n + n = m + m.
```
この定理の証明は次のようになる。
```
Proof.
  (* move both quantifiers into the context: *)
  intros n m.
  (* move the hypothesis into the context: *)
  intros H.
  (* rewrite the goal using the hypothesis: *)
  rewrite → H.
  reflexivity. Qed.
```

ここでのポイントは`intros H`と`rewrite → H`である。

`intros H`は定理`n = m → n + n = m + m`の`→`の左辺を前提として取り出している。
取り出された`n = m`は`H`という名前の仮定として登録され、これ以降の証明の中で使うことができる。

次に`rewrite`はこれまでに証明された定理や仮定に基づいて、現在の式を書き換えるTcticである。
ここでは`H`に基づいて書き換えを適用していて、仮定`H : n = m`よりnをmに書き換える。
すると今証明するべき式`n + n = m + m`は`m + m = m + m`に書き換わる。

すると等式の左辺と右辺が同値となり`reflexivity`により証明終了となる。

# 参考文献
- Software Foundations, https://softwarefoundations.cis.upenn.edu/
