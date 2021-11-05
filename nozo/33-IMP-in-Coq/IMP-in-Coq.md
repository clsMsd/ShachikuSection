# IMP

命令型プログラミング言語(IMP)をCoqの上で定義して検証する。
まずはじめにIMPの項となる算術式とBoolean式を定義する。BNFで書くと以下のようになる。

```
    a := nat
        | a + a
        | a - a
        | a × a

    b := true
        | false
        | a = a
        | a ≤ a
        | ¬b
        | b && b
```

Coqで定義すると以下のようになる。

```coq
(* Defining Syntax *)

Inductive aexp : Type :=
    | ANum : nat -> aexp
    | APlus : aexp -> aexp -> aexp
    | AMinus : aexp -> aexp -> aexp
    | AMult : aexp -> aexp -> aexp.

Inductive bexp : Type :=
    | BTrue : bexp
    | BFalse : bexp
    | BEq : aexp -> aexp -> bexp
    | BLe : aexp -> aexp -> bexp
    | BNot : bexp -> bexp
    | BAnd : bexp -> bexp -> bexp.
```

次に`aexp`と`bexp`の評価を再帰関数として定義すると以下のように書ける。

```coq
(* Defining Evaluation as a function *)

Fixpoint aeval (a : aexp) : nat :=
    match a with
    | ANum n => n
    | APlus a1 a2 => (aeval a1) + (aeval a2)
    | AMinus a1 a2 => (aeval a1) - (aeval a2)
    | AMult a1 a2 => (aeval a1) * (aeval a2)
    end.

Fixpoint beval (b : bexp) : bool :=
    match b with
    | BTrue => true
    | BFalse => false
    | BEq a1 a2 => (aeval a1) =? (aeval a2)
    | BLe a1 a2 => (aeval a1) <=? (aeval a2)
    | BNot b1 => negb (beval b1)
    | BAnd b1 b2 => andb (beval b1) (beval b2)
    end.
```

例えば`1 + 2`は`(APlus (ANum 1) (ANum 2))`で表現することができて、`aeval`を適用すると`3`が返ってくる。

```coq
Compute aeval (APlus (ANum 1) (ANum 2)).
(*
= 3
: nat
 *)
```

上記では`aexp`と`bexp`の評価を再帰関数として定義したが、評価を「項」と「値」の間の**関係**として定義することもできる。

$$
\frac{}{ANum\ n \Longrightarrow n} \ (E\_ANum)
$$

$$
\frac{
    e_1 \Longrightarrow n_1 \qquad
    e_2 \Longrightarrow n_2
    }
    {
    APlus\ e_1\ e_2 \Longrightarrow n_1 + n_2
    }\ (E\_APlus)
$$

$$
\frac{
    e_1 \Longrightarrow n_1 \qquad
    e_2 \Longrightarrow n_2
    }
    {
    AMinus\ e_1\ e_2 \Longrightarrow n_1 - n_2
    }\ (E\_AMinus)
$$

$$
\frac{
    e_1 \Longrightarrow n_1 \qquad
    e_2 \Longrightarrow n_2
    }
    {
    AMult\ e_1\ e_2 \Longrightarrow n_1 * n_2
    }\ (E\_AMult)
$$

```coq
(* Defining Evaluation as a relation *)

Inductive aevalR : aexp -> nat -> Prop :=
    | E_ANum : forall n : nat,
        aevalR (ANum n) n
    | E_APlus : forall (e1 e2 : aexp) (n1 n2 : nat),
        aevalR e1 n1 ->
        aevalR e2 n2 ->
        aevalR (APlus e1 e2) (n1 + n2)
    | E_AMinus : forall (e1 e2 : aexp) (n1 n2 : nat),
        aevalR e1 n1 ->
        aevalR e2 n2 ->
        aevalR (AMinus e1 e2) (n1 - n2)
    | E_AMult : forall (e1 e2 : aexp) (n1 n2 : nat),
        aevalR e1 n1 ->
        aevalR e2 n2 ->
        aevalR (AMult e1 e2) (n1 * n2).
```

$$
\frac {\displaystyle
       \frac {}{ANum \ 1 \Longrightarrow 1} \ (E\_ANum)
       \qquad
       \frac {}{ANum \ 2 \Longrightarrow 2} \ (E\_ANum)}
      {APlus\ (ANum \ 1)\ (ANum \ 2) \Longrightarrow 1 + 2} \ (E\_APlus)
$$

```coq
Example aevalR_ex : aevalR (APlus (ANum 1) (ANum 2)) 3.
Proof.
    apply (E_APlus (ANum 1) (ANum 2) 1 2).
    - apply E_ANum.
    - apply E_ANum.
Qed.
Print aevalR_ex.
(* 
aevalR_ex = 
E_APlus (ANum 1) (ANum 2) 1 2 (E_ANum 1) (E_ANum 2)
	 : aevalR (APlus (ANum 1) (ANum 2)) 3
*)
```

```coq
Theorem aeval_iff_aevalR : forall a n,
    aevalR a n <-> aeval a = n.
Proof.
    split.
    - (* -> *)
      intros H.
      induction H.
      + (* E_ANum n *)
        simpl. reflexivity.
      + (* E_APlus *)
        simpl.
        rewrite IHaevalR1.
        rewrite IHaevalR2.
        reflexivity.
      + (* E_AMinus *)
        simpl.
        rewrite IHaevalR1.
        rewrite IHaevalR2.
        reflexivity.
      + (* E_AMult *)
        simpl.
        rewrite IHaevalR1.
        rewrite IHaevalR2.
        reflexivity.
    - (* <- *)
      generalize dependent n.
      induction a.
      + (* ANum *)
        intros n0 H.
        simpl in H.
        rewrite H.
        apply E_ANum.
      + (* APlus *)
        intros n0 H.
        simpl in H.
        rewrite <- H.
        apply E_APlus.
        * apply IHa1. reflexivity.
        * apply IHa2. reflexivity.
      + (* AMinus *)
        intros n0 H.
        simpl in H.
        rewrite <- H.
        apply E_AMinus.
        * apply IHa1. reflexivity.
        * apply IHa2. reflexivity.
      + (* AMult *)
        intros n0 H.
        simpl in H.
        rewrite <- H.
        apply E_AMult.
        * apply IHa1. reflexivity.
        * apply IHa2. reflexivity.
Qed.
```

# 参考文献
- SOFTWARE FOUNDATIONS VOLUME 1 - IMP, https://softwarefoundations.cis.upenn.edu/lf-current/Imp.html
- 計算と論理, 五十嵐 淳, https://www.fos.kuis.kyoto-u.ac.jp/~igarashi/class/cal20w/