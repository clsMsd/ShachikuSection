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

上記では`aexp`の評価を再帰関数として定義したが、評価を「項」と「値」の間の**関係**として定義することもできる。
評価関係 $\Longrightarrow$ を $Aexp$ と $Nat$ の上の２項関係$\Longrightarrow \subseteq Aexp \times Nat$ とすると、以下の推論規則で定義される。
これらの推論規則はそれぞれ横線の上の関係が成り立つなら下の関係を導き出すことができることを表している。規則 $E\_ANum$ は上段がないが、前提条件なしで関係が成り立つことを表している。

<img src="https://latex.codecogs.com/svg.image?\frac{}{ANum\&space;n&space;\Longrightarrow&space;n}&space;\&space;(EANum)" title="\frac{}{ANum\ n \Longrightarrow n} \ (EANum)" />

<img src="https://latex.codecogs.com/svg.image?\frac{&space;&space;&space;&space;e_1&space;\Longrightarrow&space;n_1&space;\qquad&space;&space;&space;&space;e_2&space;\Longrightarrow&space;n_2&space;&space;&space;&space;}&space;&space;&space;&space;{&space;&space;&space;&space;APlus\&space;e_1\&space;e_2&space;\Longrightarrow&space;n_1&space;&plus;&space;n_2&space;&space;&space;&space;}\&space;(EAPlus)" title="\frac{ e_1 \Longrightarrow n_1 \qquad e_2 \Longrightarrow n_2 } { APlus\ e_1\ e_2 \Longrightarrow n_1 + n_2 }\ (EAPlus)" />

<img src="https://latex.codecogs.com/svg.image?\frac{&space;&space;&space;&space;e_1&space;\Longrightarrow&space;n_1&space;\qquad&space;&space;&space;&space;e_2&space;\Longrightarrow&space;n_2&space;&space;&space;&space;}&space;&space;&space;&space;{&space;&space;&space;&space;AMinus\&space;e_1\&space;e_2&space;\Longrightarrow&space;n_1&space;-&space;n_2&space;&space;&space;&space;}\&space;(EAMinus)" title="\frac{ e_1 \Longrightarrow n_1 \qquad e_2 \Longrightarrow n_2 } { AMinus\ e_1\ e_2 \Longrightarrow n_1 - n_2 }\ (EAMinus)" />

<img src="https://latex.codecogs.com/svg.image?\frac{&space;&space;&space;&space;e_1&space;\Longrightarrow&space;n_1&space;\qquad&space;&space;&space;&space;e_2&space;\Longrightarrow&space;n_2&space;&space;&space;&space;}&space;&space;&space;&space;{&space;&space;&space;&space;AMult\&space;e_1\&space;e_2&space;\Longrightarrow&space;n_1&space;*&space;n_2&space;&space;&space;&space;}\&space;(EAMult)" title="\frac{ e_1 \Longrightarrow n_1 \qquad e_2 \Longrightarrow n_2 } { AMult\ e_1\ e_2 \Longrightarrow n_1 * n_2 }\ (EAMult)" />

上記の推論規則をCoqでは以下のように定義できる。

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

例えば、$APlus\ (ANum \ 1)\ (ANum \ 2) \Longrightarrow 1 + 2$ という評価関係は以下のように推論規則を適用することで導き出すことができる。
このとき、$APlus\ (ANum \ 1)\ (ANum \ 2) \Longrightarrow 1 + 2$ は導出可能であるという。
また、下の図を導出木という。

<img src="https://latex.codecogs.com/svg.image?\frac&space;{\displaystyle&space;&space;&space;&space;&space;&space;&space;\frac&space;{}{ANum&space;\&space;1&space;\Longrightarrow&space;1}&space;\&space;(EANum)&space;&space;&space;&space;&space;&space;&space;\qquad&space;&space;&space;&space;&space;&space;&space;\frac&space;{}{ANum&space;\&space;2&space;\Longrightarrow&space;2}&space;\&space;(EANum)}&space;&space;&space;&space;&space;&space;{APlus\&space;(ANum&space;\&space;1)\&space;(ANum&space;\&space;2)&space;\Longrightarrow&space;1&space;&plus;&space;2}&space;\&space;(EAPlus)" title="\frac {\displaystyle \frac {}{ANum \ 1 \Longrightarrow 1} \ (EANum) \qquad \frac {}{ANum \ 2 \Longrightarrow 2} \ (EANum)} {APlus\ (ANum \ 1)\ (ANum \ 2) \Longrightarrow 1 + 2} \ (EAPlus)" />

Coqにおける証明は、ゴールとなる命題が与えられたとき推論規則を使って導出木を構成することと同じである。
`aevalR (APlus (ANum 1) (ANum 2)) 3`の導出は以下のように書ける。`apply`タクティックは推論規則を適用してゴール(推論規則下段)からサブゴール(推論規則上段)を生成している。

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

`aexp`の評価を再帰関数と評価関係で定義したが、これらが同値であることは以下のように証明できる。

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

続いて、算術式とBoolean式のプログラムに変数を導入する。
ここでは変数と値を対応付けるために、`string`をキーに`nat`を値としたマップ構造を状態`state`として定義する。途中で出てくる`Notation`は中置記法などユーザ定義の構文を導入するコマンドで、ここでは`x !-> v`と書くことで変数名`x`に値`v`を対応させるようにしている。

```coq
(* Defining state *)

Definition state := string -> nat.

Definition empty_st : state :=
    fun _ => 0.

Definition update_st (st : state) (x : string) (n : nat) : state :=
    fun x' => if (string_dec x x') then n else st x'.

Notation "x '!->' n ';' st" := (update_st st x n)
    (at level 100, n at next level, right associativity).
Notation "x '!->' n" := (x !-> n ; empty_st)
    (at level 100).

Definition W : string := "W".
Definition X : string := "X".
Definition Y : string := "Y".
Definition Z : string := "Z".

Compute (X !-> 1; Y !-> 2) X.
(*
= 1
: nat
 *)
```

変数を導入したときのIMPの構文は以下のようになる。ここでは`AId`を追加した。

```coq
(* Defining Syntax *)

Inductive aexp : Type :=
    | ANum : nat -> aexp
    | AId : string -> aexp
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

また、算術式とBoolean式をいちいち`APlus (ANum 3) (AMult (AId "X") (ANum 2))`のように抽象構文木の形で書くと見通しが悪いので、`Notation`で`<{ 3 + (X * 2) }>`という形で書けるようにする。

```coq
(* Defining Notation *)

Coercion AId : string >-> aexp.
Coercion ANum : nat >-> aexp.
Declare Custom Entry com.
Declare Scope com_scope.
Notation "<{ e }>" := e (at level 0, e custom com at level 99) : com_scope.
Notation "( x )" := x (in custom com, x at level 99) : com_scope.
Notation "x" := x (in custom com at level 0, x constr at level 0) : com_scope.
Notation "f x .. y" := (.. (f x) .. y)
                  (in custom com at level 0, only parsing,
                  f constr at level 0, x constr at level 9,
                  y constr at level 9) : com_scope.
Notation "x + y" := (APlus x y) (in custom com at level 50, left associativity).
Notation "x - y" := (AMinus x y) (in custom com at level 50, left associativity).
Notation "x * y" := (AMult x y) (in custom com at level 40, left associativity).
Notation "'true'" := true (at level 1).
Notation "'true'" := BTrue (in custom com at level 0).
Notation "'false'" := false (at level 1).
Notation "'false'" := BFalse (in custom com at level 0).
Notation "x <= y" := (BLe x y) (in custom com at level 70, no associativity).
Notation "x = y" := (BEq x y) (in custom com at level 70, no associativity).
Notation "x && y" := (BAnd x y) (in custom com at level 80, left associativity).
Notation "'~' b" := (BNot b) (in custom com at level 75, right associativity).
Open Scope com_scope.

Check <{ 3 + (X * 2) }>.
(* 
<{ 3 + X * 2 }>
	 : aexp
 *)
```

`aexp`と`bexp`の評価を再帰関数で定義すると以下のように書ける。
`aeval`と`beval`はそれぞれ第１引数に`st : state`を受け取るようになっている。

```coq
(* Defining Evaluation as a function *)

Fixpoint aeval (st : state) (a : aexp) : nat :=
    match a with
    | ANum n => n
    | AId x => st x
    | <{a1 + a2}> => (aeval st a1) + (aeval st a2)
    | <{a1 - a2}> => (aeval st a1) - (aeval st a2)
    | <{a1 * a2}> => (aeval st a1) * (aeval st a2)
    end.

Fixpoint beval (st : state) (b : bexp) : bool :=
    match b with
    | <{true}> => true
    | <{false}> => false
    | <{a1 = a2}> => (aeval st a1) =? (aeval st a2)
    | <{a1 <= a2}> => (aeval st a1) <=? (aeval st a2)
    | <{~ b1}> => negb (beval st b1)
    | <{b1 && b2}> => andb (beval st b1) (beval st b2)
    end.

Compute aeval (X !-> 5) <{ 3 + (X * 2) }>.
(* 
= 13
: nat
 *)
```

続いて、IMPに`if`や`while`などの文(statements)を導入する。
BNFで書くと以下のようになる。


```
    c := skip
        | x := a
        | c ; c
        | if b then c else c end
        | while b do c end
```

Coqで書くと以下のようになる。

```coq
(* Defining Syntax *)

Inductive com : Type :=
    | CSkip : com
    | CAsgn : string -> aexp -> com
    | CSeq : com -> com -> com
    | CIf : bexp -> com -> com -> com
    | CWhile : bexp -> com -> com.
```

`aexp`や`bexp`と同様に、`com`も`Notation`で読み書きしやすいようにする。

```coq
(* Defining Notation *)

Notation "'skip'" :=
         CSkip (in custom com at level 0) : com_scope.
Notation "x := y" :=
         (CAsgn x y)
            (in custom com at level 0, x constr at level 0,
             y at level 85, no associativity) : com_scope.
Notation "x ; y" :=
         (CSeq x y)
           (in custom com at level 90, right associativity) : com_scope.
Notation "'if' x 'then' y 'else' z 'end'" :=
         (CIf x y z)
           (in custom com at level 89, x at level 99,
            y at level 99, z at level 99) : com_scope.
Notation "'while' x 'do' y 'end'" :=
         (CWhile x y)
            (in custom com at level 89, x at level 99, y at level 99) : com_scope.

Definition fact_in_coq : com :=
    <{
        Z := X;
        Y := 1;
        while ~(Z = 0) do
            Y := Y * Z;
            Z := Z - 1
        end
    }>.
```

`com`の評価を再帰関数で定義しようとすると、エラーが発生する。
これは、`ceval`の`while`のケースで`ceval st <{ while b do c end }>`のように`ceval`の引数をそのまま再度`ceval`に渡している場合があり`ceval`が停止しない場合があるためである。
一般に、他のプログラミング言語であれば以下のような再帰関数(停止しない関数)の定義は許されているが、Coqでは`Fixpoint`で定義される関数は停止されることが保証されている必要がある。

```coq
(* Defining Evaluation as a function (Error) *)

Fixpoint ceval (st : state) (c : com) : state :=
    match c with
        | <{ skip }> =>
            st
        | <{ x := a }> =>
            (x !-> (aeval st a) ; st)
        | <{ c1 ; c2 }> =>
            let st' := ceval st c1 in
            ceval st' c2
        | <{ if b then c1 else c2 end}> =>
            if (beval st b)
            then ceval st c1
            else ceval st c2
        | <{ while b do c end }> =>
            if (beval st b)
            then ceval st <{ while b do c end }>
            else st
    end.

(* 
Cannot guess decreasing argument of fix.
 *)
```

そのため`com`は評価関係で定義するほうが適している。
`st =[ c ]=> st'`はある状態`st`において`c`を実行すると状態`st'`で停止することを表す。
このとき、評価関係は以下の推論規則で定義される。
規則 $EWhileTrue$ は、`b`が`true`に評価できて、かつ、`st`において`while`のボディである`c`を実行すると`st'`で停止して、かつ、`st'`において`while`全体である`while b do c end`を実行すると`st''`で停止するとき、`st`において`while b do c end`を実行すると`st''`で停止することが導出できることを表している。この規則により、停止するプログラムのみ導出可能となる。

<img src="https://latex.codecogs.com/svg.image?\frac{}{&space;\texttt{st&space;=[&space;skip&space;]=>&space;st}&space;}\&space;(ESkip)" title="\frac{}{ \texttt{st =[ skip ]=> st} }\ (ESkip)" />

<img src="https://latex.codecogs.com/svg.image?\frac{&space;\texttt{aeval&space;st&space;a&space;=&space;n}&space;}&space;&space;&space;&space;&space;{&space;\texttt{st&space;=[&space;x&space;:=&space;a&space;]=>&space;(x&space;!->&space;n&space;;&space;st)}&space;}\&space;(EAsgn)" title="\frac{ \texttt{aeval st a = n} } { \texttt{st =[ x := a ]=> (x !-> n ; st)} }\ (EAsgn)" />

<img src="https://latex.codecogs.com/svg.image?\frac{&space;\texttt{st&space;=[&space;c1&space;]=>&space;st'}&space;\qquad&space;&space;&space;&space;&space;&space;&space;\texttt{st'&space;=[&space;c2&space;]=>&space;st''}&space;}&space;&space;&space;&space;&space;{&space;\texttt{st&space;=[&space;c1;c2&space;]=>&space;st''}&space;}\&space;(ESeq)" title="\frac{ \texttt{st =[ c1 ]=> st'} \qquad \texttt{st' =[ c2 ]=> st''} } { \texttt{st =[ c1;c2 ]=> st''} }\ (ESeq)" />

<img src="https://latex.codecogs.com/svg.image?\frac{&space;\texttt{beval&space;st&space;b&space;=&space;true}&space;\qquad&space;&space;&space;&space;&space;&space;&space;\texttt{st&space;=[&space;c1&space;]=>&space;st'}&space;}&space;&space;&space;&space;&space;{&space;\texttt{st&space;=[&space;if&space;b&space;then&space;c1&space;else&space;c2&space;end&space;]=>&space;st'}&space;}\&space;(EIfTrue)" title="\frac{ \texttt{beval st b = true} \qquad \texttt{st =[ c1 ]=> st'} } { \texttt{st =[ if b then c1 else c2 end ]=> st'} }\ (EIfTrue)" />

<img src="https://latex.codecogs.com/svg.image?\frac{&space;\texttt{beval&space;st&space;b&space;=&space;false}&space;\qquad&space;&space;&space;&space;&space;&space;&space;\texttt{st&space;=[&space;c2&space;]=>&space;st'}&space;}&space;&space;&space;&space;&space;{&space;\texttt{st&space;=[&space;if&space;b&space;then&space;c1&space;else&space;c2&space;end&space;]=>&space;st'}&space;}\&space;(EIfFalse)" title="\frac{ \texttt{beval st b = false} \qquad \texttt{st =[ c2 ]=> st'} } { \texttt{st =[ if b then c1 else c2 end ]=> st'} }\ (EIfFalse)" />

<img src="https://latex.codecogs.com/svg.image?\frac{&space;\texttt{beval&space;st&space;b&space;=&space;false}&space;}&space;&space;&space;&space;&space;{&space;\texttt{st&space;=[&space;while&space;b&space;do&space;c&space;end&space;]=>&space;st}&space;}\&space;(EWhileFalse)" title="\frac{ \texttt{beval st b = false} } { \texttt{st =[ while b do c end ]=> st} }\ (EWhileFalse)" />

<img src="https://latex.codecogs.com/svg.image?\frac{&space;\texttt{beval&space;st&space;b&space;=&space;true}&space;\qquad&space;&space;&space;&space;&space;&space;&space;\texttt{st&space;=[&space;c&space;]=>&space;st'}&space;\qquad&space;&space;&space;&space;&space;&space;&space;\texttt{st'&space;=[&space;while&space;b&space;do&space;c&space;end&space;]=>&space;st''}&space;&space;&space;&space;&space;&space;}&space;&space;&space;&space;&space;{&space;\texttt{st&space;=[&space;while&space;b&space;do&space;c&space;end&space;]=>&space;st''}&space;}\&space;(EWhileTrue)" title="\frac{ \texttt{beval st b = true} \qquad \texttt{st =[ c ]=> st'} \qquad \texttt{st' =[ while b do c end ]=> st''} } { \texttt{st =[ while b do c end ]=> st''} }\ (EWhileTrue)" />

上記の推論規則をCoqでは以下のように定義できる。

```coq
Reserved Notation
         "st '=[' c ']=>' st'"
         (at level 40, c custom com at level 99,
          st constr, st' constr at next level).
Inductive ceval : com -> state -> state -> Prop :=
    | E_Skip : forall st,
        st =[ skip ]=> st
    | E_Asgn : forall st a n x,
        aeval st a = n ->
        st =[ x := a ]=> (x !-> n ; st)
    | E_Seq : forall c1 c2 st st' st'',
        st =[ c1 ]=> st' ->
        st' =[ c2 ]=> st'' ->
        st =[ c1 ; c2 ]=> st''
    | E_IfTrue : forall st st' b c1 c2,
        beval st b = true ->
        st =[ c1 ]=> st' ->
        st =[ if b then c1 else c2 end]=> st'
    | E_IfFalse : forall st st' b c1 c2,
        beval st b = false ->
        st =[ c2 ]=> st' ->
        st =[ if b then c1 else c2 end]=> st'
    | E_WhileFalse : forall b st c,
        beval st b = false ->
        st =[ while b do c end ]=> st
    | E_WhileTrue : forall st st' st'' b c,
        beval st b = true ->
        st =[ c ]=> st' ->
        st' =[ while b do c end ]=> st'' ->
        st =[ while b do c end ]=> st''
    where "st =[ c ]=> st'" := (ceval c st st').
```

例えば、`empty_st =[ X := 2; if X <= 1 then Y := 3 else Z := 4 end ]=> (Z !-> 4; X !-> 2)`という評価関係は以下のように推論規則を適用することで導き出すことができる。

$$
\frac{\displaystyle
      \frac{\displaystyle
        \verb+ aeval empty_st 2 = 2 +
      }
      {
        \verb+ empty_st =[ X := 2 ]=> (X !-> 2) +
      } \ (EAsgn)
      \qquad
      \frac{\displaystyle
        \verb+ beval (X !-> 2) <{ X <= 1 }> = false + \qquad
        \frac{\displaystyle
          \verb+ aeval (X !-> 2) 4 = 4 +
        }
        {
          \verb+ (X !-> 2) =[ Z := 4 ]=> (Z !-> 4; X !-> 2) +
        } \ (EAsgn)
      }
      {
        \verb+ (X !-> 2) =[ if X <= 1 then Y := 3 else Z := 4 end ]=> (Z !-> 4; X !-> 2) +
      } \ (EIfFalse)
     }
     {\verb+ empty_st =[ X := 2; if X <= 1 then Y := 3 else Z := 4 end ]=> (Z !-> 4; X !-> 2) +} \ (ESeq)
$$

Coqでは以下のように書ける。

```coq
Example ceval_example1:
    empty_st =[
        X := 2;
        if (X <= 1)
            then Y := 3
            else Z := 4
        end
    ]=> (Z !-> 4 ; X !-> 2).
Proof.
    apply E_Seq with (X !-> 2).
    - apply E_Asgn. simpl. reflexivity.
    - apply E_IfFalse.
      + simpl. reflexivity.
      + apply E_Asgn. simpl. reflexivity.
Qed.
```

# 参考文献
- SOFTWARE FOUNDATIONS VOLUME 1 - IMP, https://softwarefoundations.cis.upenn.edu/lf-current/Imp.html
- 計算と論理, 五十嵐 淳, https://www.fos.kuis.kyoto-u.ac.jp/~igarashi/class/cal20w/
