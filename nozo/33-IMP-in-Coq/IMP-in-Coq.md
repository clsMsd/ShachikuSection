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

```coq
(* Defining state *)

Definition total_map (A : Type) := string -> A.

Definition eqb_string (x y : string) : bool :=
    if string_dec x y then true else false.

Definition t_empty {A : Type} (v : A) : total_map A :=
    (fun _ => v).

Definition t_update {A : Type} (m : total_map A)
                    (x : string) (v : A)
                    : total_map A :=
    fun x' => if (eqb_string x x') then v else m x'.

Notation "'_' '!->' v" := (t_empty v)
    (at level 100, right associativity).
Notation "x '!->' v ';' m" := (t_update m x v)
    (at level 100, v at next level, right associativity).

Definition state := total_map nat.
Definition empty_st := (_ !-> 0).
Notation "x '!->' v" := (x !-> v ; empty_st)
    (at level 100).
```

```coq
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

```
    c := skip
      | x := a
      | c ; c
      | if b then c else c end
      | while b do c end
```

```coq
(* Defining Syntax *)

Inductive com : Type :=
    | CSkip : com
    | CAsgn : string -> aexp -> com
    | CSeq : com -> com -> com
    | CIf : bexp -> com -> com -> com
    | CWhile : bexp -> com -> com.
```

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

$$
\frac{}{\verb+ st =[ skip ]=> st +}\ (ESkip)
$$

$$
\frac{\verb+ aeval st a = n +}
     {\verb+ st =[ x := a ]=> (x !-> n ; st) +}\ (EAsgn)
$$

$$
\frac{\verb+ st =[ c1 ]=> st' +\qquad
      \verb+ st' =[ c2 ]=> st'' +}
     {\verb+ st =[ c1;c2 ]=> st'' +}\ (ESeq)
$$

$$
\frac{\verb+ beval st b = true +\qquad
      \verb+ st =[ c1 ]=> st' +}
     {\verb+ st =[ if b then c1 else c2 end ]=> st' +}\ (EIfTrue)
$$

$$
\frac{\verb+ beval st b = false +\qquad
      \verb+ st =[ c2 ]=> st' +}
     {\verb+ st =[ if b then c1 else c2 end ]=> st' +}\ (EIfFalse)
$$

$$
\frac{\verb+ beval st b = false +}
     {\verb+ st =[ while b do c end ]=> st +}\ (EWhileFalse)
$$

$$
\frac{\verb+ beval st b = true +\qquad
      \verb+ st =[ c ]=> st' +\qquad
      \verb+ st' =[ while b do c end ]=> st'' +
     }
     {\verb+ st =[ while b do c end ]=> st'' +}\ (EWhileTrue)
$$

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