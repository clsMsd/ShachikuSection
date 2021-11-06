From Coq Require Import Bool.Bool.
From Coq Require Import Init.Nat.
From Coq Require Import Arith.Arith.
From Coq Require Import Arith.EqNat. Import Nat.
From Coq Require Import Strings.String.

Module IMP_without_state.
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

Compute aeval (APlus (ANum 1) (ANum 2)).
(*
= 3
: nat
 *)

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
End IMP_without_state.



Module IMP_with_state.

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

(* Defining Syntax *)

Inductive com : Type :=
    | CSkip : com
    | CAsgn : string -> aexp -> com
    | CSeq : com -> com -> com
    | CIf : bexp -> com -> com -> com
    | CWhile : bexp -> com -> com.

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

(* Defining Evaluation as a function (Error) *)

(* 
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
 *)
(* 
Cannot guess decreasing argument of fix.
 *)

(* Defining Evaluation as a relation *)

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

Example ceval_loop: forall st st',
    ~ (st =[
        while true do skip end
    ]=> st').
Proof.
    intros st st' contra.
Abort.

End IMP_with_state.