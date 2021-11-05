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
    | CSkip
    | CAsgn (x : string) (a : aexp)
    | CSeq (c1 c2 : com)
    | CIf (b : bexp) (c1 c2 : com) 
    | CWhile (b : bexp) (c : com).

End IMP_with_state.