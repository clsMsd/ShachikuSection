(* ex1 *)
Theorem andb_comm : forall b c : bool,
    andb b c = andb c b.
Proof.
  intros.
  destruct b.
  - destruct c.
    + simpl. reflexivity.
    + simpl. reflexivity.
  - destruct c.
    + simpl. reflexivity.
    + simpl. reflexivity.
Qed.

(* ex2 *)
Fixpoint beq_nat (n m : nat) : bool :=
  match n with
  | O    => match m with
            | O    => true
            | S m' => false
            end
  | S n' => match m with
            | O    => false
            | S m' => beq_nat n' m'
            end
  end.

Theorem plus_1_neq_0 : forall n : nat,
    beq_nat (n + 1) 0 = false.
Proof.
  intros.
  destruct n as [| n'].
  - simpl. reflexivity.
  - simpl. reflexivity.
Qed.

(* ex3 *)
Theorem plus_n_0_snd : forall n : nat,
    n = n + 0.
Proof.
  intros.
  destruct n as [| n'].
  - simpl. reflexivity.
  - simpl.
    destruct n' as [| n''].
    + simpl. reflexivity.
    + simpl.
Abort.

Theorem plus_n_0_snd : forall n : nat,
    n = n + 0.
Proof.
  intros.
  induction n as [| n' IHn'].
  - (* n = 0 *)
    simpl.
    reflexivity.
  - (* n = S n' *)
    simpl.
    rewrite <- IHn'.
    reflexivity.
Qed.

(* ex4 *)
Theorem plus_n_Sm : forall n m : nat,
    n + S m = S (n + m).
Proof.
  intros.
  induction n.
  - simpl. reflexivity.
  - simpl.
    rewrite <- IHn.
    reflexivity.
Qed.
    
Theorem plus_comm : forall n m : nat,
    n + m = m + n.
Proof.
  intros.
  induction n.
  - simpl.
    rewrite <- plus_n_0_snd.
    reflexivity.
  - simpl.
    rewrite -> plus_n_Sm.
    rewrite -> IHn.
    reflexivity.
Qed.
