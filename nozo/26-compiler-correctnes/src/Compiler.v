From Coq Require Import Lists.List.
Import ListNotations.

(* Source Language *)
Inductive exp : Type :=
    | Val (n : nat)
    | Add (e1 : exp) (e2 : exp).

Fixpoint eval (e : exp) : nat :=
    match e with
    | Val n     => n
    | Add e1 e2 => (eval e1) + (eval e2)
    end.

Compute eval (Add (Val 1) (Val 2)).

(* Target machine code *)
Inductive op : Type :=
    | PUSH (n : nat)
    | ADD.
Definition stack := list nat.
Definition code := list op.

Fixpoint exec (c : code) (s : stack) : stack :=
    match c with
    | []           => s
    | (PUSH n)::cs => exec cs (n::s)
    | ADD     ::cs => match s with
                      | n1::n2::ss => exec cs ((n2+n1)::ss)
                      (* Ignore op if the stack size is less than 2. *)
                      | _          => s
                      end
    end.

Compute exec [PUSH 1; PUSH 2; ADD] [].

(* Compiler *)
Fixpoint comp (e : exp) : code :=
    match e with
    | Val n     => [PUSH n]
    | Add e1 e2 => (comp e1) ++ (comp e2) ++ [ADD]
    end.

Compute comp (Add (Val 1) (Val 2)).

(* Test compiler *)
Definition test_exp := (Add (Val 1) (Val 2)).
Example test_comp_correctness:
    exec (comp test_exp) [] = [eval test_exp].
Proof. simpl. reflexivity. Qed. 
