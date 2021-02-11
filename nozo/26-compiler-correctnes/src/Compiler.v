From Coq Require Import Lists.List.
Import ListNotations.

(* ソース言語の定義 *)
Inductive exp : Type :=
    | Val (n : nat)
    | Add (e1 : exp) (e2 : exp).

Fixpoint eval (e : exp) : nat :=
    match e with
    | Val n     => n
    | Add e1 e2 => (eval e1) + (eval e2)
    end.

Compute eval (Add (Val 1) (Val 2)).

(* ターゲットコードの定義 *)
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
                      (* スタックサイズが2より小さい場合は命令を無視する *)
                      | _          => exec cs s
                      end
    end.

Compute exec [PUSH 1; PUSH 2; ADD] [].

(* コンパイラの定義 *)
Fixpoint comp (e : exp) : code :=
    match e with
    | Val n     => [PUSH n]
    | Add e1 e2 => (comp e1) ++ (comp e2) ++ [ADD]
    end.

Compute comp (Add (Val 1) (Val 2)).

(* コンパイラの正しさのテスト *)
Definition test_exp := (Add (Val 1) (Val 2)).
Example test_comp_correctness:
    exec (comp test_exp) [] = [eval test_exp].
Proof. simpl. reflexivity. Qed.

(* スタックサイズが2より小さい場合にADD命令を実行するケース *)
Compute exec ([ADD]++[PUSH 1]) [] = exec [PUSH 1] (exec [ADD] []).

(* 分配法則 *)
Lemma exec_distr: forall (c1 c2 : code) (s : stack),
    exec (c1 ++ c2) s = exec c2 (exec c1 s).
Proof.
    intros c1 c2.
    induction c1 as [| o c1' IHc1'].
    - (* c1 = [] *)
      intros s.
      simpl.
      reflexivity.
    - intros s.
      destruct o.
      { (* o = PUSH n *)
        simpl.
        rewrite -> IHc1'.
        reflexivity.
      }
      { (* o = ADD *)
        destruct s.
        { (* s = [] *)
          simpl.  (* [] = exec c2 [] *)
          rewrite -> IHc1'.
          reflexivity.
        }
        { destruct s.
          { (* s = n::[] *)
            simpl.
            rewrite -> IHc1'.
            reflexivity.
          }
          { (* s = n::n0::[] *)
            simpl.
            rewrite -> IHc1'.
            reflexivity.
          }
        }
      }
Qed.

(* コンパイラの正しさの証明 *)
Theorem comp_correctness: forall (e : exp),
    exec (comp e) [] = [eval e].
Proof.
    intros e.
    induction e as [| e1' IHe1' e2' IHe2'].
                                (* 帰納法の仮定
                                 * IHe1': exec (comp e1') [] = [eval e1']
                                 * IHe2': exec (comp e2') [] = [eval e2']
                                 *)
                                (* 途中式 *)
    - (* e = Val n *)           (* exec (comp (Val n)) [] = [eval (Val n)] *)
      simpl.                    (* [n] = [n] *)
      reflexivity.
    - (* e = Add e1' e2' *)     (* exec (comp (Add e1' e2')) []                  = [eval (Add e1' e2')]  *)
      simpl.                    (* exec (comp e1' ++ comp e2' ++ [ADD]) []       = [eval e1' + eval e2'] *)
      rewrite -> exec_distr.    (* exec (comp e2' ++ [ADD]) (exec (comp e1') []) = [eval e1' + eval e2'] *)
      rewrite -> IHe1'.         (* exec (comp e2' ++ [ADD]) [eval e1']           = [eval e1' + eval e2'] *)
      rewrite -> exec_distr.    (* exec [ADD] (exec (comp e2') [eval e1'])       = [eval e1' + eval e2'] *)
      (* 適用できない！
      rewrite -> IHe2'.
       *)
Abort.

(* 一般化したコンパイラの正しさの証明 *)
Theorem comp_correctness_general: forall (e : exp) (s : stack),
    exec (comp e) s = (eval e)::s.
Proof.
    intros e.
    induction e as [| e1' IHe1' e2' IHe2'].
                                (* 帰納法の仮定
                                 * IHe1': forall s : stack, exec (comp e1') s = eval e1' :: s
                                 * IHe2': forall s : stack, exec (comp e2') s = eval e2' :: s
                                 *)
    - (* e = Val n *)
      intros s.                 (* 途中式 *)
      simpl.                    (* exec (comp (Val n)) s = eval (Val n) :: s *)
      reflexivity.              (* n :: s = n :: s *)
    - (* e = Add e1' e2' *)
      intros s.
      simpl.                    (* exec (comp (Add e1' e2')) s                  = eval (Add e1' e2') :: s  *)
      rewrite -> exec_distr.    (* exec (comp e1' ++ comp e2' ++ [ADD]) s       = eval e1' + eval e2' :: s *)
      rewrite -> IHe1'.         (* exec (comp e2' ++ [ADD]) (exec (comp e1') s) = eval e1' + eval e2' :: s *)
      rewrite -> exec_distr.    (* exec (comp e2' ++ [ADD]) (eval e1' :: s)     = eval e1' + eval e2' :: s *)
      rewrite -> IHe2'.         (* exec [ADD] (exec (comp e2') (eval e1' :: s)) = eval e1' + eval e2' :: s *)
      simpl.                    (* exec [ADD] (eval e2' :: eval e1' :: s)       = eval e1' + eval e2' :: s *)
      reflexivity.              (* eval e1' + eval e2' :: s                     = eval e1' + eval e2' :: s *)
Qed.
