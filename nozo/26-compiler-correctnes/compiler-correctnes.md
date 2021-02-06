# コンパイラの正しさの証明

  プログラミングHaskell第2版の「16.7 コンパイラーの正しさ」という章の証明をcoqで書いてみる。

  https://www.lambdanote.com/products/haskell-ebook?variant=28881684987988

  まずはソース言語とターゲットコードの評価関数の定義をする。

  ソース言語：
  自然数と加算だけの簡単な式からなる言語。

  ```coq
  Inductive exp : Type :=
      | Val (n : nat)
      | Add (e1 : exp) (e2 : exp).

  Fixpoint eval (e : exp) : nat :=
      match e with
      | Val n     => n
      | Add e1 e2 => (eval e1) + (eval e2)
      end.
  ```

  1+2に対応する式と、それを評価した結果は次のようになる。

  ```
  Compute eval (Add (Val 1) (Val 2)).
  (*
       = 3
       : nat
  *)
  ```

  ターゲットコード：
  PUSH/ADD命令からなるスタックマシンのコード。
  `exec`関数は命令列とスタックを受け取り、計算した結果のスタックを返す。

  ```coq
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
                        (* スタックのサイズが2より小さいとき何もしない *)
                        | _          => s
                        end
      end.
  ```

  ちなみに、書籍の実装では以下のようにADD命令についてスタックサイズが2以上であるパターンのみ定義している。coqではパターンは網羅されている必要があるので、スタックサイズが2より小さいときは何もしない実装にしてみた。

  ```haskell
  exec :: Code -> Stack -> Stack
  exec []           s           = s
  exec (PUSH n : c) s           = exec c (n : s)
  exec (ADD : c)    (m : n : s) = exec c (n+m : s)
  ```

  スタックマシンコードとその評価の結果は次のようになる。

  ```
  Compute exec [PUSH 1; PUSH 2; ADD] [].
  (*
       = [3]
       : stack
  *)
  ```

  続いてコンパイラを定義する。
  コンパイラはソース言語`exp`を受け取りターゲットコード`code`を返す関数になる。

  ```coq
  Fixpoint comp (e : exp) : code :=
      match e with
      | Val n     => [PUSH n]
      | Add e1 e2 => (comp e1) ++ (comp e2) ++ [ADD]
      end.

  Compute comp (Add (Val 1) (Val 2)).
  (*
       = [PUSH 1; PUSH 2; ADD]
       : code
  *)
  ```

  このコンパイラの正しさとは何なのかというと次の等式で表すことができる。

  ```
  exec (comp e) [] = [eval e]
  ```

  この等式は「ある式`e`をコンパイルして得られたコードを評価した結果と、式`e`を評価した結果は等しい」ことを表している。
  つまり、コンパイラの正しさとは「ソース言語の仕様(評価関数の定義)を維持したままターゲット言語に変換する性質」のことと言える。

  コンパイラの正しさをcoqで証明する。

  証明は`Expr`についての構造的帰納法を用いて次を証明したらよい。
  1. 基底ケース：
   `e = Val n`に対して`comp_correctness`が成り立つ
  2. 帰納ケース：
   `e1', e2'`に対して`comp_correctness`が成り立つと仮定したとき、`e = Add e1' e2'`に対して`comp_correctness`が成り立つ

  ```coq
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
  ```

  基底ケースは単に`simpl`するだけでよい。
  帰納ケースは次の補題`exec_distr`を定義して使う。（証明は後でする）

  ```coq
  Lemma exec_distr: forall (c1 c2 : code) (s : stack),
      exec (c1 ++ c2) s = exec c2 (exec c1 s).
  Proof. Admitted.
  ```

  この補題は、「`c1`と`c2`を連結してから実行した結果と、`c1`を先に実行した後で`c2`を実行した結果は同じ」であることを表す。

  この補題から、帰納ケースのひとつめの`rewrite -> exec_distr`によって`exec (comp e1' ++ comp e2' ++ [ADD]) []`という式を`exec (comp e2' ++ [ADD]) (exec (comp e1') [])`に置き換えている。

  そして、この式に現れる`exec (comp e1') []`という部分式に対して、帰納法の仮定`IHe1' : exec (comp e1') [] = [eval e1']`から`rewrite -> IHe1'.`によって`[eval e1']`に置き換えることができた。

  ここからさらに`rewrite -> exec_distr`を適用することによって`exec (comp e2') [eval e1']`という部分式が得られるのだが、この式はスタックが空`[]`ではないので帰納法の仮定`IHe2': exec (comp e2') [] = [eval e2']`を適用することができず、証明がうまく進まなくなってしまう。

  証明をうまく進めるために、`exec`のスタックを空ではなく任意のスタックにして定理を一般化する。

  ```coq
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
  ```

  これにより、帰納法の仮定が`IHe2': forall s : stack, exec (comp e2') s = eval e2' :: s`という形になり`exec (comp e2') (eval e1' :: s)`に対して`rewrite -> IHe2'.`を適用できるようになり`eval e2' :: eval e1' :: s`に書き換えることができる。

  あとは`simpl`して帰納ケースの証明が完了し、コンパイラの正しさが証明できた。
  と言いたいところだけど途中で定義した補題の証明がまだ残っている。

# 参考
- プログラミングHaskell 第2版, Graham Hutton (著), 山本 和彦 (訳), オーム社
