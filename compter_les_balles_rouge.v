(**

Coq/SSReflect/MathComp による定理証明
第3章 演習問題(3.1-3.4)と追加の問題(3.9, 3.10)

======

2019_10_1 @morita_hm
 *)

From mathcomp Require Import all_ssreflect.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** Question 3.1  *)

Inductive balle :=
| rouge  (* red ball, la balle rouge, 紅玉 *)
| blanc. (* white ball, la balle blanc, 白玉 *)


(** Question 3.2 *)

Print list.
Definition balles := list balle.


(** Question 3.3 *)

Check nil            : balles.
Fail Check rouge      : balles.
Check cons rouge nil  : balles.
Fail Check nil cons rouge nil : balles.
Check cons blanc (cons rouge nil).


(** Question 3.4 *)

Fixpoint compter_les_balles_rouge (s : balles) : nat :=
  match s with
  | nil => 0
  | rouge :: s => (compter_les_balles_rouge s).+1
  | blanc :: s => compter_les_balles_rouge s
  end.

(** Question 3.5 追加の問題 *)
(** 与えられた玉の列に対する赤玉の数を示す述語 num_of_red を Inductive により定義せよ。 *)

(** Question 3.6 追加の問題 *)
(** 命題 num_of_red (cons 白玉 (cons 赤玉 nil)) 1 が真であることを示せ。 *)

(** Question 3.7 追加の問題 *)
(** 命題 num_of_red (cons 白玉 (cons 赤玉 nil)) 0 が偽（否定が真）であることを示せ。 *)

(** Question 3.8 追加の問題 *)
(** 問 3.4 で定義した 関数 赤数え の結果と、問 3.5 で定義した 述語
    num_of_red の命題が必要十分条件であることを定理として示せ。
    このとき、num_of_red の定義を見直してもよい。 *)

(** Question 3.9 *)
(** sumn を用いて 関数 赤数え'(compter_les_balles_rouge') を定義し, 
    問 3.4 で定義した 関数 赤数え(compter_les_balles_rouge) の結果と一致することを証明しましょう.
 *)
Definition compter_les_balles_rouge' (s : balles) :=
  sumn (map (fun m => if m is rouge then 1 else 0) s).

Lemma compter_les_balles : forall (s : balles),
    compter_les_balles_rouge' s = compter_les_balles_rouge s.
Admitted.

(** Question 3.10 *)

(** 以下のヒントを参考に次の証明を完成しましょう *)
Goal forall (s : balles),
    compter_les_balles_rouge (rev s) = compter_les_balles_rouge s.
Admitted.

(** ヒント *)
Goal forall (s : balles),
    sumn (map (fun m => if m is rouge then 1 else 0) (rev s)) =
    sumn (map (fun m => if m is rouge then 1 else 0) s).
  move=> s.
  by rewrite map_rev sumn_rev.
Qed.

(* END *)
