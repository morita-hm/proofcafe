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
| blanche. (* white ball, la balle blanche, 白玉 *)


(** Question 3.2 *)

Print list.
Definition balles := list balle.


(** Question 3.3 *)

Check nil            : balles.
Fail Check rouge      : balles.
Check cons rouge nil  : balles.
Fail Check nil cons rouge nil : balles.
Check cons blanche (cons rouge nil).


(** Question 3.4 *)

Fixpoint compter_les_balles_rouges (s : balles) : nat :=
  match s with
  | nil => 0
  | rouge :: s => (compter_les_balles_rouges s).+1
  | blanche :: s => compter_les_balles_rouges s
  end.

(** Question 3.5, 3.6, 3.7, 3.8
 See https://github.com/suharahiromichi/coq/blob/master/csm/csm_ex_3_no_answer.v
 *)

(** Question 3.9 *)
(** sumn を用いて関数 compter_les_balles_rouges' を以下のように定義しました.
    問 3.4 で定義した 関数 compter_les_balles_rouges の結果と一致すること
    を証明しましょう. 
 *)
Definition compter_les_balles_rouges' (s : balles) :=
  sumn (map (fun m => if m is rouge then 1 else 0) s).

Lemma compter_les_balles_rouges_map : forall (s : balles),
    compter_les_balles_rouges' s = compter_les_balles_rouges s.
Admitted.

(** Question 3.10 *)

(** 以下のヒントを参考に次の証明を完成しましょう *)
Lemma compter_les_balles_rouges_rev : forall (s : balles),
    compter_les_balles_rouges (rev s) = compter_les_balles_rouges s.
Admitted.

(** ヒント *)
Goal forall (s : balles),
    sumn (map (fun m => if m is rouge then 1 else 0) (rev s)) =
    sumn (map (fun m => if m is rouge then 1 else 0) s).
  move=> s.
  by rewrite map_rev sumn_rev.
Qed.

(** Question 3.11 *)

(* 以下を証明しましょう *)
Lemma compter_les_balles_rouges_filter : forall (s : balles),
    compter_les_balles_rouges s = size [seq m <- s | if m is rouge then true else false].
Admitted.

(** Question 3.12 *)

(* 以下を証明しましょう *)
Goal forall (s : balles),
    size [seq m <- s | if m is rouge then true else false] + size [seq m <- s | if m is blanche then true else false] = size s.
Admitted.
(* END *)
