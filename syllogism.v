
From mathcomp Require Import all_ssreflect.

(* move/ の使用例 *)

(* move *)
Goal forall (P Q R : Prop),
    (P -> Q) -> (Q -> R) -> (P -> R).
Proof.
  move=> P Q R V1 V2.
  move/V1/V2.
  done.
Qed.

(* move *)
Goal forall (P Q R : Prop),
    (P -> Q) -> (Q -> R) -> (P -> R).
Proof.
  move=> P Q R V1 V2.
  move/V1/V2.
  done.
Qed.

Goal forall (P Q R : Prop),
    (P -> Q) -> (Q -> R) -> (P -> R).
Proof.
  move=> P Q R V1 V2 HP.
  move: (V1 HP).
  done.
Qed.

Goal forall (P Q R : Prop),
    (P -> Q) -> (Q -> R) -> (P -> R).
Proof.
  move=> P Q R V1 V2 HP.
  move/V1/V2 in HP.
  done.
Qed.

(* vanilla Coq *)
Goal forall (P Q R : Prop),
    (P -> Q) -> (Q -> R) -> (P -> R).
Proof.
  intros P Q R V1 V2 HP.
  apply V1,V2 in HP.
  exact HP.
Qed.