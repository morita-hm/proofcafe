(**
Coq/SSReflect/MathComp による定理証明

ZArith から Z_eqType, Z_choiseType をつくる
======
2018_04_21 @suharahiromichi
2021_01_30 @suharahiromichi
2021_02_27 proofcafeでの実習箇所を抜粋
 *)

From mathcomp Require Import all_ssreflect. (* eqType 他 *)
Require Import ZArith.                      (* Standard Coq の整数型 *)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Set Print All.

(**
# 可換群の定義

説明： MathComp の型クラスのインスタンスとしての整数型を定義します。
整数型の定義は、Standard Coq の ZArith を使用します。

型インスタンス           型クラス      説明
Z_eqType                 eqType       決定可能な同値関係を持つ（整数）型
Z_choiceType             choiceType   有限選択公理のある（整数）型

CanChoiceMixin を使うことで、この順番で証明します。
このような定義の方法は、MCB の 7.5節でも用いられています。

参考： Mathematical Components (MCB) 7.5 Linking a custom data type to the library *)

(* まだ、== は使えない。 *)
Fail Compute 1%Z == 1%Z.
Fail Compute 1%Z == 0%Z.

Section EqAndChoise.
  (* eqType のインスタンス : Z_eqType *)
  Compute Zeq_bool 0%Z 0%Z.                 (* true *)
  Compute Zeq_bool 0%Z 1%Z.                 (* false *)
  Compute Zeq_bool 1%Z 1%Z.                 (* true *)

  Print Equality.axiom. (* reflection 補題が成り立つこと *)
  Lemma Zeq_boolP : Equality.axiom Zeq_bool.
  Proof.
    move=> x y.
      by apply: (iffP idP); rewrite Zeq_is_eq_bool.
  Qed.

  (* Z_eqType をつくって == を使えるようにする *)
  Definition Z_eqMixin := EqMixin Zeq_boolP.
  Canonical Z_eqType := EqType Z Z_eqMixin.

  Compute 1%Z == 1%Z.
  Compute 1%Z == 0%Z.
  
  (* choiseType のインスタンス : Z_choiseType *)
  Definition Z_pickle (z : Z) : nat :=
    if (0 <=? z)%Z then
      (Z.abs_nat z).*2
    else
      (Z.abs_nat (- z)).*2.+1.
  
  Definition Z_unpickle (n : nat) : Z :=
    if odd n then
      (- (Z.of_nat n.-1./2))%Z
    else
      Z.of_nat n./2.

  Compute Z_pickle 1%Z.                     (* 2 *)
  Compute Z_unpickle 2.                     (* 1%Z *)

  (* Z_pickle と Z_unpickle が逆写像の関係にあること *)
  (* Vanilla Coq の ZArith の補題を多用するため証明に不要な Search も残しています *)
  Lemma Z_pickleK : cancel Z_pickle Z_unpickle.
  Proof.
    rewrite /cancel => x.
    rewrite /Z_unpickle /Z_pickle.
    case H : (0 <=? x)%Z.
    - rewrite odd_double.
      Search _ ( (_ + _.*2)./2 = _).
      rewrite (half_bit_double _ false).
      Search _ Z.abs_nat.
      rewrite Nat2Z.inj_abs_nat.
      Search _ (Z.abs _ = _).
      apply: Z.abs_eq.
      Search _ ((_ <= _)%Z).
      by apply: Zle_bool_imp_le.
    - case H1 : (odd (Z.abs_nat (- x)).*2.+1).
      + Search _ (_.+1.-1).
        rewrite Nat.pred_succ.
        rewrite (half_bit_double _ false).
        Search _ (Z.abs_nat _).
        rewrite Nat2Z.inj_abs_nat.
        Search _ (Z.abs _).
        * rewrite Z.abs_eq.
          Search _ ((- - _)%Z).
            by rewrite Z.opp_involutive.
        * Search _ ((0 <= - _)%Z).
          apply/Z.opp_nonneg_nonpos.
          Search _ ((_ <=? _)%Z = false).
          move/Z.leb_gt in H.
          Search _ ((_ < _)%Z).
            by apply: Z.lt_le_incl.
    - Search _ (odd _).
      rewrite oddS in H1.
      by rewrite odd_double in H1.
  Qed.

  (* Z_choiseType *)
  Definition Z_choiceMixin := CanChoiceMixin Z_pickleK.
  Canonical Z_choiceType := ChoiceType Z Z_choiceMixin.
  
  (* Z_countType *)
  Definition Z_countMixin := CanCountMixin Z_pickleK.
  Canonical Z_countType := CountType Z Z_countMixin.

End EqAndChoise.
