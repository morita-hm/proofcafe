(**
Coq/SSReflect/MathComp による定理証明

本ファイルは下書きであり,
           ProofCafe で解説する資料との互換性がない部分があります。
           ProofCafe での解説は connpass の案内を参照してください。

5. 集合の形式化
======
2018_05_03 @suharahiromichi
2020_10_25 @morita_hm : 積集合関連の演算を追記
2020_11_08 @morita_hm : 部分集合に対する像, 逆像を追記
 *)

From mathcomp Require Import all_ssreflect.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Set Print All.

(* 5.1 集合、部分集合 *)

Definition mySet (M : Type) := M -> Prop.
Definition belong {M : Type} (A : mySet M) (x : M) : Prop := A x.
Notation "x ∈ A" := (belong A x) (at level 11).

(* リフレクション補題の成立を公理として, 排中律を証明する *)
Axiom refl_mySet : forall (M : Type) (A : mySet M) (x : M), reflect (A x) true.
Lemma axiom_mySet : forall (M : Type) (A : mySet M), forall (x : M), x ∈ A \/ ~(x ∈ A).
Proof.
  rewrite /belong=> M A x.
  by case: (refl_mySet A x) => Hr; [left | right].
Qed.  

Definition myEmptySet {M : Type} : mySet M := fun _ => False.
Definition myMotherSet {M : Type} : mySet M := fun _ => True.

(* 5.2 包含関係と統合 *)

Definition mySub {M : Type} := fun (A B : mySet M) => forall (x : M), x ∈ A -> x ∈ B.
(* ブルバキ流の記法 *)
Notation "A ⊂ B" := (mySub A B) (at level 11).

Section 包含関係.
  Variable M : Type.

  Check mySet M : Type.
  Check myEmptySet : mySet M.
  Check myMotherSet : mySet M.

  Lemma Sub_Mother (A : mySet M) : A ⊂ myMotherSet.
  Proof. by []. Qed.

  Lemma Sub_Empty (A : mySet M) : myEmptySet ⊂ A.
  Proof. by []. Qed.

  Lemma rfl_Sub (A : mySet M) : A ⊂ A.
  Proof. by []. Qed.

  Lemma transitive_Sub (A B C : mySet M) : A ⊂ B -> B ⊂ C -> A ⊂ C.
  Proof.
    move=> HAB HBC t HtA.
    apply: HBC.
    apply: HAB.
    apply: HtA.
  Qed.
End 包含関係.

Definition eqmySet {M : Type} := fun (A B : mySet M) => (A ⊂ B) /\ (B ⊂ A).
Axiom axiom_ExteqmySet : forall {M : Type} (A B : mySet M), eqmySet A B -> A = B.

Section 等号.
  Variable Mother : Type.

  Lemma rfl_eqS (A : mySet Mother) : A = A.
  Proof. by []. Qed.

  Lemma sym_eqS (A B : mySet Mother) : A = B -> B = A.
  Proof. move=> HAB. by rewrite HAB. Qed.

End 等号.

(* 5.3 集合上の演算 *)

Definition myComplement {M : Type} (A : mySet M) : mySet M := fun (x : M) => ~(A x).
Notation "A ^c" := (myComplement A) (at level 11).

(* Union : 和集合 *)
Definition myCup {M : Type} (A B : mySet M) : mySet M := fun (x : M) => x ∈ A \/ x ∈ B.
Notation "A ∪ B" := (myCup A B) (at level 11).

(* Intersection 積集合 共通部分 *)
(* @morita_hm 追記 *)
Definition myCap {M : Type} (A B : mySet M) : mySet M := fun (x : M) => x ∈ A /\ x ∈ B.
Notation "A ∩ B" := (myCap A B) (at level 11).

(* 差集合, 相対補集合 *)
Definition myBackSlash {M : Type} (A B : mySet M) : mySet M := fun (x : M) => x ∈ A /\ ~(x ∈ B).
Notation "A \ B" := (myBackSlash A B) (at level 11).

(* 部分集合族 *)
Definition power {M : Type} (X : mySet M) : mySet (mySet M) :=
  fun (V : mySet M) => V ⊂ X.

Section 演算.
  Variable M : Type.

  Lemma cEmpty_Mother : (@myEmptySet M)^c = myMotherSet.
  Proof.
    apply: axiom_ExteqmySet.
    by apply: conj; rewrite /myComplement => x HxM.
  Qed.

  (* 母集合 U, 空集合 phi を使った言い換え *)
  Definition U := @myMotherSet M.
  Definition phi := @myEmptySet M.
  
  Lemma cphi_U : phi^c = U.
  Proof.
    rewrite /phi /U.
      by apply: cEmpty_Mother.
  Qed.
  
  Lemma cc_cancel (A : mySet M) : (A^c)^c = A.
  Proof.
    apply: axiom_ExteqmySet.
    rewrite /eqmySet.
    by apply: conj; rewrite /myComplement => x H;
       case: (axiom_mySet A x) => HxA.

    Restart.
    
    apply: axiom_ExteqmySet.
    rewrite /eqmySet.
    rewrite /myComplement.
    apply: conj => x H.
    (* rewrite /mySub 代わりに => x している。 *)
    
    Check (axiom_mySet A x) : x ∈ A \/ ~(x ∈ A).
    
    - case: (axiom_mySet A x) => HxA.
      (* HxA : x∈A の 場合 *)
      + done.
      (* HxA : ~x∈A の 場合 *)
      + Check H HxA : False.
        move/H in HxA.                      (* HxA : False で矛盾 *)
        done.
        
    - case: (axiom_mySet A x) => HxA.
      (* HxA : x∈A の 場合 *)
      + move=> Hnot_xA.                     (* 二重否定を除去する。 *)
        apply Hnot_xA.
        apply HxA.
      (* HxA : ~x∈A の 場合 *)
      + done.                               (* x∈A かつ ~x ∈ A  で矛盾 *)
  Qed.

  Lemma cMotehr_Empty : (@myMotherSet M)^c = myEmptySet.
  Proof.
      by rewrite -cEmpty_Mother cc_cancel.
  Qed.
    
  Lemma myCupA (A B C : mySet M) : (A ∪ B) ∪ C = A ∪ (B ∪ C).
  Proof.
    apply: axiom_ExteqmySet.
    rewrite /eqmySet.
    split => x [H | H].
    - case: H => H.
      + by left.
      + by right; left.
    - by right; right.
    - by left; left.
    - case: H => H.
      + by left; right.
      + by right.
  Qed.

  (* 和集合(union) の交換法則 *)
  (* @morita_hm 追記 *)
  Lemma myCupC (A B : mySet M) : A ∪ B = B ∪ A.
  Proof.
    apply: axiom_ExteqmySet.
    rewrite /eqmySet /mySub /myCup /belong.
    apply: conj => x H.
    - case H => t.
      + by apply: or_intror.
      + by apply: or_introl.
    - case H => t.
      + by apply: or_intror.
      + by apply: or_introl.
  Qed.

  
  Lemma myUnionCompMother (A : mySet M) : A ∪ (A^c) = myMotherSet.
  Proof.
    apply: axiom_ExteqmySet.
    rewrite /eqmySet.
    split => [| x H].
    - done.
    - case: (axiom_mySet A x) => H';
        by [left | right].
  Qed.

  
  (* @morita_hm : intersection の結合法則 *)
  Lemma myCapA (A B C : mySet M) : (A ∩ B) ∩ C = A ∩ (B ∩ C).
  Proof.
    apply: axiom_ExteqmySet.
    rewrite /eqmySet /mySub /myCap /belong.
    apply: conj => x H.
    - case H => Hab Hc.
      + case Hab => Hax Hbx.
        split.
        * done.
        * by split.
    - case H => Ha Hbc.
      case Hbc => Hbx Hcx.
        by split.
  Qed.

  (* @morita_hm : intersection の交換法則 *)
  Lemma myCapC (A B : mySet M) : A ∩ B = B ∩ A.
  Proof.
    apply: axiom_ExteqmySet.
    rewrite /eqmySet /mySub /myCap /belong.
    apply: conj => x Hab.
    - case Hab => Hax Hbx.
        by split.
    - case Hab => Hbx Hax.
        by split.
  Qed.  
  
  (* @morita_hm : 積集合は部分集合 *)
  Lemma intersection_self (A B : mySet M) : A ∩ B ⊂ A.
  Proof.
    rewrite /mySub /myCap /belong => x Hab.
    by case Hab => Hax Hbx.
  Qed.

  (* @morita_hm : 積集合が元の集合の部分集合 *)
  Lemma intersection_sub (A B : mySet M) : A ∩ B ⊂ A /\ A ∩ B ⊂ B.
  Proof.
    split.
    - by apply: intersection_self.
    - rewrite myCapC.
      by apply: intersection_self.
  Qed.

  (* de Morgan *)
  Lemma deMorgan (A B : mySet M) :  (A^c) ∩ (B^c) = (A ∪ B)^c.
  Proof.
    apply: axiom_ExteqmySet.
    rewrite /eqmySet /myComplement /myCap /myCup /belong.
    apply: conj=> x.
      rewrite /belong => H.
      case H => Hna Hnb Hnab.
        apply: Hna.
        by case: Hnab.
    - rewrite /belong => H.
      split => Hn.
      + apply: H.
          by left.
      + apply: H.
          by right.
  Qed.

  Lemma deMorgan2 (A B : mySet M) :  (A^c) ∪ (B^c) = (A ∩ B)^c.
  Proof.
    apply: axiom_ExteqmySet.
    rewrite /eqmySet.
    rewrite /myCup /myCap /myComplement /belong /mySub.
    split=> x.
    - rewrite /belong.
      case=> H H'.
      + apply: H.
          by case: H'.
      + apply: H.
          by case: H'.
    - case: (axiom_mySet A x).
      + rewrite /belong => Hin Hnab.
        right => Hb.
        apply: Hnab.
        by split.
      + rewrite /belong => Hout Hnab.
          by left.
  Qed.          

  
  (* @morita_hm : 差集合 = 相対補集合 *)
  Lemma relative_complemant (A B : mySet M) : A \ B = A ∩ (B^c).
  Proof.
    apply: axiom_ExteqmySet.
    rewrite /eqmySet /myCap /myBackSlash /myComplement /mySub /belong.
    apply: conj => x H.
    - case: H => Hax Hnbx.
        by apply: conj.
    - case: H => Hax Hnbx.
        by apply: conj.
  Qed.

  (* @morita_hm : 部分集合族を使った包含関係の言い換え *)
  Lemma power_trivial (V X : mySet M) : V ⊂ X -> V ∈ power X.
  Proof.
    move=> Hvx.
      by rewrite /belong /power.
  Qed.

  Lemma power_intersection (V W X : mySet M) :
    V ∈ power X -> W ∈ power X -> V ∩ W ∈ power X.
  Proof.
    rewrite /belong /power.
    have Hvw : V ∩ W ⊂ V by apply: intersection_self.
    move=> Hv Hw.
    move: Hvw Hv.
    by apply: transitive_Sub.
  Qed.

  Lemma power_relative_complement (V W X : mySet M) :
    V ∈ power X -> W ∈ power X -> V \ W ∈ power X.
  Proof.
    rewrite /belong /power.
    have Hvw : V \ W ⊂ V by apply: intersection_self.
    move=> Hv Hw.
    move: Hvw Hv.
    by apply: transitive_Sub.
  Qed.
  
End 演算.

(* 5.4 集合間の写像 *)

Definition myMap {M1 M2 : Type} (A : mySet M1) (B : mySet M2) (f : M1 -> M2) :=
  forall (x : M1), x ∈ A -> f x ∈ B.
Notation "f ∈Map A \to B" := (myMap A B f) (at level 11).

Definition MapCompo {M1 M2 M3 : Type} (f : M2 -> M3) (g : M1 -> M2) : M1 -> M3 :=
  fun (x : M1) => f (g x).
Notation "f ● g" := (MapCompo f g) (at level 11).

(* 像 : image *)
Definition ImgOf {M1 M2 : Type} (f : M1 -> M2) {A : mySet M1} {B : mySet M2}
           (_ : f ∈Map A \to B) : mySet M2 :=
  fun (y : M2) => exists (x : M1), y = f x /\ x ∈ A.

(* @morita_hm : 部分集合を用いた像の定義 *)
Definition ImgOfSub {M1 M2 : Type} (f : M1 -> M2) {X : mySet M1} {Y : mySet M2} (_ : f ∈Map X \to Y) (A : mySet M1) : mySet M2 :=
  fun (y : M2) => exists (x : M1), A ⊂ X -> x ∈ A -> y = f x.

(* 逆像 : f^{-1}(B) *)
Definition InvImgOfSub {M1 M2 : Type} (f : M1 -> M2) {X : mySet M1} {Y : mySet M2} (_ : f ∈Map X \to Y) (B : mySet M2) : mySet M1 :=
  fun (x : M1) => exists (y : M2), B ⊂ Y -> y ∈ B -> y = f x. 

(* 単射 : injection *)
Definition mySetInj {M1 M2 : Type} (f : M1 -> M2) {A : mySet M1} {B : mySet M2}
           (_ : f ∈Map A \to B) : Prop :=
  forall (x y : M1), x ∈ A -> y ∈ A -> f x = f y -> x = y.

(* 全射 : surjection *)
Definition mySetSur {M1 M2 : Type} (f : M1 -> M2) {A : mySet M1} {B : mySet M2}
           (_ : f ∈Map A \to B) : Prop :=
  forall (y : M2), y ∈ B -> exists (x : M1), x ∈ A -> f x = y.

(* 全単射 : bijection *)
Definition mySetBi {M1 M2 : Type} (f : M1 -> M2) {A : mySet M1} {B : mySet M2}
           (fAB : f ∈Map A \to B) : Prop :=
  mySetInj fAB /\ mySetSur fAB.


Section 写像.
  Variable M1 M2 M3 : Type.
  Variable f : M2 -> M3.
  Variable g : M1 -> M2.
  Variables A A' : mySet M1.
  Variable B B' : mySet M2.
  Variable C : mySet M3.
  Hypothesis gAB : g ∈Map A \to B.
  Hypothesis fBC : f ∈Map B \to C.
  
  Lemma transitive_Inj (fgAC : (f ● g) ∈Map A \to C) :
    mySetInj fBC -> mySetInj gAB -> mySetInj fgAC.
  Proof.
    rewrite /mySetInj => Hinjf Hinjg x y HxA HyA H.
    Check Hinjg x y HxA HyA.
    Check Hinjf (g x) (g y) (gAB HxA) (gAB HyA).
    apply: Hinjg.
    - done.
    - done.
      apply: Hinjf.
      + by apply gAB.
      + by apply gAB.
      + by apply H.
  Qed.
  
  Lemma CompoTrans : (f ● g) ∈Map A \to C.
  Proof.
    move: gAB fBC.
    rewrite /MapCompo /myMap => Hab Hbc t Ha.
    apply: Hbc.
    apply: Hab.
    apply: Ha.
  Qed.

  Lemma ImSub : (ImgOf gAB) ⊂ B.
  Proof.
    rewrite /ImgOf => t.
    case=> x.
    case=> H1 H2.
    rewrite H1.
      by apply: gAB.
  Qed.

  (* 集合 X, Y と写像 h : X → Y および部分集合 V ⊂ X (V ∈ power X) に対して、
     h (X \ V) ⊂ h(X) \ h(V)
     であることの形式化 *)
  Variable h : M1 -> M2.
  Variable X : mySet M1.
  Variable Y : mySet M2.
  Variable V : mySet M1.
  Variable W1 W2 : mySet M2.
  Hypothesis hXY : h∈Map X \to Y.

  Lemma ImgOfSubIncl :
    V ⊂ X -> (ImgOfSub hXY X \ ImgOfSub hXY V) ⊂ ImgOfSub hXY (X \ V).
  Proof.
  Admitted.

  Lemma InvImgOfSubIncl :
    W1 ⊂ Y -> W2 ⊂ Y -> W1 ⊂ W2 -> InvImgOfSub hXY W1 ⊂ InvImgOfSub hXY W2.
  Proof.
    Admitted.
  
End 写像.

(*
   同値関係の準備 : 2項関係, 反射律, 対称律, 推移律 を定義する
*)
Definition myRel (M : Type) := M -> M -> Prop.

(* 反射律 *)
Definition myRefl {M : Type} (r : myRel M) :=
  forall (x : M), r x x.
(* 対照律 *)
Definition mySym {M : Type} (r : myRel M) :=
  forall (x y : M), r x y -> r y x.
(* 推移律 *)
Definition myTrans {M : Type} (r : myRel M) :=
  forall (x y z : M), r x y -> r y z -> r x z.


(* 5.5 fintype を用いた有限集合の形式化 *)

Definition p2S {M : finType} (pA : pred M) : mySet M :=
  fun (x : M) => if x \in pA then True else False.
Notation "\{ x 'in' pA \}" := (p2S pA).     (* x は飾り。 *)

Section fintypeを用いた有限集合.
  (* Set Printing Coercions. *)
  
  Variable M : finType.
  
  (* myMotherSet =
     p2S (pred_of_simpl (pred_of_argType (Equality.sort (Finite.eqType M)))) *)
  Check p2S M : mySet M.
  Check p2S (mem M).
  Check p2S (pred_of_simpl (pred_of_argType (Equality.sort (Finite.eqType M)))).
  
  Lemma Mother_predT : myMotherSet = \{ x in M \}.
  Proof. by []. Qed.
  
  Lemma myFinBelongP (x : M) (pA : pred M) : reflect (x ∈ \{x in pA \}) (x \in pA).
  Proof.
    rewrite /belong /p2S.
    apply/(iffP idP) => H1.
    - Check (_ : (x \in pA) = true).
        by rewrite (_ : (x \in pA) = true).
    - have testH : (x \in pA) || ~~(x \in pA).
      + set t := x \in pA.
          by case: t.
      + move: testH.
        case/orP => [| Harg]; first by [].
        Check (_ : (x \in pA) = false).
        rewrite (_ : (x \in pA) = false) in H1; first by [].
        by apply: negbTE.
  Qed.
  
  (* suhara *)
  Lemma myFinBelongP' (x : M) (pA : pred M) : reflect (x ∈ \{x in pA \}) (x \in pA).
  Proof.
    rewrite /belong /p2S.
    apply/(iffP idP) => H1.
    - by rewrite H1.
    - by case H : (x \in pA); last rewrite H in H1.
  Qed.
  
  Lemma myFinBelongP'' (x : M) (pA : pred M) : reflect (x ∈ \{x in pA \}) (x \in pA).
  Proof.
    rewrite /belong /p2S.
    apply/(iffP idP) => H1.
    - by rewrite H1.
    - case: ifP (H1) => H2.
      + done.
      + by rewrite H2 in H1.
  Qed.
  
  Lemma myFinSubsetP (pA pB : pred M) :
    reflect (\{ x in pA \} ⊂ \{ x in pB \}) (pA \subset pB).
  Proof.
    rewrite /mySub.
    apply/(iffP idP) => H.
    - move=> x /myFinBelongP => H2.
      apply/myFinBelongP.
      move: H => /subsetP.
      rewrite /sub_mem.
      by apply.
    - apply/subsetP.
      rewrite /sub_mem => x /myFinBelongP => HpA.
      apply/myFinBelongP.
      by apply H.
  Qed.
  
  (* fintype の補題 *)
  Check predT_subset : forall (T : finType) (A : pred T),
      T \subset A -> forall x : T, x \in A.
  
  Lemma Mother_Sub (pA : pred M) :
    myMotherSet ⊂ \{ x in pA \} -> forall x, x ∈ \{ x in pA \}.
  Proof.
    rewrite Mother_predT => /myFinSubsetP => H x.
    apply/myFinBelongP.
    by apply: predT_subset.
  Qed.

  (* fintype の補題 *)
  Check subset_trans : forall (T : finType) (A B C : pred T),
      A \subset B -> B \subset C -> A \subset C.

  Lemma transitive_Sub' (pA pB pC : pred M) :
    \{ x in pA \} ⊂ \{ x in pB \} ->
    \{ x in pB \} ⊂ \{ x in pC \} ->
    \{ x in pA \} ⊂ \{ x in pC \}.
  Proof.
    move/myFinSubsetP => HAB /myFinSubsetP HBC.
      by apply/myFinSubsetP/(subset_trans HAB HBC).
  Qed.

  Lemma transitive_Sub'' (pA pB pC : pred M) :
    \{ x in pA \} ⊂ \{ x in pB \} ->
    \{ x in pB \} ⊂ \{ x in pC \} ->
    \{ x in pA \} ⊂ \{ x in pC \}.
  Proof.
    by apply: transitive_Sub.
  Qed.
End fintypeを用いた有限集合.  

Section ライブラリfinsetの利用.
  Variable M : finType.

  Lemma demorgan (A B C : {set M}) : (A :&: B) :|: C = (A :|: C) :&: (B :|: C).
  Proof.
    apply/setP => x.
    rewrite !inE.                          (* || と && に変換する。 *)
    Check orb_andl.
    by rewrite -orb_andl.         (* || と && の ド・モルガンの定理 *)
  Qed.
End ライブラリfinsetの利用.

(* ************************************* *)
(* ************************************* *)
(* ************************************* *)

Section 具体的なfinType.                    (* suhara *)
  (* 具体的な finType として、'I_5 を与える。 *)
  
  (* 'I_5 の要素として、p0 を定義する。 *)
  Definition p0 := @Ordinal 5 0 is_true_true.
  Check p0 : 'I_5 : Type.
  
  Check Finite.sort (ordinal_finType 5) : Type.
  Check              ordinal_finType 5  : finType.
  Check              ordinal_finType 5  : Type.      (* コアーション *)
  Check p0 : Finite.sort (ordinal_finType 5) : Type.
  Check p0 :              ordinal_finType 5  : Type. (* コアーション *)
  (** コアーションによって、(ordinal_finType 5) は型として見える。
      つまり、(ordinal_finType 5) は finType型クラスから作られた、型インスタンスである。 *)
  
  (* 'I_5 を要素とする集合を定義する。 *)
  Check @p2S : forall M : finType, pred M -> mySet M.
  
  (* see also. ssr/ssr_in_operator.v *)
  (* 'I_5 は finType のインスタンスである。(あ) *)
  Goal 'I_5 = ordinal_eqType 5. Proof. done. Qed.
  
  (* (pred_of_simpl (pred_of_argType 'I_5)) は、pred 'I_5 型である。(い) *)
  Check pred_of_simpl (pred_of_argType 'I_5) : pred 'I_5.
  
  (* (あ)(い) より、(pred_of_simpl (pred_of_argType 'I_5)) は、
     T : finType, P : pred T なる P である。 *)
  Check pred_of_argType : forall T : predArgType, simpl_pred T.
  Check pred_of_simpl   : forall T : Type, simpl_pred T -> pred T.
  Check (fun T => pred_of_simpl (pred_of_argType T)) : forall T : predArgType, pred T.
  
  (* (pred_of_simpl (pred_of_argType 'I_5)) は、
     mem の引数に書くことができ、また、mem も省略できる。 *)
  Check p2S (mem (pred_of_simpl (pred_of_argType 'I_5))) : mySet 'I_5. (* (1) *)
  Check p2S (mem                                 'I_5)   : mySet 'I_5. (* (2) *)
  Check p2S      (pred_of_simpl (pred_of_argType 'I_5))  : mySet 'I_5.  
  Check p2S                                      'I_5    : mySet 'I_5.
  Check \{ x in 'I_5 \}                                  : mySet 'I_5.  
  
  (* *************** *)
  (* ここからが本題。 *)
  (* *************** *)
  
  (* p0 は素の集合の要素である。 *)
  Goal p0 ∈ \{ x in 'I_5 \}.
  Proof.
      (*
        rewrite /belong /p2S.
        by case H : (p  1 \in 'I_5).
       *)
      by [].
  Qed.
  
End 具体的なfinType.

(* END *)
