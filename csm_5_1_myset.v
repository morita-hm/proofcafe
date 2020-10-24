(* 集合の形式化
   元である
   包含関係
   集合の等しい
   和集合, 積集合, 補集合, 差集合
   写像
*)

From mathcomp Require Import all_ssreflect.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

(* 母集合 M の集合 *)
Definition mySet (M : Type) := M -> Prop.

(* x は 集合 A の元である *)
Definition belong {M : Type} (A : mySet M) (x : M) : Prop := A x.
Notation "x ∈ A" := (belong A x) (at level 11).

Axiom axiom_mySet : forall (M : Type) (A : mySet M),
    forall (x : M), (x ∈ A) \/ ~(x ∈ A).

Definition myEmptySet {M : Type} : mySet M := fun _ => False.
Definition myMotherSet {M : Type} : mySet M := fun _ => True.
  
Definition mySub {M : Type} :=
  fun (A B : mySet M) => (forall (x : M), (x ∈ A) -> (x ∈ B)). 

(* ブルバキ流の包含関係 *)
Notation "A ⊂ B" := (mySub A B) (at level 11).
(* 高校の教科書では　A ⊆ B に相当します *)


Section SubsetRelation.
  
  Variable M : Type.
  Lemma Sub_Mother (A : mySet M) : A ⊂ myMotherSet.
  Proof. done. Qed.

  Lemma Sub_Empty (A : mySet M) : myEmptySet ⊂ A.
  Proof. done. Qed.

  Lemma rfl_Sub (A : mySet M) : (A ⊂ A).
  Proof. done. Qed.

  Lemma transitive_Sub (A B C : mySet M) :
    (A ⊂ B) -> (B ⊂ C) -> (A ⊂ C).
  Proof.
    move=> H1 H2 t H3.
    by apply/H2/H1.
  Qed.    

End SubsetRelation.

Definition eqmySet {M : Type} :=
  fun (A B : mySet M) => (A ⊂ B /\ B ⊂ A).

Goal forall {M: Type} (A B : mySet M),
    A = B -> eqmySet A B.
Proof.
  move=> M A B H.
  rewrite H /eqmySet.
  split; by apply: rfl_Sub.
Qed.  

Axiom axiom_ExteqmySet : forall {M : Type} (A B : mySet M),
    eqmySet A B -> A = B.

Section EqsetRelation.
  Variable M : Type.

  Lemma rfl_eqS (A : mySet M) : A = A.
  Proof.
    done.
  Qed.

  Lemma sym_eqS (A B : mySet M) : A = B -> B = A.
  Proof.
    done.
  Qed.

End EqsetRelation.

(* 補集合 *)
Definition myComplement {M : Type} (A : mySet M) : mySet M :=
  fun (x : M) => ~(x ∈ A).
Notation "A ^c" := (myComplement A) (at level 11).

(* Union 和集合 交わり *)
Definition myCup {M : Type} (A B : mySet M) : mySet M :=
  fun (x : M) => (x ∈ A) \/ (x ∈ B).
Notation "A ∪ B" := (myCup A B) (at level 11).

(* Intersection 積集合 共通部分 *)
Definition myCap {M : Type} (A B : mySet M) : mySet M :=
  fun (x : M) => (x ∈ A) /\ (x ∈ B).
Notation "A ∩ B" := (myCap A B) (at level 11).

Definition myRelativeComplement {M : Type} (A B : mySet M) : mySet M :=
  fun (x : M) => (x ∈ A) /\ ~(x ∈ B).
Notation "A \ B" := (myRelativeComplement A B) (at level 11).

Section SetOperation.
  Variable M : Type.

  Lemma cDualEmptyMother : (@myEmptySet M)^c = myMotherSet.
  Proof.
    apply: axiom_ExteqmySet; rewrite /eqmySet.
    apply conj; rewrite /mySub /myComplement /belong /myEmptySet /myMotherSet.
    - done.
    - move=> Hm Ht Hnf.
      done.
  Qed.

  Lemma cDoubleDual (A : mySet M) : (A^c)^c = A.
  Proof.
    apply: axiom_ExteqmySet.
    rewrite /eqmySet.
    apply conj; rewrite /mySub /myComplement /belong => x H1.
    - case (axiom_mySet A x).
      + done.
      + move=> H2.
        done.
    - move=> Hn.
      done.
  Qed.
      
  (* union の結合法則 *)
  Lemma myCupA (A B C : mySet M) : (A ∪ B) ∪ C = A ∪ (B ∪ C).
  Proof.
    apply: axiom_ExteqmySet.
    rewrite /eqmySet /mySub.
    apply: conj => x [H1 | H2].
    - case: H1 => t.
      + by apply/or_introl.
      + by apply/or_intror/or_introl.
    - by apply/or_intror/or_intror.
    - by apply/or_introl/or_introl.
    - case: H2 => t.
      + by apply/or_introl/or_intror.
      + by apply/or_intror.
  Qed.

  (* union の交換法則 *)
  Lemma myCupC (A B : mySet M) : A ∪ B = B ∪ A.
  Proof.
    apply: axiom_ExteqmySet.
    rewrite /eqmySet /mySub /myCup /belong.
    apply: conj.
    - move=> x H1.
      case H1 => t.
      + by apply or_intror.
      + by apply or_introl.
    - move=> x H2.
      case H2 => t.
      + by apply or_intror.
      + by apply or_introl.
  Qed.

  (* intersection の結合法則 *)
  Lemma myCapA (A B C : mySet M) : (A ∩ B) ∩ C = A ∩ (B ∩ C).
  Proof.
    apply: axiom_ExteqmySet.
    rewrite /eqmySet /mySub /myCap /belong.
    apply: conj.
    - move=> x H.
      case H => Hab Hc.
      inversion Hab.
      split.
      done.
      split.
      done.
      done.
    - move=> x H.
      case H => Ha Hbc.
      inversion Hbc.
      split.
      split.
      done.
      done.
      done.
  Qed.

  (* intersection の交換法則 *)
  Lemma myCapC (A B : mySet M) : A ∩ B = B ∩ A.
  Proof.
    apply: axiom_ExteqmySet.
    rewrite /eqmySet /mySub /myCap /belong.
    apply: conj.
    - move=> x Hab.
      inversion Hab.
      split.
      + done.
      + done.
    - move=> x Hba.
      inversion Hba.
      split.
      + done.
      + done.
  Qed.

  Lemma intersection_self (A B : mySet M) : A ∩ B ⊂ A.
  Proof.
    rewrite /mySub /myCap /belong.
    move=> x HAB.
    inversion HAB.
    done.
  Qed.

  Lemma intersection_sub (A B : mySet M) : A ∩ B ⊂ A /\ A ∩ B ⊂ B.
  Proof.
    split.
    - by apply: intersection_self.
    - rewrite myCapC.
      by apply: intersection_self.
  Qed.
  
(*
  Lemma deMorgan (A B : mySet M) : (A ∩ B)^c = A^c ∪ B^c.
  Proof.
 *)  
    
End SetOperation.
