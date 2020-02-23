From mathcomp Require Import all_ssreflect.

(*
 * [概略]
 * 直観主義論理でリフレクション補題の成立を証明または公理にして
 * 二重否定除去(背理法の考え方)を使う試みについて
 *
 * 日本語でも「 P でないことはない」という言い方を
 * 「P である」より弱い意味で使うことがありますよね?
 * P -> ~ ~ P は直観主義論理でも証明できますが ~ ~ P -> P は証明できません. 
 *)

(*
 * P -> ~ ~ P の証明の例
 * Vanilla Coq の証明は以下を参照するとよいでしょう:
 * https://www.iij-ii.co.jp/activities/programming-coq/coqt2.html
 *)
Goal forall (P : Prop),  P -> ~ ~ P.
Proof.
  move=> P H H0.
  apply/H0. (* by apply/H0 と 1 行で書くこともできます *)
  done.
Qed.

(* ~ ~ P -> P は証明できません *)
Goal forall (P : Prop), ~ ~ P -> P.
  move=> P H.
  exfalso.
  apply/H.
  Abort.

(* しかし... 直観主義論理でも bool 代数は計算可能です. *)
Goal forall (b : bool), b = ~~ ~~ b.
Proof.
  case. (* case b *)
  - done.
  - done.
Qed.

(* 
 古典論理を直観主義論理で扱うには
 リフレクション補題の成立があればよいことが次の証明でわかります。
 
 簡潔な証明は以下を参照してください。
 https://qiita.com/suharahiromichi/items/3c01d8a111a190302629
 *)
Lemma ssr_em_p : forall (P : Prop) (b : bool), reflect P b -> P \/ ~ P.
Proof.
  move=> P b.
  case=> Hr.
  - left. (* by left. と 1 行で書くことも可能です *)
    done.
  - right. (* by left. と 1 行で書くことも可能です *)
    done.
Qed.
    

(*
 * 排中律 -> 二重否定除去
 * 今度は exfalso のゴリ押しで証明できました ...
 *)
Lemma ssr_nnpp_p : forall (P : Prop) (b : bool), reflect P b -> ~ ~ P -> P.
Proof.
  move=> P b Hr Hnp.
  apply/Hr.
  have : P \/ ~ P by apply/ssr_em_p/Hr. (* 排中律の主張のつけたし *)
  case=> Hem. (* 排中律の主張で場合分け *)
  - case Hr.
    + done.
    + move=> H.
      exfalso.
      apply/Hnp.
      done.
  - case Hr.
    + move=> H.
      exfalso.
      apply/Hem.
      done.
    + done.  
Qed.


(* 
 * ProofCafe では
 * リフレクション補題を使った基本的な証明テクニックとして
 * (1) Bool型の項目は case で場合分できる
 * (2) H : reflect P b のとき apply/H でゴールの P を b, b を P に相互変換できること
 * を挙げています.
 * この観点から二重否定除去の証明をしてみましょう.
 *)

(* まずは準備運動: reflect P b で P を b に書き換える例です. *)
Lemma refl_notP_negb : forall (P : Prop) (b : bool), reflect P b -> ~ P -> ~~ b.
Proof.
  move=> P b Hr H.
  apply/Hr. (* reflect P b で P を b に書き換える *)
  done.
Qed.

(* Bool.iff_reflect : P <-> b = true -> reflect P b を使って, 
 * reflect (~ P) (~~ b), reflect (~ ~ P) (~~ ~~ b) を言い換えて,
 * reflect P b -> reflect (~ P) (~~ ~~ b) -> reflect (~ ~ P) (~~ ~~ b)
 * を証明していきます.
 *)

(* まずは reflect P b -> reflect (~ P) (~~ ~~ b) から *)
Lemma refl_notP_negb_iff : forall (P : Prop) (b : bool), reflect P b -> reflect (~ P) (~~ b).
Proof.
  move=> P b Hr.
  apply/Bool.iff_reflect.
  split.
  - move=> Hnp.
    apply/Hr.
    done.
  - move=> Hf.
    apply/Hr.
    rewrite Hf.
    done.
Qed.

(* 次に reflect P b -> reflect (~ ~ P) (~~ ~~ b) *)
Lemma refl_double_notP_negb : forall (P : Prop) (b : bool), reflect P b -> reflect (~ ~ P) (~~ ~~ b).
Proof.
  move=> P b Hr.
  apply/(refl_notP_negb_iff (~ P))/Bool.iff_reflect.
  split.
  - move=> Hnp.
    apply/Hr.
    done.
  - move=> Hf.
    apply/Hr.
    rewrite Hf.
    done.
Qed.

(* リフレクション補題を使って Claim ~ ~ P -> P を ~~ ~~ b -> b に言い換えます *)
Lemma refl_nnpp_p : forall (P : Prop) (b : bool), reflect P b -> ~ ~ P -> P.
Proof.
  move=> P b Hr Hnnp. 
  (* 
   * P, ~ ~ P を reflect P b, reflect (~ ~ P) (~~ ~~ b) をつかって
   * それぞれ b , ~~ ~~ b に変換します.
   *)
  have Hrd : reflect (~ ~ P) (~~ ~~ b) by apply/refl_double_notP_negb.
  move/Hrd in Hnnp.
  apply/Hr.
  (* Hnnp を generalize して case で場合分けします. *)
  move: Hnnp.
  case b.
  - done.
  - done.
Qed.

(*
 * また, 排中律や二重否定除去と同値な命題については
 * http://proofcafe.org/sf/Logic_J.html
 * を参照するとよいでしょう.
 *)
