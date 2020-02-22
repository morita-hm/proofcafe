From mathcomp Require Import all_ssreflect.

(*
 * [概略]
 * 直観主義論理でリフレクション補題の成立を証明または公理にして
 * 二重否定除去(背理法の考え方)を使う試みについて
 *
 * 日本語でも「 P でないことはない」という言い方を
 * 「P である」より弱い意味で使うことがありますよね?
 *)

(* P -> ~ ~ P は直観主義論理でも証明できますが ~ ~ P -> P は証明できません. *)

(*
 * P -> ~ ~ P の証明の例
 * Vanilla Coq の証明は以下を参照するとよいでしょう:
 * https://www.iij-ii.co.jp/activities/programming-coq/coqt2.html
 *)
Goal forall (P : Prop),  P -> ~ ~ P.
Proof.
  move=> P H H0.
  by apply/H0.
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
  move=> b.
  case b.
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
  move=> P b Hr.
  case Hr.
  - move=> Hp.
    left.
    done.
  - move=> Hnp.
    right.
    done.
Qed.

(*
 * 排中律 -> 二重否定除去
 * 今度は exfalso のゴリ押しで証明できました ...
 *)
Lemma ssr_nnpp_p : forall (P : Prop) (b : bool), reflect P b -> ~ ~ P -> P.
Proof.
  move=> P b Hr.
  have : P \/ ~ P . (* 排中律の主張をつけたし *)
  - by apply/ssr_em_p/Hr.
  - case=> Hp. (* 排中律の主張で場合分け *)
    + case Hr.
      * done.
      * move=> Hnp.
        exfalso.
        apply/Hnp.
        done.
    + case Hr.
      * move=> Hp'.
        exfalso.
        apply/Hp.
        done.
      * done.
Qed.
