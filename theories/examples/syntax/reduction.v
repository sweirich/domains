From Stdlib Require Import Relations List Program
     ssreflect ssrfun ssrbool.
From Stdlib Require Import Classes.RelationClasses 
  Classes.Morphisms Lia Arith.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Require Import smpl.Smpl.
Require Import utils.all.

Require Import syntax.syntax.
Require Import syntax.typing.
Require Import syntax.relations.

Import SyntaxNotations.
Import SubstNotations.
Import typing.Notations.

Open Scope syntax_scope.

(** * single-step head reduction *)
Inductive HeadRed1 (n : nat) : Tm n -> Tm n -> Prop := 
 | hr_beta A M N :
    HeadRed1 (app (abs A M) N) M[N..]
 | hr_app  M1 M2 N :
    HeadRed1 M1 M2 -> 
    HeadRed1 (app M1 N) (app M2 N)
 | hr_zero M0 M1 :
    HeadRed1 (ncase zero M0 M1) M0
 | hr_succ M0 M1 N :
    HeadRed1 (ncase (succ N) M0 M1) (M1[N..])
 | hr_case M M' M0 M1 :
    HeadRed1 M M' ->
    HeadRed1 (ncase M M0 M1) (ncase M' M0 M1)
.

(* reflexive-transitive closure *)
Definition HeadRed (n : nat) : Tm n -> Tm n -> Prop := 
  multi (@HeadRed1 n).

Lemma HeadRed_app {n:nat} (M1 M2 : Tm n) N :
   HeadRed M1 M2 -> HeadRed (app M1 N) (app M2 N).
Proof.
  intro h.
  induction h; eauto. eapply ms_refl.
  eapply ms_trans; eauto. eapply hr_app; eauto.
Qed.

Lemma HeadRed1_det (n:nat) (M N P : Tm n) : 
  HeadRed1 M N -> HeadRed1 M P -> N = P.
Proof.
  move=> h1 h2.
  induction M.
  all: inversion h1; inversion h2; subst. 
  - inversion H3. done.
  - inversion H5.
Admitted.
(*  - inversion H2.
  - rewrite (@IHM1 M3 M5) ; eauto.
Qed. *)

(* generic head-contraction to a HeadRed1-normal target (covers zero/succ) *)
Lemma HeadRed_contract_to {n} (M M' N : Tm n) :
  (forall P, ~ HeadRed1 N P) -> HeadRed1 M M' -> HeadRed M N -> HeadRed M' N.
Proof.
  move=> Hnf R HR. inversion HR; subst.
  - exfalso; eapply Hnf; exact R.
  - rewrite (HeadRed1_det R ltac:(eassumption)); assumption.
Qed.

Lemma HeadRed_contract_to_multi {n} (M M' N : Tm n) :
  (forall P, ~ HeadRed1 N P) -> HeadRed M M' -> HeadRed M N -> HeadRed M' N.
Proof.
  move=> Hnf R. induction R.
  - done.
  - move=> HM. apply IHR. eapply HeadRed_contract_to; eauto.
Qed.

Lemma nf_zero {n} : forall (P : Tm n), ~ HeadRed1 zero P.
Proof. move=> P H; inversion H. Qed.

Lemma nf_succ {n} (M : Tm n) : forall (P : Tm n), ~ HeadRed1 (succ M) P.
Proof. move=> P H; inversion H. Qed.

(* determinism of head reduction to a [succ] normal form (mirrors HeadRed_tpi_det) *)
Lemma HeadRed_succ_det {n} (M : Tm n) a b :
  HeadRed M (succ a) -> HeadRed M (succ b) -> a = b.
Proof.
  move=> h1. move: b. dependent induction h1.
  all: move=> b h2.
  - inversion h2; subst. congruence. inversion H.
  - inversion h2; subst. inversion H.
    specialize (IHh1 _ ltac:(reflexivity) b).
    have EQ : e2 = e3 by (eapply HeadRed1_det; eauto). subst. eauto.
Qed.


(* ============================================================
   Head reduction for tpi
   ============================================================ *)

Lemma HeadRed_tpi_det (n:nat) (M : Tm n) A1 B1 A2 B2 : 
  HeadRed M (tpi A1 B1) -> HeadRed M (tpi A2 B2) -> A1 = A2 /\ B1 = B2.
Proof.
  move=> h1. move:A2 B2.
  dependent induction h1.
  all: move=> A2 B2 h2. 
  - inversion h2; subst. done. inversion H.
  - inversion h2; subst. inversion H.
    specialize (IHh1 _ _ ltac:(reflexivity) A2 B2).
    have EQ: e2 = e3. eapply HeadRed1_det; eauto.
    subst.
    eauto.
Qed.

Lemma HeadRed_tpi_eq {n}( A1 : Tm n) B1 A2 B2 :
   HeadRed (tpi A1 B1) (tpi A2 B2) -> A1 = A2 /\ B1 = B2.
Proof. 
  move=> R1.
  have R2: HeadRed (tpi A1 B1) (tpi A1 B1).
  { eapply ms_refl. }
  eapply HeadRed_tpi_det; eauto.
Qed.

Lemma HeadRed1_tpi_expand {n} (M M' : Tm n) A B :
  HeadRed1 M M' ->
  HeadRed M' (tpi A B) ->
  HeadRed M  (tpi A B).
Proof.
  move=> R HR.
  eapply ms_trans; eauto.
Qed.

Lemma HeadRed1_tpi_contract {n} (M M' : Tm n) A B :
  HeadRed1 M M' ->
  HeadRed M  (tpi A B) ->
  HeadRed M' (tpi A B).
Proof.
  move=> R HR.
  inversion HR; subst.
  - (* M = tpi A B is HeadRed1-normal, so [HeadRed1 (tpi A B) M'] is impossible *)
    inversion R.
  - (* M ->1 e2 ->* tpi A B; determinism gives e2 = M' *)
    rewrite (HeadRed1_det R ltac:(eassumption)). assumption.
Qed.

(* multi-step contract of a [tpi]-target (HeadRed is deterministic) *)
Lemma HeadRed_tpi_contract {n} (M M' A : Tm n) (B : Tm (S n)) :
  HeadRed M M' -> HeadRed M (tpi A B) -> HeadRed M' (tpi A B).
Proof.
  move=> R. induction R.
  - done.
  - move=> HM. apply IHR. eapply HeadRed1_tpi_contract; eauto.
Qed.





