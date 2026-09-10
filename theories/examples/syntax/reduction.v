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
 (* Y-unfolding (Agda [headred-Y]): [fix g] unfolds to [g (fix g)]. *)
 | hr_fix g :
    HeadRed1 (fix_ g) (app g (fix_ g))
 (* based-J (Agda [headred-J]/[headred-J-scrut]): [jcase C d p] fires on a
    *literal* [rfl a], contracting to [app d a]; otherwise the proof reduces. *)
 | hr_jcase C d a :
    HeadRed1 (jcase C d (rfl a)) (app d a)
 | hr_jcase_scrut C d p p' :
    HeadRed1 p p' ->
    HeadRed1 (jcase C d p) (jcase C d p')
 (* Sigma projections (Agda SigmaProp [headred-beta-fst]/[headred-beta-snd] and
    the congruences [headred-fst]/[headred-snd]): a projection fires on a
    *literal* [mkpair]; otherwise the scrutinee reduces. *)
 | hr_pfst M N :
    HeadRed1 (pfst (mkpair M N)) M
 | hr_pfst_scrut M M' :
    HeadRed1 M M' ->
    HeadRed1 (pfst M) (pfst M')
 | hr_psnd M N :
    HeadRed1 (psnd (mkpair M N)) N
 | hr_psnd_scrut M M' :
    HeadRed1 M M' ->
    HeadRed1 (psnd M) (psnd M')
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

(* Head reduction is deterministic: the head redex is unique.  Induct on the
   first derivation and invert the second; the mismatched pairs all place a
   [HeadRed1] on a term that has no head redex ([abs], [zero], [succ _]). *)
Lemma HeadRed1_det (n:nat) (M N P : Tm n) : 
  HeadRed1 M N -> HeadRed1 M P -> N = P.
Proof.
  move=> h1. move: P.
  induction h1 as
    [ A M0 N0
    | Ma Mb N0 hM IH
    | M0 M1
    | M0 M1 N0
    | Mc Mc' M0 M1 hM IH
    | g
    | Cj dj aj
    | Cj dj pj pj' hP IHP
    | Fm Fn
    | Fm Fm' hF IHF
    | Sm Sn
    | Sm Sm' hS IHS ]; move=> P h2.
  - (* hr_beta vs. a reduction of the [abs] itself *)
    inversion h2; subst; [ reflexivity | ].
    exfalso.
    match goal with [ H : HeadRed1 (abs _ _) _ |- _ ] => inversion H end.
  - (* hr_app: either the function was an [abs] (impossible, it reduces) or
       congruence, and then the IH applies *)
    inversion h2; subst.
    + exfalso. inversion hM.
    + f_equal. eapply IH; eassumption.
  - (* hr_zero vs. a reduction of [zero] *)
    inversion h2; subst; [ reflexivity | ].
    exfalso.
    match goal with [ H : HeadRed1 zero _ |- _ ] => inversion H end.
  - (* hr_succ vs. a reduction of [succ _] *)
    inversion h2; subst; [ reflexivity | ].
    exfalso.
    match goal with [ H : HeadRed1 (succ _) _ |- _ ] => inversion H end.
  - (* hr_case: the scrutinee cannot be both a numeral and reducible *)
    inversion h2; subst.
    + exfalso. inversion hM.
    + exfalso. inversion hM.
    + f_equal. eapply IH; eassumption.
  - (* hr_fix: [fix g] has exactly one redex *)
    inversion h2; subst; reflexivity.
  - (* hr_jcase vs. a reduction of the [rfl] proof *)
    inversion h2; subst; [ reflexivity | ].
    exfalso.
    match goal with [ H : HeadRed1 (rfl _) _ |- _ ] => inversion H end.
  - (* hr_jcase_scrut: the proof cannot be both an [rfl] and reducible *)
    inversion h2; subst.
    + exfalso. inversion hP.
    + f_equal. eapply IHP; eassumption.
  - (* hr_pfst vs. a reduction of the [mkpair] *)
    inversion h2; subst; [ reflexivity | ].
    exfalso.
    match goal with [ H : HeadRed1 (mkpair _ _) _ |- _ ] => inversion H end.
  - (* hr_pfst_scrut: the scrutinee cannot be both a pair and reducible *)
    inversion h2; subst.
    + exfalso. inversion hF.
    + f_equal. eapply IHF; eassumption.
  - (* hr_psnd vs. a reduction of the [mkpair] *)
    inversion h2; subst; [ reflexivity | ].
    exfalso.
    match goal with [ H : HeadRed1 (mkpair _ _) _ |- _ ] => inversion H end.
  - (* hr_psnd_scrut *)
    inversion h2; subst.
    + exfalso. inversion hS.
    + f_equal. eapply IHS; eassumption.
Qed.

(* the two projection congruences, lifted to the reflexive-transitive closure
   (Agda [HeadRed-Fst]/[HeadRed-Snd]) *)
Lemma HeadRed_pfst {n:nat} (M1 M2 : Tm n) :
   HeadRed M1 M2 -> HeadRed (pfst M1) (pfst M2).
Proof.
  intro h.
  induction h; eauto. eapply ms_refl.
  eapply ms_trans; eauto. eapply hr_pfst_scrut; eauto.
Qed.

Lemma HeadRed_psnd {n:nat} (M1 M2 : Tm n) :
   HeadRed M1 M2 -> HeadRed (psnd M1) (psnd M2).
Proof.
  intro h.
  induction h; eauto. eapply ms_refl.
  eapply ms_trans; eauto. eapply hr_psnd_scrut; eauto.
Qed.

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

(* ============================================================
   Head reduction for the identity fragment.  [tid] and [rfl] are
   head-normal (no [HeadRed1] rule mentions them), so these mirror the
   [tpi] and [succ] lemmas exactly.
   ============================================================ *)

Lemma nf_tid {n} (A a b : Tm n) : forall (P : Tm n), ~ HeadRed1 (tid A a b) P.
Proof. move=> P H; inversion H. Qed.

Lemma nf_rfl {n} (M : Tm n) : forall (P : Tm n), ~ HeadRed1 (rfl M) P.
Proof. move=> P H; inversion H. Qed.

(* [tsig] and [mkpair] are both head-normal: a type former never reduces, and
   a pair is a value (only its projections reduce). *)
Lemma nf_tsig {n} (A : Tm n) (B : Tm (S n)) :
  forall (P : Tm n), ~ HeadRed1 (tsig A B) P.
Proof. move=> P H; inversion H. Qed.

Lemma nf_mkpair {n} (M N : Tm n) :
  forall (P : Tm n), ~ HeadRed1 (mkpair M N) P.
Proof. move=> P H; inversion H. Qed.

Lemma HeadRed_tid_det {n} (M : Tm n) A1 a1 b1 A2 a2 b2 :
  HeadRed M (tid A1 a1 b1) -> HeadRed M (tid A2 a2 b2) ->
  A1 = A2 /\ a1 = a2 /\ b1 = b2.
Proof.
  move=> h1. move: A2 a2 b2.
  dependent induction h1.
  all: move=> A2 a2 b2 h2.
  - inversion h2; subst. done. inversion H.
  - inversion h2; subst. inversion H.
    specialize (IHh1 _ _ _ ltac:(reflexivity) A2 a2 b2).
    have EQ : e2 = e3 by (eapply HeadRed1_det; eauto). subst.
    eauto.
Qed.

Lemma HeadRed_tid_eq {n} (A1 a1 b1 : Tm n) A2 a2 b2 :
  HeadRed (tid A1 a1 b1) (tid A2 a2 b2) -> A1 = A2 /\ a1 = a2 /\ b1 = b2.
Proof.
  move=> R1.
  have R2 : HeadRed (tid A1 a1 b1) (tid A1 a1 b1) by apply ms_refl.
  eapply HeadRed_tid_det; eauto.
Qed.

Lemma HeadRed_rfl_det {n} (M : Tm n) a b :
  HeadRed M (rfl a) -> HeadRed M (rfl b) -> a = b.
Proof.
  move=> h1. move: b. dependent induction h1.
  all: move=> b h2.
  - inversion h2; subst. congruence. inversion H.
  - inversion h2; subst. inversion H.
    specialize (IHh1 _ ltac:(reflexivity) b).
    have EQ : e2 = e3 by (eapply HeadRed1_det; eauto). subst. eauto.
Qed.

Lemma HeadRed1_tid_expand {n} (M M' A a b : Tm n) :
  HeadRed1 M M' -> HeadRed M' (tid A a b) -> HeadRed M (tid A a b).
Proof. move=> R HR. eapply ms_trans; eauto. Qed.

Lemma HeadRed1_tid_contract {n} (M M' A a b : Tm n) :
  HeadRed1 M M' -> HeadRed M (tid A a b) -> HeadRed M' (tid A a b).
Proof.
  move=> R HR.
  inversion HR; subst.
  - (* [tid A a b] is [HeadRed1]-normal *) inversion R.
  - rewrite (HeadRed1_det R ltac:(eassumption)). assumption.
Qed.

Lemma HeadRed_tid_contract {n} (M M' A a b : Tm n) :
  HeadRed M M' -> HeadRed M (tid A a b) -> HeadRed M' (tid A a b).
Proof.
  move=> R. induction R.
  - done.
  - move=> HM. apply IHR. eapply HeadRed1_tid_contract; eauto.
Qed.





(* ============================================================
   Head reduction at the Sigma codes.

   [tsig] and [mkpair] are both [HeadRed1]-normal ([nf_tsig]/[nf_mkpair]),
   so the [tpi] / [tid] groups transcribe verbatim.
   ============================================================ *)

Lemma HeadRed_tsig_det (n:nat) (M : Tm n) A1 B1 A2 B2 :
  HeadRed M (tsig A1 B1) -> HeadRed M (tsig A2 B2) -> A1 = A2 /\ B1 = B2.
Proof.
  move=> h1. move: A2 B2.
  dependent induction h1.
  all: move=> A2 B2 h2.
  - inversion h2; subst. done. inversion H.
  - inversion h2; subst. inversion H.
    specialize (IHh1 _ _ ltac:(reflexivity) A2 B2).
    have EQ: e2 = e3. eapply HeadRed1_det; eauto.
    subst. eauto.
Qed.

Lemma HeadRed_tsig_eq {n} (A1 : Tm n) B1 A2 B2 :
  HeadRed (tsig A1 B1) (tsig A2 B2) -> A1 = A2 /\ B1 = B2.
Proof.
  move=> R1.
  have R2: HeadRed (tsig A1 B1) (tsig A1 B1). { eapply ms_refl. }
  eapply HeadRed_tsig_det; eauto.
Qed.

Lemma HeadRed1_tsig_expand {n} (M M' : Tm n) A B :
  HeadRed1 M M' -> HeadRed M' (tsig A B) -> HeadRed M (tsig A B).
Proof. move=> R HR. eapply ms_trans; eauto. Qed.

Lemma HeadRed1_tsig_contract {n} (M M' : Tm n) A B :
  HeadRed1 M M' -> HeadRed M (tsig A B) -> HeadRed M' (tsig A B).
Proof.
  move=> R HR.
  inversion HR; subst.
  - (* [tsig A B] is [HeadRed1]-normal *) inversion R.
  - rewrite (HeadRed1_det R ltac:(eassumption)). assumption.
Qed.

Lemma HeadRed_tsig_contract {n} (M M' : Tm n) A B :
  HeadRed M M' -> HeadRed M (tsig A B) -> HeadRed M' (tsig A B).
Proof.
  move=> R. induction R.
  - done.
  - move=> HM. apply IHR. eapply HeadRed1_tsig_contract; eauto.
Qed.

Lemma HeadRed_mkpair_det {n} (M : Tm n) a1 b1 a2 b2 :
  HeadRed M (mkpair a1 b1) -> HeadRed M (mkpair a2 b2) -> a1 = a2 /\ b1 = b2.
Proof.
  move=> h1. move: a2 b2.
  dependent induction h1.
  all: move=> a2 b2 h2.
  - inversion h2; subst. done. inversion H.
  - inversion h2; subst. inversion H.
    specialize (IHh1 _ _ ltac:(reflexivity) a2 b2).
    have EQ: e2 = e3. eapply HeadRed1_det; eauto.
    subst. eauto.
Qed.

Lemma HeadRed1_mkpair_expand {n} (M M' a b : Tm n) :
  HeadRed1 M M' -> HeadRed M' (mkpair a b) -> HeadRed M (mkpair a b).
Proof. move=> R HR. eapply ms_trans; eauto. Qed.

Lemma HeadRed1_mkpair_contract {n} (M M' a b : Tm n) :
  HeadRed1 M M' -> HeadRed M (mkpair a b) -> HeadRed M' (mkpair a b).
Proof.
  move=> R HR.
  inversion HR; subst.
  - inversion R.
  - rewrite (HeadRed1_det R ltac:(eassumption)). assumption.
Qed.

Lemma HeadRed_mkpair_contract {n} (M M' a b : Tm n) :
  HeadRed M M' -> HeadRed M (mkpair a b) -> HeadRed M' (mkpair a b).
Proof.
  move=> R. induction R.
  - done.
  - move=> HM. apply IHR. eapply HeadRed1_mkpair_contract; eauto.
Qed.

(* ============================================================
   Head reduction for [jcase].

   [jcase] reduces in its *proof* argument ([hr_jcase_scrut]) and contracts
   once that argument is a literal [rfl] ([hr_jcase]).  So a proof that
   head-reduces to an [rfl] drives the whole eliminator to the base branch,
   which is what the adequacy driver for [J] needs.
   ============================================================ *)

Lemma HeadRed_jcase_scrut {n} (C d : Tm n) (p p' : Tm n) :
  HeadRed p p' -> HeadRed (jcase C d p) (jcase C d p').
Proof.
  move=> h. induction h.
  - apply ms_refl.
  - eapply ms_trans; [ apply hr_jcase_scrut; eassumption | assumption ].
Qed.

(* [jcase C d p] with [p] reducing to [rfl P0] drives to [app d P0]. *)
Lemma HeadRed_jcase {n} (C d p P0 : Tm n) :
  HeadRed p (rfl P0) -> HeadRed (jcase C d p) (app d P0).
Proof.
  move=> h.
  eapply ms_app; [ eapply HeadRed_jcase_scrut; exact h | ].
  eapply ms_trans; [ apply hr_jcase | apply ms_refl ].
Qed.
