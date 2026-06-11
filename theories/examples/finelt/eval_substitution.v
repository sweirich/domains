(* cf. EvalSubstitution.agda *)

From Stdlib Require Import Relations List Program
     ssreflect ssrfun ssrbool.
From Stdlib Require Import Classes.RelationClasses 
  Classes.Morphisms Lia Arith.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Require Import syntax.syntax.
Require Import syntax.typing.
Require Import findom.
Require Import types.
Require Import raw_semantics.

Import SyntaxNotations.
Import SubstNotations.

Import Raw.

Open Scope syntax_scope.

(** * renaming preserves evaluation *)

Lemma EvalRel_ren n (M : Tm n) (ρ : Env n) a  
  m  (ξ : fin n -> fin m) (ρ' : Env m) :
  (forall x, ρ x = ρ' (ξ x)) ->
  EvalRel M⟨ξ⟩ ρ' a <-> EvalRel M ρ a.
Proof.
  move: m ξ ρ ρ' a.
  induction M.
  all: move=> m ξ ρ ρ' a EQ.
  all: try done.
  - cbn. rewrite <- EQ. done.
  - cbn. destruct a; try done.
    split.
    all: move=> [Va [Vf [a [WT [ER h]]]]].
    all: repeat split; eauto.
    all: exists a.
    all: repeat split; eauto.
    all: try rewrite -> IHM1 in ER; try rewrite IHM1; eauto.
    all: move=> ui vi Ini APP.
    all: specialize (h ui vi Ini APP).
    all: destruct h as [x [Le [WT2 E2]]].
    all: exists x; repeat split; eauto.       
    rewrite <- (IHM2 _ (up_ren ξ) _ (x .: ρ')). eauto.
    auto_case.
    rewrite (IHM2 _ (up_ren ξ) (x .: ρ)); eauto.
    auto_case.
  - (* app *) cbn.
    destruct (is_bot a); try done.
    split.
    all: move=> [u [E1 E2]].
    all: exists u.
    rewrite -> IHM1 in E1; eauto.
    rewrite -> IHM2 in E2; eauto.
    rewrite -> IHM1 ; eauto.
    rewrite -> IHM2 ; eauto.
  - (* succ *)
    cbn.
    destruct (is_bot a); try done.
    split.
    all: move=> [Va [u [L E1]]].
    all: split; auto.
    all: exists u.
    all: split; auto.
    rewrite -> IHM in E1; eauto.
    rewrite -> IHM ; eauto.
  - (* tpi *)
    cbn.
    destruct a; try done.
    split.
    all: move=> [Va [Vl [ER [a0 [ER0 h]]]]].
    all: repeat split; auto.
    all: repeat split; auto.
    all: try rewrite IHM1 in ER; auto; try rewrite IHM1; auto.
    all: exists a0; split; [
     try rewrite IHM1 in ER0; auto; try rewrite IHM1; auto|].
    all: move=> u v Vu APP.
    all: destruct (h u v Vu APP) as [x [WTx [Le E2]]].
    all: exists x; repeat split; auto.
    all: try rewrite IHM2 in E2; auto; try rewrite IHM2; eauto.
    all: auto_case.
Qed.


Lemma EvalRel_wk {n} (M : Tm n) (ρ : Env n) u v :
  EvalRel M ρ u -> EvalRel M⟨↑⟩ (v .: ρ) u.
Proof.
  rewrite -> EvalRel_ren with (ρ:=ρ); eauto.
Qed.

Lemma EvalRel_unwk {n} (M : Tm n) (ρ : Env n) u v :
  EvalRel M⟨↑⟩ (v .: ρ) u -> EvalRel M ρ u.
Proof.
  rewrite <- EvalRel_ren with (ρ:=ρ); eauto.
Qed.

(** * Semantic substitution *)

(*
EvalRel-subst : {h g : Nat} (sigma : Sub h g)
  (M : Expr g) (rho : EnvApprox h) (rho' : EnvApprox g) ->
  CoherentEnv rho ->
  SubRel sigma rho rho' ->
  (u : FinEl) -> EvalRel M rho' u -> EvalRel (substExpr sigma M) rho u
*)

Definition Sub h g := fin h -> Tm g.

Definition SubRel {h g} (σ : Sub h g) (ρ' : Env h) (ρ : Env g) := 
  forall i, EvalRel (σ i) ρ (ρ' i).

Lemma SubRel_lift {h g} (σ : Sub h g) ρ' ρ u :
  SubRel σ ρ ρ' -> 
  valid u -> 
  SubRel (⇑σ) (u .: ρ) (u .: ρ').
Proof.
  move=> SR Vu [f|]. 
  move: (SR f) => h1. 
  eapply EvalRel_wk; eauto.
  split; eauto using le_refl.
Qed.

Lemma EvalRel_subst {m n} (σ : Sub m n) (M : Tm m)
  (ρ : Env m) (ρ' : Env n)  u : 
  valid_env ρ -> valid_env ρ' -> SubRel σ ρ ρ' -> 
  EvalRel M ρ u -> EvalRel M[σ] ρ' u.
Proof.
  move: n σ ρ ρ' u.
  dependent induction M.
  all: rename n_Tm into m; try rename n into n1.
  all: move=> n σ ρ ρ' u Vρ Vρ' SR E.
  all: cbn in *.
  all: try solve [destruct (is_bot u); auto].
  - (* var *)
    move: (SR f) => h1. 
    eapply EvalRel_down; eauto.
  - (* abs *)
    destruct u; try done.
    move: E => [Vf [Nl [a [WT [E1 F]]]]].
    repeat split; eauto.
    exists a. repeat split; eauto.
    move=> u v Vu APP.
    move: (F _ _ Vu APP) => [x [Le [WT2 E2]]].
    have Vx: valid x. eapply wt_valid_tm; eauto.
    exists x. 
    repeat split; eauto.
    eauto using valid_cons, SubRel_lift.
  - (* app *)
    destruct (is_bot u); try done.
    move: E => [a [E1 E2]].
    eauto.
  - (* succ *)
    destruct (is_bot u); try done.
    move: E => [h1 [a [L1 E1]]].
    eauto.
  - (* tpi *)
    destruct u; try done.
    move: E => [Vu [Vf [E1 [a0 [E0 h1]]]]].
    all: repeat split; eauto.
    exists a0. 
    split. eapply IHM1; eauto.

    move=> ui vi Vui APP.
    destruct (h1 _ _ Vui APP) as [x [Le [WT2 E2]]].
    have Vx: valid x. eapply wt_valid_tm; eauto.
    exists x. 
    repeat split; eauto.
    eauto using valid_cons, SubRel_lift.
Qed.

Lemma EvalRel_subst1_backwards {n} 
  (B : Tm (S n)) (M : Tm n) 
  (ρ : Env n) v u : 
  valid_env ρ -> 
  EvalRel M ρ v -> 
  EvalRel B (v .: ρ) u ->
  EvalRel B[M..] ρ u.
Proof.
  move=> Vρ E1 E2.
  eapply EvalRel_subst with (ρ := v .: ρ); 
    eauto using valid_cons, EvalRel_valid.
  unfold SubRel. auto_case.
  eauto using le_refl.
Qed.

(** * MaxRel *)

Definition MaxSubRel {h g} (σ : Sub h g) (ρ' : Env h) (ρ : Env g) := 
  forall i, forall u,  EvalRel (σ i) ρ u -> le u (ρ' i).

Lemma MaxSubRel_lift {h g} (σ : Sub h g) ρ' ρ u :
  MaxSubRel σ ρ ρ' -> 
  valid u -> 
  MaxSubRel (⇑σ) (u .: ρ) (u .: ρ').
Proof.
  move=> SR Vu [f|] v; cbn. 
  move: (SR f v) => h1 h2.
  eapply EvalRel_unwk in h2; eauto.
  eauto using le_refl.
Qed.

Lemma EvalRel_subst_forward_max {m n} (σ : Sub m n) (M : Tm m)
  (ρ : Env m) (ρ' : Env n)  u : 
  valid_env ρ -> valid_env ρ' -> MaxSubRel σ ρ ρ' -> 
  EvalRel M[σ] ρ' u -> EvalRel M ρ u.
Proof.
  move: n σ ρ ρ' u.
  dependent induction M.
  all: rename n_Tm into m; try rename n into n1.
  all: move=> n σ ρ ρ' u Vρ Vρ' SR E.
  all: cbn in *.
  all: try solve [destruct (is_bot u); auto].
  - (* var *)
    move: (SR f) => h1. 
    split; eauto using EvalRel_valid.
  - (* abs *)
    destruct u; try done.
    move: E => [Vf [Nf [a [WT [E1 F]]]]].
    repeat split; eauto.
    exists a. repeat split; eauto.
    move=> u v Vu APP.
    move: (F _ _ Vu APP) => [x [Le [WT2 E2]]].
    have Vx: valid x. eapply wt_valid_tm; eauto.
    exists x.
    repeat split; eauto.
    eauto using valid_cons, MaxSubRel_lift.
  - (* app *)
    destruct (is_bot u); try done.
    move: E => [a [E1 E2]].
    eauto.
  - (* succ *)
    destruct (is_bot u); try done.
    move: E => [h1 [a [L1 E1]]].
    eauto.
  - (* tpi *)
    destruct u; try done.
    move: E => [Vf [Vu [E1 [a0 [E0 h1]]]]].
    all: repeat split; eauto.
    exists a0. split. eauto.
    move=> ui vi Vui APP.
    destruct (h1 _ _ Vui APP) as [x [Le [WT2 E2]]].
    have Vx: valid x. eapply wt_valid_tm; eauto.
    exists x. 
    repeat split; eauto.
    eauto using valid_cons, MaxSubRel_lift.
Qed.

(** * Forward substitution with witness environment

    Translation of EvalRel-subst-forward-wit and EvalRel-subst1-forward
    from EvalSubstitution.agda. Given EvalRel M[σ] ρ u where σ : Sub h g,
    M : Tm h and ρ : Env g, we produce a witness env ρ' : Env h such that
    valid_env ρ', SubRel σ ρ' ρ, and EvalRel M ρ' u. The subst1 corollary
    picks v := ρ' var_zero. *)

(** ** bot_env *)

Definition bot_env {n} : Env n := fun _ => bot.

Lemma bot_env_valid n : valid_env (@bot_env n).
Proof. move=> ?. done. Qed.

(* SubRel σ bot_env ρ : forall i, EvalRel (σ i) ρ bot, by EvalRel_bot. *)
Lemma SubRel_bot_env {h g} (σ : Sub h g) (ρ : Env g) :
  SubRel σ bot_env ρ.
Proof. move=> i. unfold bot_env. apply EvalRel_bot. Qed.

(** ** singleton_env: u at position i, bot elsewhere *)

Fixpoint singleton_env (n : nat) : fin n -> elt -> Env n :=
  match n return fin n -> elt -> Env n with
  | 0    => fun _ _ => @null elt
  | S k  => fun i u =>
      match (i : option (fin k)) with
      | None   => u .: bot_env
      | Some j => bot .: @singleton_env k j u
      end
  end.

Lemma singleton_env_valid n (i : fin n) u :
  valid u -> valid_env (@singleton_env n i u).
Proof.
  move: i. induction n; first by [move=> []].
  move=> [j|] Vu; cbn.
  - apply valid_cons; first done. by apply IHn.
  - apply valid_cons; first done. apply bot_env_valid.
Qed.

Lemma singleton_env_lookup n (i : fin n) u :
  @singleton_env n i u i = u.
Proof.
  move: i. induction n; first by [move=> []].
  by move=> [j|]; cbn; eauto.
Qed.

(* SubRel σ (singleton_env i u) ρ : forall j, EvalRel (σ j) ρ (singleton_env i u j).
   At j = i: EvalRel (σ i) ρ u.  At j ≠ i: EvalRel (σ j) ρ bot, by EvalRel_bot. *)
Lemma SubRel_singleton_env {h g} (σ : Sub h g) (ρ : Env g) (i : fin h) u :
  EvalRel (σ i) ρ u -> SubRel σ (@singleton_env h i u) ρ.
Proof.
  move: i σ. induction h; first by [move=> []].
  move=> [j|] σ E.
  - move=> [k|]; cbn.
    + by apply (IHh j (fun x => σ (Some x))).
    + apply EvalRel_bot.
  - move=> [k|]; cbn.
    + apply EvalRel_bot.
    + exact E.
Qed.

(** ** le_env: reflexivity and transitivity *)

Lemma le_env_refl {n} (ρ : Env n) : valid_env ρ -> le_env ρ ρ.
Proof. move=> Vρ x. apply le_refl, Vρ. Qed.

Lemma le_env_trans {n} (ρ1 ρ2 ρ3 : Env n) :
  valid_env ρ1 -> valid_env ρ2 -> valid_env ρ3 ->
  le_env ρ1 ρ2 -> le_env ρ2 ρ3 -> le_env ρ1 ρ3.
Proof.
  move=> V1 V2 V3 L12 L23 x.
  exact (le_trans (V1 x) (V2 x) (V3 x) (L12 x) (L23 x)).
Qed.

(** ** compatible env *)

Definition compat_env {n} (ρ1 ρ2 : Env n) := forall x, compatible (ρ1 x) (ρ2 x).

Lemma compat_env_from_SubRel {h g} (σ : Sub h g) (ρ : Env g) ρ1 ρ2 :
  valid_env ρ -> SubRel σ ρ1 ρ -> SubRel σ ρ2 ρ -> compat_env ρ1 ρ2.
Proof.
  move=> Vρ S1 S2 x.
  exact (EvalRel_compatible Vρ (S1 x) (S2 x)).
Qed.

(** ** sup_env: pointwise lub. 
    Total by defaulting to bot when undefined;
    under compat_env it equals the actual lub. *)

Definition sup_env {n} (ρ1 ρ2 : Env n) : Env n :=
  fun x => lub (ρ1 x) (ρ2 x).

Lemma sup_env_at {n} (ρ1 ρ2 : Env n) x v :
  lub (ρ1 x) (ρ2 x) = v -> sup_env ρ1 ρ2 x = v.
Proof. by move=> <-. Qed.

Lemma sup_env_valid {n} (ρ1 ρ2 : Env n) :
  valid_env ρ1 -> valid_env ρ2 -> compat_env ρ1 ρ2 ->
  valid_env (sup_env ρ1 ρ2).
Proof.
  move=> V1 V2 C x. rewrite /sup_env.
  eapply (valid_lub (C x)); [apply V1 | apply V2].
Qed.

Lemma le_env_sup_env_left {n} (ρ1 ρ2 : Env n) :
  valid_env ρ1 -> valid_env ρ2 -> compat_env ρ1 ρ2 ->
  le_env ρ1 (sup_env ρ1 ρ2).
Proof.
  move=> V1 V2 C x. rewrite /sup_env.
  eapply (le_lub_left (C x)); [apply V1 | apply V2].
Qed.

Lemma le_env_sup_env_right {n} (ρ1 ρ2 : Env n) :
  valid_env ρ1 -> valid_env ρ2 -> compat_env ρ1 ρ2 ->
  le_env ρ2 (sup_env ρ1 ρ2).
Proof.
  move=> V1 V2 C x. rewrite /sup_env.
  eapply (le_lub_right (C x)); [apply V1 | apply V2].
Qed.

Lemma SubRel_sup_env {h g} (σ : Sub h g) (ρ : Env g) ρ1 ρ2 :
  valid_env ρ -> valid_env ρ1 -> valid_env ρ2 ->
  SubRel σ ρ1 ρ -> SubRel σ ρ2 ρ ->
  SubRel σ (sup_env ρ1 ρ2) ρ.
Proof.
  move=> Vρ V1 V2 S1 S2 i.
  have CC: compatible (ρ1 i) (ρ2 i)
    := EvalRel_compatible Vρ (S1 i) (S2 i).
  rewrite (sup_env_at (v := lub (ρ1 i) (ρ2 i)) erefl).
  eapply EvalRel_sup with (u := ρ1 i) (u' := ρ2 i); eauto.
Qed.

(** ** combine_fwd: combine two SubRel witness environments *)

Lemma combine_fwd {h g} (σ : Sub h g) (ρ : Env g) ρ1 ρ2 :
  valid_env ρ -> valid_env ρ1 -> valid_env ρ2 ->
  SubRel σ ρ1 ρ -> SubRel σ ρ2 ρ ->
  exists ρ',
    valid_env ρ' /\ SubRel σ ρ' ρ /\ le_env ρ1 ρ' /\ le_env ρ2 ρ'.
Proof.
  move=> Vρ V1 V2 S1 S2.
  have C: compat_env ρ1 ρ2 := @compat_env_from_SubRel _ _ σ ρ ρ1 ρ2 Vρ S1 S2.
  exists (sup_env ρ1 ρ2). repeat split.
  - by apply sup_env_valid.
  - eapply SubRel_sup_env; eauto.
  - by apply le_env_sup_env_left.
  - by apply le_env_sup_env_right.
Qed.

(** ** Decompositions for SubRel under lifted substitutions

    If SubRel (⇑σ) ρ' (z .: ρ) (where ρ' : Env (S h), σ : Sub h g),
    we can extract:
    - tail ρ' = ρ' ∘ Some satisfies SubRel σ (tail ρ') ρ.
    - head ρ' = ρ' var_zero satisfies valid (head ρ') and le (head ρ') z. *)

Lemma SubRel_lift_inv {h g} (σ : Sub h g) (ρ : Env g) z (ρ' : Env (S h)) :
  SubRel (⇑σ) ρ' (z .: ρ) ->
  SubRel σ (fun x => ρ' (Some x)) ρ.
Proof.
  move=> SR i.
  move: (SR (Some i)) => H.
  cbn in H.
  (* ⇑σ (Some i) = (σ i)⟨↑⟩ in ρ-context (z .: ρ). *)
  asimpl in H.
  eapply EvalRel_unwk. eassumption.
Qed.

Lemma SubRel_lift_head {h g} (σ : Sub h g) (ρ : Env g) z (ρ' : Env (S h)) :
  SubRel (⇑σ) ρ' (z .: ρ) ->
  valid (ρ' var_zero) /\ le (ρ' var_zero) z.
Proof.
  move=> SR. by move: (SR var_zero); cbn.
Qed.

(** ** Forward result type *)

Definition FwdResult {h g} (σ : Sub h g) (M : Tm h) (ρ : Env g) (u : elt) : Prop :=
  exists ρ', valid_env ρ' /\ SubRel σ ρ' ρ /\ EvalRel M ρ' u.

(** ** Fold over edge list to combine per-edge witness environments

    Given a list of edges, with for each (u,v) ∈ gs an x and a source-env
    witness ρ_uv such that EvalRel M (x .: ρ_uv) v with le x u and wt x a,
    build a single source env ρ' ≥ acc supporting all edges. *)

Lemma fold_edge_fwd {h g} (σ : Sub h g) (ρ : Env g)
  (M : Tm (S h)) (a : elt) :
  forall (gs : list (elt * elt)) (acc : Env h),
    valid_env ρ -> valid_env acc -> SubRel σ acc ρ ->
    (forall u v, valid u -> app gs u = v ->
       exists x (h: wt x a) ρ_uv,
         le x u /\ valid_env ρ_uv /\
         SubRel σ ρ_uv ρ /\
         EvalRel M (x .: ρ_uv) v) ->
    exists ρ',
      valid_env ρ' /\ SubRel σ ρ' ρ /\ le_env acc ρ' /\
      forall u v, valid u -> app gs u = v ->
        exists x (h: wt x a), le x u /\ EvalRel M (x .: ρ') v.
Proof.
Admitted.
(*
  induction gs as [|[u v] gs IH].
  - move=> acc Vρ Vacc SRacc _.
    exists acc. repeat split; auto.
    + by apply le_env_refl.
    + move=> u v Vu APP.
      cbn in APP. inversion APP. subst.
      exists bot. split. eapply wt_bot. eapply wt_
  - move=> acc Vρ Vacc SRacc body.
    move: (body u v ltac:(left; reflexivity))
      => [x   [Wtx [ρ_uv [Lex [Vρuv [SRρuv ERuv]]]]]].
    move: (@combine_fwd _ _ σ ρ acc ρ_uv Vρ Vacc Vρuv SRacc SRρuv)
      => [mid [Vmid [SRmid [LEacc LEuv]]]].
    have IH' := IH mid Vρ Vmid SRmid
                  (fun u' v' h => body u' v' (or_intror h)).
    move: IH' => [ρ' [Vρ' [SRρ' [LEmid bodyAll]]]].
    have LEρuv : le_env ρ_uv ρ'
      := le_env_trans Vρuv Vmid Vρ' LEuv LEmid.
    have LEacc' : le_env acc ρ'
      := le_env_trans Vacc Vmid Vρ' LEacc LEmid.
    exists ρ'. repeat split; auto.
    move=> u' v' [EQ|InGS].
    * inversion EQ; subst.
      have Vx: valid x by eapply wt_valid_tm; eauto.
      exists x. repeat split; auto.
      have V1 : valid_env (x .: ρ_uv) := valid_cons Vx Vρuv.
      have V2 : valid_env (x .: ρ') := valid_cons Vx Vρ'.
      have LE : le_env (x .: ρ_uv) (x .: ρ').
      { move=> [k|]; cbn.
        - apply LEρuv.
        - apply le_refl. exact Vx. }
      exact (EvalRel_mono_env ERuv V1 V2 LE).
    * by apply bodyAll.
Qed. *)

(** ** Main forward witness lemma *)

Lemma EvalRel_subst_forward_wit {h g} (σ : Sub h g)
  (M : Tm h) (ρ : Env g) (u : elt) :
  valid_env ρ -> EvalRel M[σ] ρ u -> FwdResult σ M ρ u.
Proof.
  move: g σ ρ u.
  dependent induction M.
  all: rename n_Tm into m; try rename n into n1.
  all: move=> n σ ρ u Vρ E.
  all: cbn in E.
  - (* var *)
    have Vu: valid u by eapply EvalRel_valid; eauto.
    exists (@singleton_env m f u). split; [|split].
    + by apply singleton_env_valid.
    + by apply SubRel_singleton_env.
    + cbn [EvalRel]. split; first exact Vu.
      rewrite singleton_env_lookup. by apply le_refl.
  - (* abs *)
    destruct u as [| | | | | |l].
    1:{ (* bot *) exists bot_env. split; [|split].
        - by apply bot_env_valid.
        - by apply SubRel_bot_env.
        - by cbn. }
    all: try (exfalso; cbn in E; done).
    (* u = abs l *)
    move: E => [Vf [Nl [a [WT [EA body]]]]].
    move: (IHM1 _ _ _ _ Vρ EA) => [ρA [VρA [SRρA EA']]].
    have body' : forall u v, valid u -> app l u = v ->
       exists x (h:wt x a) ρ_uv,
         le x u /\ valid_env ρ_uv /\
         SubRel σ ρ_uv ρ /\
         EvalRel M2 (x .: ρ_uv) v.
    { move=> u' v' Vu' APP.
      move: (body u' v' Vu' APP) => [x [Wtx [Lx  Ev]]].
      have Vx : valid x by eapply wt_valid_tm; eauto.
      have Vxρ : valid_env (x .: ρ) by apply valid_cons.
      move: (IHM2 _ _ _ _ Vxρ Ev) => [ρ_xv [Vρxv [SRxv ERxv]]].
      pose ρ_uv := fun y => ρ_xv (Some y).
      have Vρuv : valid_env ρ_uv by move=> y; apply Vρxv.
      have SRtail : SubRel σ ρ_uv ρ by eapply SubRel_lift_inv; eauto.
      move: (SubRel_lift_head SRxv) => [Vh Lh].
      have ER' : EvalRel M2 (x .: ρ_uv) v'.
      { have V1 : valid_env (x .: ρ_uv) := valid_cons Vx Vρuv.
        have LE : le_env ρ_xv (x .: ρ_uv).
        { move=> [k|]; cbn.
          - apply le_refl. by apply Vρxv.
          - exact Lh. }
        exact (EvalRel_mono_env ERxv Vρxv V1 LE). }
      exists x. exists Wtx. exists ρ_uv. by repeat split. }

    move: (@fold_edge_fwd _ _ σ ρ M2 a l ρA Vρ VρA SRρA body')
      => [ρ' [Vρ' [SRρ' [LEρA bodyAll]]]].
    exists ρ'. split; [|split]; auto.
    repeat split; eauto.
    cbn. exists a. repeat split; auto.
    eapply EvalRel_mono_env; eauto.
  - (* app *)
    destruct (is_bot u) eqn:Hb.
    { exists bot_env. split; [|split].
      - by apply bot_env_valid.
      - by apply SubRel_bot_env.
      - cbn. by rewrite Hb. }
    move: E => [a [E1 E2]].
    move: (IHM1 _ _ _ _ Vρ E1) => [ρ1 [V1 [SR1 ER1]]].
    move: (IHM2 _ _ _ _ Vρ E2) => [ρ2 [V2 [SR2 ER2]]].
    move: (@combine_fwd _ _ σ ρ ρ1 ρ2 Vρ V1 V2 SR1 SR2)
      => [ρ' [Vρ' [SR' [LE1 LE2]]]].
    exists ρ'. split; [|split]; auto.
    cbn. rewrite Hb. exists a. split.
    + eapply EvalRel_mono_env; eauto.
    + eapply EvalRel_mono_env; eauto.
  - (* zero *)
    exists bot_env. split; [|split].
    + by apply bot_env_valid.
    + by apply SubRel_bot_env.
    + cbn. exact E.
  - (* succ *)
    destruct (is_bot u) eqn:Hb.
    { exists bot_env. split; [|split].
      - by apply bot_env_valid.
      - by apply SubRel_bot_env.
      - cbn. by rewrite Hb. }
    move: E => [Vu [a [Le ER1]]].
    move: (IHM _ _ _ _ Vρ ER1) => [ρ' [Vρ' [SR' ER']]].
    exists ρ'. split; [|split]; auto.
    cbn. rewrite Hb. split; auto. by exists a.
  - (* nrec — no non-bot result *)
    destruct (is_bot u) eqn:Hb; try done.
    exists bot_env. split; [|split].
    + by apply bot_env_valid.
    + by apply SubRel_bot_env.
    + cbn. by rewrite Hb.
  - (* tnat *)
    exists bot_env. split; [|split].
    + by apply bot_env_valid.
    + by apply SubRel_bot_env.
    + cbn. exact E.
  - (* tpi *)
    destruct u as [| | | | |e l|].
    1:{ (* bot *) exists bot_env. split; [|split].
        - by apply bot_env_valid.
        - by apply SubRel_bot_env.
        - by cbn. }
    all: try (exfalso; cbn in E; done).
    (* u = tpi e l *)
    move: E => [Vu [Vf [EA [a0 [Ea0 body]]]]].
    move: (IHM1 _ _ _ _ Vρ EA) => [ρA [VρA [SRρA EA']]].
    move: (IHM1 _ σ ρ _ Vρ Ea0) => [ρA0 [VρA0 [SRρA0 EA0']]]. 
    move: (combine_fwd Vρ VρA VρA0 SRρA SRρA0) => [ρA1 [VρA1 [SRρA1 [LEρA LEρA0]]]].
    have body' : forall u' v', valid u' -> app l u' = v' ->
      exists x (h: wt x a0) ρ_uv,
        le x u' /\ valid_env ρ_uv /\
        SubRel σ ρ_uv ρ /\
        EvalRel M2 (x .: ρ_uv) v'.
    { move=> u' v' Vu' APP.
      move: (body u' v' Vu' APP) => [x [Wtx [Lx  Ev]]].
      have Vx: valid x by eapply wt_valid_tm; eauto.
      have Vxρ: valid_env (x .: ρ) by apply valid_cons.
      move: (IHM2 _ _ _ _ Vxρ Ev) => [ρ_xv [Vρxv [SRxv ERxv]]].
      pose ρ_uv := fun y => ρ_xv (Some y).
      have Vρuv : valid_env ρ_uv by move=> y; apply Vρxv.
      have SRtail : SubRel σ ρ_uv ρ by eapply SubRel_lift_inv; eauto.
      move: (SubRel_lift_head SRxv) => [Vh Lh].
      have ER' : EvalRel M2 (x .: ρ_uv) v'.
      { have V1 : valid_env (x .: ρ_uv) := valid_cons Vx Vρuv.
        have LE : le_env ρ_xv (x .: ρ_uv).
        { move=> [k|]; cbn.
          - apply le_refl. by apply Vρxv.
          - exact Lh. }
        exact (EvalRel_mono_env ERxv Vρxv V1 LE). }
      fold fin in ρ_uv.
      exists x, Wtx, ρ_uv. by repeat split. }
    move: (@fold_edge_fwd _ _ σ ρ M2 a0 l ρA1 Vρ VρA1 SRρA1 body')
      => [ρ' [Vρ' [SRρ' [LEρ' bodyAll]]]].
    exists ρ'. split; [|split]; first done.
    { exact SRρ'. }
    cbn. repeat split; eauto. 
    eapply EvalRel_mono_env; eauto. eapply le_env_trans with (ρ2 := ρA1); eauto.
    exists a0. split.
    eapply EvalRel_mono_env; eauto.  eapply le_env_trans with (ρ2 := ρA1); eauto.
    exact bodyAll.
  - (* tuniv *)
    exists bot_env. split; [|split].
    + by apply bot_env_valid.
    + by apply SubRel_bot_env.
    + cbn. exact E.
Qed.

(** ** EvalRel_subst1_forward as a corollary *)

Lemma EvalRel_subst1_forward n (M : Tm (S n)) (N : Tm n) (ρ : Env n) u :
  valid_env ρ ->
  EvalRel M[N..] ρ u ->
  exists v, EvalRel N ρ v /\ EvalRel M (v .: ρ) u.
Proof.
  move=> Vρ E.
  (* M[N..] = M[N .: var]. Apply forward witness. *)
  have E' : EvalRel M[N .: (var)] ρ u by exact E.
  move: (@EvalRel_subst_forward_wit _ _ (N .: (var)) M ρ u Vρ E')
    => [ρ' [Vρ' [SR ER]]].
  set v := ρ' var_zero.
  have hv : EvalRel N ρ v by move: (SR var_zero); cbn.
  have Vv : valid v by eapply EvalRel_valid; eauto.
  exists v. split; auto.
  eapply EvalRel_mono_env; try eassumption.
  - by apply valid_cons.
  - unfold le_env. auto_case.
    + (* Some f case *)
      move: (SR (Some f)). cbn. by move=> [_ ?].
    + (* var_zero case *)
      apply le_refl, Vv.
Qed.

