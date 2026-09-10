(** * eval_substitution.v: Renaming and substitution for [EvalRel]

    (cf. [MIN/Model/EvalSubstitution.agda].)

    This file shows how the evaluation relation [EvalRel] interacts with
    renamings and substitutions.  The two directions are:
    - *renaming/backward substitution*: an approximation of [M] under a related
      environment is an approximation of the substituted term [M[σ]]
      ([EvalRel_subst], via [SubRel]);
    - *forward substitution*: an approximation of [M[σ]] comes from one of [M]
      under a witness environment built from the substitution
      ([EvalRel_subst_forward_max] / [EvalRel_subst1_forward]).

    The forward direction is the harder one and is organized around building a
    per-variable *witness environment* and combining the per-edge witnesses
    with [sup_env] / [fold_edge_fwd]. *)

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
  - (* ncase — renaming commutes through the case branches *)
    cbn. split.
    + move=> [w [EM Hb]]. exists w. split.
      * rewrite -> IHM1 in EM; eauto.
      * destruct w as [ | | | | v | | | | | | | | ]; cbn in Hb |- *; try contradiction.
        -- exact Hb.
        -- rewrite -> IHM2 in Hb; eauto.
        -- rewrite <- (IHM3 _ (up_ren ξ) _ (v .: ρ')). exact Hb. auto_case.
    + move=> [w [EM Hb]]. exists w. split.
      * rewrite -> IHM1; eauto.
      * destruct w as [ | | | | v | | | | | | | | ]; cbn in Hb |- *; try contradiction.
        -- exact Hb.
        -- rewrite -> IHM2; eauto.
        -- rewrite -> (IHM3 _ (up_ren ξ) (v .: ρ) (v .: ρ')). exact Hb. auto_case.
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
  - (* fix_: relabel the Kleene step through the renaming IH *)
    cbn. split.
    + move=> [k HA]. exists k. eapply Approx_mon; [ | exact HA ].
      move=> p w Hst. exact (proj1 (IHM _ ξ ρ ρ' _ EQ) Hst).
    + move=> [k HA]. exists k. eapply Approx_mon; [ | exact HA ].
      move=> p w Hst. exact (proj2 (IHM _ ξ ρ ρ' _ EQ) Hst).
  - (* tid: componentwise, no binders *)
    cbn. destruct a; try done. split.
    all: move=> [V [EA [E0 E1]]].
    all: split; [ exact V | ].
    all: try (rewrite -> IHM1 in EA; eauto);
         try (rewrite -> IHM2 in E0; eauto);
         try (rewrite -> IHM3 in E1; eauto).
    all: split; [ | split ]; eauto.
    all: try (rewrite -> IHM1; eauto);
         try (rewrite -> IHM2; eauto);
         try (rewrite -> IHM3; eauto).
  - (* rfl *)
    cbn. destruct a; try done. split.
    + move=> H. rewrite -> IHM in H; eauto.
    + move=> H. rewrite -> IHM; eauto.
  - (* jcase — renaming commutes through the proof dispatch *)
    cbn. split.
    + move=> [w [EM Hb]]. exists w. split.
      * rewrite -> IHM3 in EM; eauto.
      * destruct w as [ | | | | | | | | v | | | | ]; cbn in Hb |- *; try contradiction.
        -- exact Hb.
        -- rewrite -> IHM2 in Hb; eauto.
    + move=> [w [EM Hb]]. exists w. split.
      * rewrite -> IHM3; eauto.
      * destruct w as [ | | | | | | | | v | | | | ]; cbn in Hb |- *; try contradiction.
        -- exact Hb.
        -- rewrite -> IHM2; eauto.
  - (* tsig: the [tpi] argument.  Same clause shape, but written with the iff
       projections rather than copied from [tpi] -- that case's [all:]-chain
       leans on how [destruct] happens to name the components. *)
    cbn. destruct a; try done.
    split.
    + move=> [Va [Vf [ERa [a' [ERa' h]]]]].
      split; [ exact Va | ]. split; [ exact Vf | ].
      split; [ exact (proj1 (IHM1 _ ξ ρ ρ' _ EQ) ERa) | ].
      exists a'. split; [ exact (proj1 (IHM1 _ ξ ρ ρ' _ EQ) ERa') | ].
      move=> ui vi Vui APP.
      destruct (h ui vi Vui APP) as [x [WTx [Lex E2]]].
      have EQ2 : forall y, (x .: ρ) y = (x .: ρ') (up_ren ξ y) by auto_case.
      exists x, WTx. split; [ exact Lex | ].
      exact (proj1 (IHM2 _ (up_ren ξ) (x .: ρ) (x .: ρ') vi EQ2) E2).
    + move=> [Va [Vf [ERa [a' [ERa' h]]]]].
      split; [ exact Va | ]. split; [ exact Vf | ].
      split; [ exact (proj2 (IHM1 _ ξ ρ ρ' _ EQ) ERa) | ].
      exists a'. split; [ exact (proj2 (IHM1 _ ξ ρ ρ' _ EQ) ERa') | ].
      move=> ui vi Vui APP.
      destruct (h ui vi Vui APP) as [x [WTx [Lex E2]]].
      have EQ2 : forall y, (x .: ρ) y = (x .: ρ') (up_ren ξ y) by auto_case.
      exists x, WTx. split; [ exact Lex | ].
      exact (proj2 (IHM2 _ (up_ren ξ) (x .: ρ) (x .: ρ') vi EQ2) E2).
  - (* mkpair: componentwise, no binders *)
    cbn. destruct a; try done.
    split.
    + move=> [V [E1 E2]].
      split; [ exact V | ].
      split; [ exact (proj1 (IHM1 _ ξ ρ ρ' _ EQ) E1)
             | exact (proj1 (IHM2 _ ξ ρ ρ' _ EQ) E2) ].
    + move=> [V [E1 E2]].
      split; [ exact V | ].
      split; [ exact (proj2 (IHM1 _ ξ ρ ρ' _ EQ) E1)
             | exact (proj2 (IHM2 _ ξ ρ ρ' _ EQ) E2) ].
  - (* pfst: the renaming passes straight through the projection *)
    cbn. destruct (is_bot a); try done.
    split.
    + move=> [y E]. exists y. exact (proj1 (IHM _ ξ ρ ρ' _ EQ) E).
    + move=> [y E]. exists y. exact (proj2 (IHM _ ξ ρ ρ' _ EQ) E).
  - (* psnd *)
    cbn. destruct (is_bot a); try done.
    split.
    + move=> [x E]. exists x. exact (proj1 (IHM _ ξ ρ ρ' _ EQ) E).
    + move=> [x E]. exists x. exact (proj2 (IHM _ ξ ρ ρ' _ EQ) E).
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

(** A substitution maps each of [h] variables to a term over [g] variables. *)
Definition Sub h g := fin h -> Tm g.

(** [SubRel σ ρ' ρ]: the environment [ρ'] (over the source scope) is realized
    by the substitution [σ] under [ρ], i.e. each [ρ' i] is an approximation of
    [σ i] in [ρ].  This is the relation transported by [EvalRel_subst]. *)
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

(** Substitution lemma (backward): if [ρ] is realized by [σ] under [ρ'], then
    every approximation of [M] under [ρ] is an approximation of [M[σ]] under
    [ρ']. *)
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
  - (* ncase *)
    move: E => [w [EM Hb]]. exists w. split.
    + eapply IHM1; eauto.
    + destruct w as [ | | | | v | | | | | | | | ]; try contradiction.
      * exact Hb.
      * eapply IHM2; eauto.
      * have Vv : valid v := EvalRel_valid EM.
        eapply IHM3; [ | | | exact Hb ]; eauto using valid_cons, SubRel_lift.
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
  - (* fix_: relabel the Kleene step through the substitution IH *)
    move: E => [k HA]. exists k.
    eapply Approx_mon; [ | exact HA ].
    move=> p w Hst. eapply IHM; eauto.
  - (* tid: componentwise *)
    destruct u; try done.
    move: E => [V [EA [E0 E1]]].
    split; [ exact V | ].
    split; [ eapply IHM1; eauto | ].
    split; [ eapply IHM2; eauto | eapply IHM3; eauto ].
  - (* rfl *)
    destruct u; try done. eapply IHM; eauto.
  - (* jcase *)
    move: E => [w [EM Hb]]. exists w. split.
    + eapply IHM3; eauto.
    + destruct w as [ | | | | | | | | v | | | | ]; try contradiction.
      * exact Hb.
      * eapply IHM2; eauto.
  - (* tsig: the [tpi] argument verbatim *)
    destruct u; try done.
    move: E => [Vs [Vfs [Es1 [as0 [Es0 hs1]]]]].
    repeat split; eauto.
    exists as0.
    split. eapply IHM1; eauto.
    move=> ui vi Vui APP.
    destruct (hs1 _ _ Vui APP) as [x [Le [WT2 E2]]].
    have Vx: valid x. eapply wt_valid_tm; eauto.
    exists x.
    repeat split; eauto.
    eauto using valid_cons, SubRel_lift.
  - (* mkpair: componentwise, as [tid] *)
    destruct u; try done.
    move: E => [Vp [Ep1 Ep2]].
    split; [ exact Vp | ].
    split; [ eapply IHM1; eauto | eapply IHM2; eauto ].
  - (* pfst *)
    destruct (is_bot u); try done.
    move: E => [y Ey]. exists y. eapply IHM; eauto.
  - (* psnd *)
    destruct (is_bot u); try done.
    move: E => [x Ex]. exists x. eapply IHM; eauto.
Qed.

(** Single-variable specialization: an approximation [u] of body [B] in an
    environment extended by an approximation [v] of [M] is an approximation of
    the one-point substitution [B[M..]]. *)
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


(* EvalRel_Pi_app_type: from EvalRel of a (Core.tpi A B) at semantic
   (tpi b f), the codomain B[N..] evaluates to the appropriate element
   of f for any compatible N.

   Statement mirrors Agda EvalRel-Pi-app-type:
     EvalRel (Core.tpi A B) ρ (tpi b f) →
     valid u → app f u = Some v → ¬ is_bot v → wt u b →
     EvalRel B[N..] ρ v
   where N evaluates appropriately to u in ρ.
   The exact phrasing depends on how we connect the syntactic substitution
   B[N..] with the semantic-function image (EvalFun f u). *)
Lemma EvalRel_Pi_app_type {n} (A : Tm n) (B : Tm (S n)) (ρ : Env n)
  (b : elt) (f : list (elt * elt)) :
  EvalRel (Core.tpi A B) ρ (tpi b f) ->
  valid_env ρ ->
  forall u v,
    valid u -> app f u = v -> ~ is_bot v ->
    forall N, EvalRel N ρ u ->
    EvalRel B[N..] ρ v.
Proof.
  move=> h Vρ u v Vu APP _ N ER.
  cbn in h.
  move: h => [_ [_ [_ [a' [_ EFun]]]]].
  move: (EFun u v Vu APP) => [x [wtx [Lex EB]]].
  have Vx : valid x by eapply wt_valid_tm; eauto.
  have ER_x : EvalRel N ρ x by eapply EvalRel_down; eauto.
  eapply EvalRel_subst1_backwards; eauto.
Qed.




(** * MaxRel *)

(** [MaxSubRel σ ρ' ρ]: [ρ' i] is an upper bound of *every* approximation of
    [σ i] under [ρ].  This "maximal" variant supports the forward substitution
    lemma, where we need the realizing environment to dominate all approximants. *)
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

(** Forward substitution via a maximal realizer: under a [MaxSubRel], every
    approximation of [M[σ]] is already an approximation of [M] in the realizing
    environment. *)
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
  - (* ncase *)
    move: E => [w [EM Hb]]. exists w. split.
    + eapply IHM1; eauto.
    + destruct w as [ | | | | v | | | | | | | | ]; try contradiction.
      * exact Hb.
      * eapply IHM2; eauto.
      * have Vv : valid v := EvalRel_valid EM.
        eapply IHM3; [ | | | exact Hb ]; eauto using valid_cons, MaxSubRel_lift.
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
  - (* fix_: relabel the Kleene step through the IH *)
    move: E => [k HA]. exists k.
    eapply Approx_mon; [ | exact HA ].
    move=> p w Hst. eapply IHM; eauto.
  - (* tid: componentwise *)
    destruct u; try done.
    move: E => [V [EA [E0 E1]]].
    split; [ exact V | ].
    split; [ eapply IHM1; eauto | ].
    split; [ eapply IHM2; eauto | eapply IHM3; eauto ].
  - (* rfl *)
    destruct u; try done. eapply IHM; eauto.
  - (* jcase *)
    move: E => [w [EM Hb]]. exists w. split.
    + eapply IHM3; eauto.
    + destruct w as [ | | | | | | | | v | | | | ]; try contradiction.
      * exact Hb.
      * eapply IHM2; eauto.
  - (* tsig: the [tpi] argument verbatim *)
    destruct u; try done.
    move: E => [Vfs [Vus [Es1 [as0 [Es0 hs1]]]]].
    repeat split; eauto.
    exists as0. split. eauto.
    move=> ui vi Vui APP.
    destruct (hs1 _ _ Vui APP) as [x [Le [WT2 E2]]].
    have Vx: valid x. eapply wt_valid_tm; eauto.
    exists x.
    repeat split; eauto.
    eauto using valid_cons, MaxSubRel_lift.
  - (* mkpair: componentwise, as [tid] *)
    destruct u; try done.
    move: E => [Vp [Ep1 Ep2]].
    split; [ exact Vp | ].
    split; [ eapply IHM1; eauto | eapply IHM2; eauto ].
  - (* pfst *)
    destruct (is_bot u); try done.
    move: E => [y Ey]. exists y. eapply IHM; eauto.
  - (* psnd *)
    destruct (is_bot u); try done.
    move: E => [x Ex]. exists x. eapply IHM; eauto.
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

(** Goal of the forward direction for a given approximation [u] of [M[σ]]:
    exhibit a valid source environment [ρ'] realized by [σ] under [ρ] in which
    [u] already approximates [M]. *)
Definition FwdResult {h g} (σ : Sub h g) (M : Tm h) (ρ : Env g) (u : elt) : Prop :=
  exists ρ', valid_env ρ' /\ SubRel σ ρ' ρ /\ EvalRel M ρ' u.

(** ** Fold over edge list to combine per-edge witness environments

    Given a list of edges, with for each (u,v) ∈ gs an x and a source-env
    witness ρ_uv such that EvalRel M (x .: ρ_uv) v with le x u and wt x a,
    build a single source env ρ' ≥ acc supporting all edges. *)

Lemma fold_edge_fwd {h g} (σ : Sub h g) (ρ : Env g)
  (M : Tm (S h)) (a : elt) :
  forall (gs : list (elt * elt)) (acc : Env h),
    valid_fun gs ->
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
  induction gs as [|[u0 v0] gs' IH].
  - (* gs = [] : app [] u = bot *)
    move=> acc VF Vρ Vacc SRacc body.
    exists acc. split; [exact Vacc | split; [exact SRacc | split]].
    + by apply le_env_refl.
    + move=> u v Vu APP.
      rewrite app_nil_eq in APP. subst v.
      move: (body u bot Vu (app_nil_eq u)) => [x [Wtx [ρ_uv [Lx _]]]].
      exists x, Wtx. split; [exact Lx | apply EvalRel_bot].
  - (* gs = (u0,v0) :: gs' *)
    move=> acc VF Vρ Vacc SRacc body.
    have Vft : valid_fun gs' := valid_fun_tail VF.
    have [Vu0 Vv0 _ COH] := valid_fun_head VF.
    (* tail body: app gs' u <= app ((u0,v0)::gs') u, so transport the witness *)
    have body' : forall u w, valid u -> app gs' u = w ->
       exists x (hh : wt x a) ρ_uv, le x u /\ valid_env ρ_uv /\
         SubRel σ ρ_uv ρ /\ EvalRel M (x .: ρ_uv) w.
    { move=> u w Vu APP.
      move: (body u (app ((u0,v0)::gs') u) Vu erefl)
        => [x [Wtx [ρ_uv [Lx [Vρuv [SRρuv ER]]]]]].
      exists x, Wtx, ρ_uv. split; [exact Lx | split; [exact Vρuv | split; [exact SRρuv |]]].
      eapply EvalRel_down;
        [ apply valid_cons; [ exact (wt_valid_tm Wtx) | exact Vρuv ]
        | rewrite -APP; apply valid_app; [ exact Vft | exact Vu ]
        | exact ER | ].
      rewrite -APP app_cons_eq.
      destruct (le u0 u) eqn:Hle.
      - apply le_lub_right.
        + apply compatible_app. apply/forallb_forall. move=> [ui vi] Hin.
          apply/implyP => Hleui.
          move: COH => /forallb_forall /(_ (ui,vi) Hin) /implyP HC. apply HC.
          eapply le_compatible_pair; [exact Vu | exact Hle | exact Hleui].
        + exact Vv0.
        + apply valid_app; [exact Vft | exact Vu].
      - apply le_refl. apply valid_app; [exact Vft | exact Vu]. }
    (* recurse on the tail *)
    move: (IH acc Vft Vρ Vacc SRacc body')
      => [ρt [Vρt [SRρt [LEρt bodyAllt]]]].
    (* head witness at the key u0 *)
    have Hle00 : le u0 u0 := le_refl Vu0.
    have COMP00 : compatible v0 (app gs' u0).
    { apply compatible_app. apply/forallb_forall. move=> [ui vi] Hin.
      apply/implyP => Hleui.
      move: COH => /forallb_forall /(_ (ui,vi) Hin) /implyP HC. apply HC.
      apply compatible_sym. eapply le_compatible; [exact Vu0 | exact Hleui]. }
    have Vapp0 : valid (app gs' u0) := valid_app Vft Vu0.
    move: (body u0 (app ((u0,v0)::gs') u0) Vu0 erefl)
      => [x0 [Wtx0 [ρ0 [Lx0 [Vρ0 [SRρ0 ER0]]]]]].
    have ER0v : EvalRel M (x0 .: ρ0) v0.
    { eapply EvalRel_down;
        [ apply valid_cons; [ exact (wt_valid_tm Wtx0) | exact Vρ0 ]
        | exact Vv0 | exact ER0
        | rewrite app_cons_eq Hle00; exact (le_lub_left COMP00 Vv0 Vapp0) ]. }
    (* combine the head env with the tail env *)
    move: (@combine_fwd _ _ σ ρ ρ0 ρt Vρ Vρ0 Vρt SRρ0 SRρt)
      => [ρ' [Vρ' [SRρ' [LE0 LEt]]]].
    exists ρ'. split; [exact Vρ' | split; [exact SRρ' | split]].
    + exact (le_env_trans Vacc Vρt Vρ' LEρt LEt).
    + move=> u v Vu APP.
      have Vappu : valid (app gs' u) := valid_app Vft Vu.
      move: (bodyAllt u (app gs' u) Vu erefl) => [xt [Wtxt [Lxt ERt]]].
      have Vxt : valid xt := wt_valid_tm Wtxt.
      destruct (le u0 u) eqn:Hle.
      * (* le u0 u : app ((u0,v0)::gs') u = lub v0 (app gs' u) *)
        have Vx0 : valid x0 := wt_valid_tm Wtx0.
        have Lx0u : le x0 u := le_trans Vx0 Vu0 Vu Lx0 Hle.
        have Cx0xt : compatible x0 xt.
        { eapply le_compatible_pair; [exact Vu | exact Lx0u | exact Lxt]. }
        have Vlub : valid (lub x0 xt) := valid_lub Cx0xt Vx0 Vxt.
        have WTlub : wt (lub x0 xt) a := wt_lub Wtx0 Cx0xt Wtxt.
        exists (lub x0 xt), WTlub.
        split; [ exact (le_sup_lub Lx0u Lxt) |].
        have E_v0 : EvalRel M (lub x0 xt .: ρ') v0.
        { eapply EvalRel_mono_env;
            [ exact ER0v
            | apply valid_cons; [exact Vx0 | exact Vρ0]
            | apply valid_cons; [exact Vlub | exact Vρ']
            | apply le_env_cons; [ exact (le_lub_left Cx0xt Vx0 Vxt) | exact LE0 ] ]. }
        have E_t : EvalRel M (lub x0 xt .: ρ') (app gs' u).
        { eapply EvalRel_mono_env;
            [ exact ERt
            | apply valid_cons; [exact Vxt | exact Vρt]
            | apply valid_cons; [exact Vlub | exact Vρ']
            | apply le_env_cons; [ exact (le_lub_right Cx0xt Vx0 Vxt) | exact LEt ] ]. }
        move: (EvalRel_compatible_lub (valid_cons Vlub Vρ') E_v0 E_t) => [_ hlub].
        rewrite -APP app_cons_eq Hle. apply hlub. reflexivity.
      * (* ~ le u0 u : app ((u0,v0)::gs') u = app gs' u *)
        exists xt, Wtxt. split; [exact Lxt |].
        rewrite -APP app_cons_eq Hle.
        eapply EvalRel_mono_env;
          [ exact ERt
          | apply valid_cons; [exact Vxt | exact Vρt]
          | apply valid_cons; [exact Vxt | exact Vρ']
          | apply le_env_cons; [ apply le_refl; exact Vxt | exact LEt ] ].
Qed.

(** ** Main forward witness lemma *)

(** The forward substitution theorem, in witness form: every approximation of
    [M[σ]] is reflected back to [M] under some source environment realized by
    [σ] (i.e. [FwdResult] holds).  Proven by induction on [M]; the function
    cases consume [fold_edge_fwd] to assemble a single witness environment from
    the per-edge ones. *)
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
    destruct u as [| | | | | |l| | | | | | ].
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

    move: (@fold_edge_fwd _ _ σ ρ M2 a l ρA Vf Vρ VρA SRρA body')
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
  - (* ncase — forward witness for case, assembled from the selected branch *)
    move: E => [w [EM Hb]].
    destruct w as [ | | | | v | | | | | | | | ]; cbn in Hb; try contradiction.
    + (* bot: u = bot *)
      move: Hb => [_ Lu]. apply le_bot_inv in Lu; subst u.
      exists bot_env. split; [|split].
      * by apply bot_env_valid.
      * by apply SubRel_bot_env.
      * apply EvalRel_bot.
    + (* zero *)
      move: (IHM1 _ _ _ _ Vρ EM) => [ρ0 [V0 [SR0 E0]]].
      move: (IHM2 _ _ _ _ Vρ Hb) => [ρ1 [V1 [SR1 E1]]].
      move: (@combine_fwd _ _ σ ρ ρ0 ρ1 Vρ V0 V1 SR0 SR1)
        => [ρ' [Vρ' [SR' [LE0 LE1]]]].
      exists ρ'. split; [ exact Vρ' | split; [ exact SR' | ] ].
      cbn. exists zero. split.
      * eapply EvalRel_mono_env; [ exact E0 | exact V0 | exact Vρ' | exact LE0 ].
      * cbn. eapply EvalRel_mono_env; [ exact E1 | exact V1 | exact Vρ' | exact LE1 ].
    + (* succ v *)
      have Vv : valid v := EvalRel_valid EM.
      move: (IHM1 _ _ _ _ Vρ EM) => [ρ0 [V0 [SR0 E0]]].
      move: (IHM3 _ _ _ _ (valid_cons Vv Vρ) Hb) => [ρx [Vx [SRx Ex]]].
      pose ρ_uv := fun y => ρx (Some y).
      have Vρuv : valid_env ρ_uv by (move=> y; apply Vx).
      have SRtail : SubRel σ ρ_uv ρ by (eapply SubRel_lift_inv; eauto).
      move: (SubRel_lift_head SRx) => [Vp Lp].
      have Vsp : valid (succ (ρx var_zero)) := Vp.
      have Lsp : le (succ (ρx var_zero)) (succ v) by (rewrite le_succ; exact Lp).
      have Ep : EvalRel M1 ρ0 (succ (ρx var_zero)) := EvalRel_down V0 Vsp E0 Lsp.
      move: (@combine_fwd _ _ σ ρ ρ0 ρ_uv Vρ V0 Vρuv SR0 SRtail)
        => [ρ' [Vρ' [SR' [LE0 LEuv]]]].
      exists ρ'. split; [ exact Vρ' | split; [ exact SR' | ] ].
      cbn. exists (succ (ρx var_zero)). split.
      * eapply EvalRel_mono_env; [ exact Ep | exact V0 | exact Vρ' | exact LE0 ].
      * cbn.
        have V1' : valid_env ((ρx var_zero) .: ρ') := valid_cons Vp Vρ'.
        have LEx : le_env ρx ((ρx var_zero) .: ρ').
        { move=> [k|]; cbn.
          - exact (LEuv k).
          - apply le_refl; exact Vp. }
        exact (EvalRel_mono_env Ex Vx V1' LEx).
  - (* tnat *)
    exists bot_env. split; [|split].
    + by apply bot_env_valid.
    + by apply SubRel_bot_env.
    + cbn. exact E.
  - (* tpi *)
    destruct u as [| | | | |e l| | | | | | | ].
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
    move: (@fold_edge_fwd _ _ σ ρ M2 a0 l ρA1 Vf Vρ VρA1 SRρA1 body')
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
  - (* fix_: one witness environment for the whole approximant chain, by
       combining the per-step witnesses with [combine_fwd] *)
    move: E => [k HA].
    have gen : forall k0 u0,
        Approx (fun p w => EvalRel M[σ] ρ (p ↦ w)) k0 u0 ->
        exists ρ', valid_env ρ' /\ SubRel σ ρ' ρ /\
                   Approx (fun p w => EvalRel M ρ' (p ↦ w)) k0 u0.
    { move=> k0. induction k0 as [ | k0 IH ]; move=> u0 H.
      - exists bot_env. split; [ by apply bot_env_valid | ].
        split; [ by apply SubRel_bot_env | exact H ].
      - move: H => [p [Hp Hst]].
        move: (IH p Hp) => [ρ1 [V1 [S1 A1]]].
        move: (IHM _ σ ρ _ Vρ Hst) => [ρ2 [V2 [S2 E2]]].
        move: (combine_fwd Vρ V1 V2 S1 S2) => [ρ3 [V3 [S3 [L1 L2]]]].
        exists ρ3. split; [ exact V3 | split; [ exact S3 | ] ].
        exists p. split.
        + eapply Approx_mon; [ | exact A1 ].
          move=> q w Hq.
          eapply EvalRel_mono_env; [ exact Hq | exact V1 | exact V3 | exact L1 ].
        + eapply EvalRel_mono_env; [ exact E2 | exact V2 | exact V3 | exact L2 ]. }
    move: (gen k u HA) => [ρ' [V' [S' A']]].
    exists ρ'. split; [ exact V' | split; [ exact S' | exists k; exact A' ] ].
  - (* tid: three component witnesses, combined pairwise *)
    destruct u as [ | | | | | | | t v w | | | | | ].
    1:{ (* bot *) exists bot_env. split; [|split].
        - by apply bot_env_valid.
        - by apply SubRel_bot_env.
        - by cbn. }
    all: try (exfalso; cbn in E; done).
    move: E => [Vu [EA [E0 E1]]].
    move: (IHM1 _ _ _ _ Vρ EA) => [ρ1 [V1 [S1 F1]]].
    move: (IHM2 _ _ _ _ Vρ E0) => [ρ2 [V2 [S2 F2]]].
    move: (IHM3 _ _ _ _ Vρ E1) => [ρ3 [V3 [S3 F3]]].
    move: (combine_fwd Vρ V1 V2 S1 S2) => [ρ12 [V12 [S12 [L1 L2]]]].
    move: (combine_fwd Vρ V12 V3 S12 S3) => [ρ' [Vρ' [SR' [L12 L3]]]].
    exists ρ'. split; [ exact Vρ' | split; [ exact SR' | ] ].
    cbn. split; [ exact Vu | ].
    split.
    { eapply EvalRel_mono_env; [ exact F1 | exact V1 | exact Vρ' | ].
      eapply le_env_trans;
        [ exact V1 | exact V12 | exact Vρ' | exact L1 | exact L12 ]. }
    split.
    { eapply EvalRel_mono_env; [ exact F2 | exact V2 | exact Vρ' | ].
      eapply le_env_trans;
        [ exact V2 | exact V12 | exact Vρ' | exact L2 | exact L12 ]. }
    eapply EvalRel_mono_env; [ exact F3 | exact V3 | exact Vρ' | exact L3 ].
  - (* rfl: the witness of the witness *)
    destruct u as [ | | | | | | | | w | | | | ].
    1:{ exists bot_env. split; [|split].
        - by apply bot_env_valid.
        - by apply SubRel_bot_env.
        - by cbn. }
    all: try (exfalso; cbn in E; done).
    move: (IHM _ _ _ _ Vρ E) => [ρ' [Vρ' [SR' F]]].
    exists ρ'. split; [ exact Vρ' | split; [ exact SR' | exact F ] ].
  - (* jcase — forward witness, assembled from the scrutinee and the edge *)
    move: E => [w [EM Hb]].
    destruct w as [ | | | | | | | | v | | | | ]; cbn in Hb; try contradiction.
    + (* bot: u = bot *)
      move: Hb => [_ Lu]. apply le_bot_inv in Lu; subst u.
      exists bot_env. split; [|split].
      * by apply bot_env_valid.
      * by apply SubRel_bot_env.
      * apply EvalRel_bot.
    + (* rfl v: the branch is the edge [v ↦ u] of the base *)
      move: (IHM3 _ _ _ _ Vρ EM) => [ρ0 [V0 [SR0 E0]]].
      move: (IHM2 _ _ _ _ Vρ Hb) => [ρ1 [V1 [SR1 E1]]].
      move: (@combine_fwd _ _ σ ρ ρ0 ρ1 Vρ V0 V1 SR0 SR1)
        => [ρ' [Vρ' [SR' [LE0 LE1]]]].
      exists ρ'. split; [ exact Vρ' | split; [ exact SR' | ] ].
      cbn. exists (rfl v). split.
      * eapply EvalRel_mono_env; [ exact E0 | exact V0 | exact Vρ' | exact LE0 ].
      * cbn. eapply EvalRel_mono_env; [ exact E1 | exact V1 | exact Vρ' | exact LE1 ].
  - (* tsig: the [tpi] case verbatim -- same clause, same [fold_edge_fwd] *)
    destruct u as [| | | | | | | | |e l| | | ].
    1:{ (* bot *) exists bot_env. split; [|split].
        - by apply bot_env_valid.
        - by apply SubRel_bot_env.
        - by cbn. }
    all: try (exfalso; cbn in E; done).
    (* u = tsig e l *)
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
    move: (@fold_edge_fwd _ _ σ ρ M2 a0 l ρA1 Vf Vρ VρA1 SRρA1 body')
      => [ρ' [Vρ' [SRρ' [LEρ' bodyAll]]]].
    exists ρ'. split; [|split]; first done.
    { exact SRρ'. }
    cbn. repeat split; eauto. 
    eapply EvalRel_mono_env; eauto. eapply le_env_trans with (ρ2 := ρA1); eauto.
    exists a0. split.
    eapply EvalRel_mono_env; eauto.  eapply le_env_trans with (ρ2 := ρA1); eauto.
    exact bodyAll.
  - (* mkpair: two component witnesses, combined pairwise (as [tid]) *)
    destruct u as [ | | | | | | | | | | x y | | ].
    1:{ (* bot *) exists bot_env. split; [|split].
        - by apply bot_env_valid.
        - by apply SubRel_bot_env.
        - by cbn. }
    all: try (exfalso; cbn in E; done).
    move: E => [Vu [E1 E2]].
    move: (IHM1 _ _ _ _ Vρ E1) => [ρ1 [V1 [S1 F1]]].
    move: (IHM2 _ _ _ _ Vρ E2) => [ρ2 [V2 [S2 F2]]].
    move: (combine_fwd Vρ V1 V2 S1 S2) => [ρ' [Vρ' [SR' [L1 L2]]]].
    exists ρ'. split; [ exact Vρ' | split; [ exact SR' | ] ].
    cbn. split; [ exact Vu | ].
    split.
    { eapply EvalRel_mono_env; [ exact F1 | exact V1 | exact Vρ' | exact L1 ]. }
    eapply EvalRel_mono_env; [ exact F2 | exact V2 | exact Vρ' | exact L2 ].
  - (* pfst: one witness environment; the pair code is rebuilt around it *)
    destruct (is_bot u) eqn:Hb.
    { exists bot_env. split; [|split].
      - by apply bot_env_valid.
      - by apply SubRel_bot_env.
      - cbn. by rewrite Hb. }
    move: E => [y Ey].
    move: (IHM _ _ _ _ Vρ Ey) => [ρ' [Vρ' [SR' F]]].
    exists ρ'. split; [|split]; auto.
    cbn. rewrite Hb. by exists y.
  - (* psnd *)
    destruct (is_bot u) eqn:Hb.
    { exists bot_env. split; [|split].
      - by apply bot_env_valid.
      - by apply SubRel_bot_env.
      - cbn. by rewrite Hb. }
    move: E => [x Ex].
    move: (IHM _ _ _ _ Vρ Ex) => [ρ' [Vρ' [SR' F]]].
    exists ρ'. split; [|split]; auto.
    cbn. rewrite Hb. by exists x.
  - (* tprop: a code leaf, like [tuniv] *)
    exists bot_env. split; [|split].
    + by apply bot_env_valid.
    + by apply SubRel_bot_env.
    + cbn. exact E.
  - (* tunit: the unit type code, a leaf like [tuniv] *)
    exists bot_env. split; [|split].
    + by apply bot_env_valid.
    + by apply SubRel_bot_env.
    + cbn. exact E.
  - (* tstar: the unit element: [le b bot] forces [b = bot] *)
    exists bot_env. split; [|split].
    + by apply bot_env_valid.
    + by apply SubRel_bot_env.
    + cbn. exact E.
Qed.

(** ** EvalRel_subst1_forward as a corollary *)

(** Single-variable forward substitution: an approximation of [M[N..]] factors
    as some approximation [v] of [N] together with an approximation of the body
    [M] in the environment extended by [v].  This is the form used by the beta
    case of the validity/adequacy proofs. *)
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



(* ============================================================
   The motive spine of [J].

   [d : base_ty A C = tpi A (app (app (app C⟨↑⟩ 0) 0) (rfl 0))], so a value of
   [d]'s Π-codomain is a value of the motive [C] applied to *one* code three
   times over -- namely at codes below the selected argument [x].  The goal of
   the [J] driver instead needs the motive applied to [a], [b] and [p].

   They agree because of Coquand's membership rule: the proof's own value is an
   [rfl wmax] with [wmax] below **both** endpoint codes, so [a] and [b] both
   take [wmax], and every code below [x <= wmax] is therefore an approximation
   of [a], of [b], and (wrapped in [rfl]) of [p].  This is the [EvalRel]-level
   heart of the [J] case, shared by [InvTyp_J] (soundness) and [st_jcase]
   (adequacy).
   ============================================================ *)
(* The strengthened form, which also hands back the three spine codes together
   with the bounds that place them below the witness.  The adequacy driver needs
   those bounds: the witness's *reducible* equalities to the endpoints live at
   the witness's own code, so they can only be restricted to codes below it. *)
Lemma EvalRel_base_cod_spine_codes {n} (C a b p : Tm n) (ρ : Env n) x wmax c :
  valid_env ρ ->
  valid x ->
  le x wmax ->
  EvalRel a ρ wmax ->
  EvalRel b ρ wmax ->
  EvalRel p ρ (rfl wmax) ->
  is_bot c = false ->
  EvalRel (Core.app (Core.app (Core.app C⟨↑⟩ (Core.var var_zero))
                       (Core.var var_zero))
             (Core.rfl (Core.var var_zero))) (x .: ρ) c ->
  exists w1 w2 w3,
       EvalRel C ρ (w3 ↦ (w2 ↦ (w1 ↦ c)))
    /\ le w3 wmax /\ le w2 wmax /\ le w1 (rfl wmax)
    /\ EvalRel a ρ w3 /\ EvalRel b ρ w2 /\ EvalRel p ρ w1.
Proof.
  move=> Vρ Vx Lxw Eaw Ebw Epw Bc EB.
  have Vwmax : valid wmax by (move: (EvalRel_valid Epw); cbn; done).
  (* peel the three application edges off the codomain *)
  cbn [EvalRel] in EB. rewrite Bc in EB.
  move: EB => [w1 [EB1 Erf]].
  have NB1 : is_bot (w1 ↦ c) = false by (rewrite /singleton Bc).
  rewrite NB1 in EB1. move: EB1 => [w2 [EB2 Ev2]].
  have NB2 : is_bot (w2 ↦ (w1 ↦ c)) = false by (rewrite /singleton NB1).
  rewrite NB2 in EB2. move: EB2 => [w3 [EB3 Ev3]].
  cbn in Ev2, Ev3, Erf.
  exists w1, w2, w3.
  have G3 : EvalRel C ρ (w3 ↦ (w2 ↦ (w1 ↦ c)))
    by (eapply EvalRel_unwk; exact EB3).
  (* the three argument codes all sit below [x <= wmax] *)
  have [Vw3 Lw3] := Ev3. have [Vw2 Lw2] := Ev2.
  have L3 : le w3 wmax
    by (eapply (@le_trans w3 x wmax);
        [ exact Vw3 | exact Vx | exact Vwmax | exact Lw3 | exact Lxw ]).
  have L2 : le w2 wmax
    by (eapply (@le_trans w2 x wmax);
        [ exact Vw2 | exact Vx | exact Vwmax | exact Lw2 | exact Lxw ]).
  have [L1 Vw1] : le w1 (rfl wmax) /\ valid w1.
  { destruct w1 as [ | | | | | | | | w0 | | | | ]; try solve [ destruct Erf ].
    - (* the proof argument takes [bot] *) split; [ apply le_bot' | done ].
    - move: Erf => [Vw0 Lw0]. split.
      + apply le_rfl_intro. eapply (@le_trans w0 x wmax);
          [ exact Vw0 | exact Vx | exact Vwmax | exact Lw0 | exact Lxw ].
      + cbn; exact Vw0. }
  split; [ exact G3 | ].
  split; [ exact L3 | ]. split; [ exact L2 | ]. split; [ exact L1 | ].
  (* ... and are therefore approximations of [a], [b] and [p] *)
  split.
  { eapply EvalRel_down; [ exact Vρ | exact Vw3 | exact Eaw | exact L3 ]. }
  split.
  { eapply EvalRel_down; [ exact Vρ | exact Vw2 | exact Ebw | exact L2 ]. }
  eapply EvalRel_down; [ exact Vρ | exact Vw1 | exact Epw | exact L1 ].
Qed.

Lemma EvalRel_base_cod_spine {n} (C a b p : Tm n) (ρ : Env n) x wmax c :
  valid_env ρ ->
  valid x ->
  le x wmax ->
  EvalRel a ρ wmax ->
  EvalRel b ρ wmax ->
  EvalRel p ρ (rfl wmax) ->
  EvalRel (Core.app (Core.app (Core.app C⟨↑⟩ (Core.var var_zero))
                       (Core.var var_zero))
             (Core.rfl (Core.var var_zero))) (x .: ρ) c ->
  EvalRel (Core.app (Core.app (Core.app C a) b) p) ρ c.
Proof.
  move=> Vρ Vx Lxw Eaw Ebw Epw EB.
  destruct (is_bot c) eqn:Bc.
  { have Ec : c = bot by (destruct c; cbn in Bc; try discriminate; reflexivity).
    rewrite Ec. apply EvalRel_bot. }
  have [w1 [w2 [w3 [G3 [_ [_ [_ [Ga [Gb Gp]]]]]]]]] :=
    EvalRel_base_cod_spine_codes Vρ Vx Lxw Eaw Ebw Epw Bc EB.
  have NB1 : is_bot (w1 ↦ c) = false by (rewrite /singleton Bc).
  have NB2 : is_bot (w2 ↦ (w1 ↦ c)) = false by (rewrite /singleton NB1).
  have G2 : EvalRel (Core.app C a) ρ (w2 ↦ (w1 ↦ c)).
  { cbn [EvalRel]. rewrite NB2. exists w3. split; [ exact G3 | exact Ga ]. }
  have G1 : EvalRel (Core.app (Core.app C a) b) ρ (w1 ↦ c).
  { cbn [EvalRel]. rewrite NB1. exists w2. split; [ exact G2 | exact Gb ]. }
  cbn [EvalRel]. rewrite Bc. exists w1. split; [ exact G1 | exact Gp ].
Qed.
