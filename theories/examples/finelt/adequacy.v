(** * adequacy.v: Fundamental theorem and Π-injectivity

    (See [MIN/Adequacy/Bundle.agda] and [MIN/PiInjectivity.agda].)

    This file proves the *fundamental theorem* (adequacy) of the value PER from
    [raw_validity.v]: well-typed syntax is in the relation.  It is organized as
    one [semantic_typing]/[semantic_conv2] lemma per typing/conversion rule:
    - [st_var], [st_univ], [st_tpi], [st_abs], [st_app], [st_conv], … —
      the typing rules (Agda: [adequacyV2-*]);
    - [sc_refl], [sc_sym], [sc_trans], [sc_conv], [sc_app1], [sc_app2],
      [sc_beta], [sc_eta], [sc_tpi], [sc_abs] — the conversion rules
      (Agda: [adequacyE2-*]).

    [semantic_typing Γ M A] (≈ Agda [AdqV2]) bundles, for every substitution and
    every related member, the [Val] facts; [semantic_conv2] (≈ [AdqE2]) the
    [EqVal] facts.  The relations [ValSub]/[EqValSub] thread the logical
    relation through a substitution at *every fuel above the rank* — the Coq
    rendering of Agda's single canonical [Stage]; the cross-fuel bridges
    ([Val_fuel_any] etc.) move between such fuels.

    The headline application, assembled at the end, is [piInjectivity]: from a
    type conversion [tpi A0 B0 ≡ tpi A1 B1] the components are convertible
    ([piConv]), proven by evaluating both sides in the trivial (bottom)
    environment ([evalRel_Pi_trivial]). *)

(* Fundamental theorem of the logical relation *)


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
Require Import syntax.reduction.

Require Import findom.
Import Raw.
Require Import types.
Require Import raw_semantics.
Require Import typing_semantics.
Require Import raw_validity.
Require Import selection.
Require Import eval_substitution.

Open Scope subst_scope.
Import SubstNotations.
Import SyntaxNotations.
Import typing.Notations.



(* Fundamental theorem for the logical relation
   
   We want to show that well-typed terms are in the 
   relation.

   - If Γ |- M : A (typing) then


     if Γ |= ρ ~ σ  (ValSub)

          and  Γ |- σ  (typing_subst ctx_empty)

          and  Γ |= ρ  (fits)   


     for all u, a, such that h ∈ u : a   (wt)

        where [[M]]ρ = u  and [[A]]ρ = a  (EvalRel)

     we have

        Val u a M[σ] A[σ] h

   - If Γ |- M = N : A  (conv) 

     and  Γ |- σ1  Γ |- σ2 (typing_subst ctx_empty)

     and  Γ |= ρ  (fits)   

     and [[M]]ρ = u and [[N]]ρ = u and [[A]]ρ = a  (EvalRel)
 
     and h ∈ u : a   (wt)

     and Γ |= ρ ~ σ1 == σ2   (EqValSub)

     then

     EqVal u a M[σ1] N[σ2] A[σ] h
*)


(* A substitution: σ *)
Definition Sub m n := fin m -> Tm n.


(* A valid substitution σ maps every term in ρ to one that
   can be interpreted in Δ. *)
(* Agda-aligned canonical-fuel design: the substitution relations assert
   [Val]/[EqVal] at every fuel [RB] ABOVE the ranks ([max (rk u) (rk a) < RB]).
   By the cross-fuel bridges this is equivalent to Agda's single canonical
   stage, but keeps the [forall RB] shape.  Crucially it makes the Pi/Lam
   codomain *edges* provable: an edge supplies its argument at one above-rank
   fuel, and [Val_fuel_any] then provides it at all above-rank fuels (as
   [ValSub_cons] needs) — every fuel in play stays above the rank, where
   fuel-stability applies. *)
(** [ValSub Δ Γ σ ρ] (≈ Agda [TySub]): the substitution [σ : Γ → Δ] is
    semantically well-typed against the environment [ρ].  For each variable [i]
    and each valid approximation [u <= ρ i] typed at the variable's evaluated
    type [a], the substituted term [σ i] is in [Val] at [u : a] — and at *every*
    fuel [RB] above the ranks, so codomain edges (which produce members at one
    above-rank fuel and need them at all) go through via [Val_fuel_any]. *)
Definition ValSub {n} (Δ : Ctx n) {g} (Γ : Ctx g) (σ : Sub g n) (ρ : Env g)    : Prop :=
  forall i u, valid u -> le u (ρ i) ->
    forall a, EvalRel (lookup i Γ) ρ a ->
    forall (h : wt u a) RB, max (rk u) (rk a) < RB ->
      Val RB Δ (σ i) (lookup i Γ)[σ] h.

Lemma ValSub_empty {g} (Δ : Ctx g)(σ : Sub 0 g) :
  ValSub Δ ctx_empty σ null.
unfold ValSub. done. Qed.

Lemma ValSub_cons {g} (Γ : Ctx g) (ρ : Env g) {h} (Δ : Ctx h) (σ : Sub g h) (A: Tm g) v (M : Tm h):
    (forall u, valid u -> le u v -> forall a (h : wt u a),
    EvalRel A ρ a ->
    forall RB, max (rk u) (rk a) < RB -> Val RB Δ M A[σ] h) ->
    ValSub Δ Γ σ ρ ->
    ValSub Δ (Γ ++ A) (M .: σ) (v .: ρ).
Proof.
  intros hyp0 VS.
  unfold ValSub in *.
  move=> i u0 Vu0 Le0 a0 E0 WT0 RB Hrank.
  destruct i as [i|].
  - (* succ case *)
    cbn in *. asimpl.
    apply EvalRel_unwk in E0.
    specialize (VS i u0 Vu0 Le0 a0 E0 WT0 RB Hrank).
    rewrite renSubst_Tm. asimpl.
    done.
  - (* zero case *)
    cbn in *. asimpl.
    eapply EvalRel_unwk in E0; auto.
    rewrite renSubst_Tm. asimpl.
    eapply hyp0; eauto.
Qed.

(** [EqValSub Δ Γ σ1 σ2 ρ] (≈ Agda [TyConvSub]): the binary companion of
    [ValSub] — two substitutions [σ1], [σ2] act equally (in [EqVal]) on every
    member realized by [ρ], again at every above-rank fuel. *)
Definition EqValSub {h} {g} (Δ : Ctx h) (Γ : Ctx g)
  (σ1 : Sub g h) (σ2 : Sub g h) (ρ : Env g) : Prop :=
  forall i,
  forall u, valid u -> le u (ρ i) ->
    forall a, EvalRel (lookup i Γ) ρ a ->
    forall (h : wt u a) RB, max (rk u) (rk a) < RB ->
      EqVal RB Δ (σ1 i) (σ2 i) (lookup i Γ)[σ1] h.

  
Lemma EqValSub_empty {g} (Δ : Ctx g)(σ1 σ2 : Sub 0 g) :
   EqValSub Δ ctx_empty  σ1 σ2 null.
unfold EqValSub. done. Qed.

Lemma EqValSub_cons {h} {g} (Δ : Ctx h) (Γ : Ctx g) (ρ : Env g)
  (σ1 σ2 : Sub g h) A v (M1 M2 : Tm h):
    (forall u, valid u -> le u v -> forall a (h : wt u a),
    EvalRel A ρ a ->
    forall RB, max (rk u) (rk a) < RB -> EqVal RB Δ M1 M2 A[σ1] h) ->
    EqValSub Δ Γ σ1 σ2 ρ ->
    EqValSub Δ (Γ ++ A)  (M1 .: σ1) (M2 .: σ2) (v .: ρ).
Proof.
  intros hyp0 VS.
  unfold EqValSub in *.
  move=> i u0 Vu0 Le0 a0 E0 WT0 RB Hrank.
  destruct i as [i|].
  - (* succ case *)
    cbn in *. asimpl.
    rewrite renSubst_Tm. asimpl.
    apply EvalRel_unwk in E0.
    eapply VS; eauto.
  - (* zero case *)
    cbn in *. asimpl.
    rewrite renSubst_Tm. asimpl.
    apply EvalRel_unwk in E0.
    eapply hyp0; eauto.
Qed.


(* Syntactic pointwise conv between substitutions.  Mirrors Agda's
   WtConvSub: σ and σ' are conv at every variable, in the target context Δ.
   Together with subst_conv_cross, this lets us derive conv Δ M[σ] M[σ'] A[σ]
   from typing Γ M A — the syntactic counterpart of EqValSub.                *)
Definition ConvSub {h} {g} (Δ : Ctx h) (Γ : Ctx g)
  (σ1 σ2 : Sub g h) : Prop :=
  forall i, conv Δ (σ1 i) (σ2 i) (lookup i Γ)[σ1].

Lemma ConvSub_empty {h} (Δ : Ctx h)(σ1 σ2 : Sub 0 h) :
  ConvSub Δ ctx_empty σ1 σ2.
Proof. unfold ConvSub. by case. Qed.

Lemma ConvSub_refl {h} {g} (Δ : Ctx h) (Γ : Ctx g) (σ : Sub g h) :
  typing_subst Δ σ Γ -> ConvSub Δ Γ σ σ.
Proof.
  move=> TS i. eapply c_refl; eauto.
Qed.



Lemma ConvSub_cons {h} {g} (Δ : Ctx h) (Γ : Ctx g) (σ1 σ2 : Sub g h)
  (A : Tm g) (M1 M2 : Tm h) :
  conv Δ M1 M2 A[σ1] ->
  ConvSub Δ Γ σ1 σ2 ->
  ConvSub Δ (Γ ++ A) (M1 .: σ1) (M2 .: σ2).
Proof.
  move=> hM hC [i|]; cbn; asimpl.
  - move: (hC i). asimpl. done.
  - asimpl. done.
Qed.

Lemma ConvSub_id {n} (Γ : Ctx n) :
  ctx Γ -> ConvSub Γ Γ var var.
Proof.
  move=> CΓ i. asimpl. eapply c_refl; eauto.
  apply: t_var. exact CΓ.
Qed.

(* Lift a [ConvSub] under a new domain binder [A]: mirrors [typing_subst_lift],
   weakening each component conversion by [↑] ([renaming_conv]); the new
   variable is [c_refl]. *)
Lemma ConvSub_lift {h} {g} (Δ : Ctx h) (Γ : Ctx g) (σ σ' : Sub g h) (A : Tm g) :
  ctx (Δ ++ A[σ]) ->
  typing_subst Δ σ Γ ->
  ConvSub Δ Γ σ σ' ->
  ConvSub (Δ ++ A[σ]) (Γ ++ A) (⇑ σ) (⇑ σ').
Proof.
  move=> EC TS CS. intro x. destruct x.
  - (* succ: weaken the component conv by [↑] *)
    cbn. specialize (CS f).
    eapply renaming_conv with (Δ := Δ ++ A[σ]) in CS; eauto with renaming.
    asimpl in CS. asimpl. exact CS.
  - (* zero: the new variable, by reflexivity *)
    cbn. eapply c_refl. eapply t_var'; eauto. cbn. asimpl. done.
Qed.

(* Lift the second substitution [σ'] into the *[σ]*-extended context
   [Δ ++ A[σ]] (rather than [Δ ++ A[σ']]): the new variable is retyped from
   [A[σ]⟨↑⟩] to [A[σ']⟨↑⟩] via the domain conversion [A[σ] ≡ A[σ']]. *)
Lemma typing_subst_lift_conv {h} {g} (Δ : Ctx h) (Γ : Ctx g) (σ σ' : Sub g h) (A : Tm g) :
  ctx (Δ ++ A[σ]) ->
  typing_subst Δ σ' Γ ->
  conv Δ A[σ] A[σ'] Core.tuniv ->
  typing_subst (Δ ++ A[σ]) (⇑ σ') (Γ ++ A).
Proof.
  move=> EC TS' Hconv. intro x. destruct x.
  - (* succ: weaken the component typing by [↑] *)
    cbn. specialize (TS' f).
    eapply renaming_typing with (Δ := Δ ++ A[σ]) in TS'; eauto with renaming.
    asimpl in TS'. asimpl. exact TS'.
  - (* zero: [var 0 : A[σ]⟨↑⟩] retyped to [A[σ']⟨↑⟩] *)
    cbn. eapply t_conv with (A := A[σ]⟨↑⟩).
    + eapply t_var'; eauto.
    + asimpl.
      eapply renaming_conv with (Δ := Δ ++ A[σ]) in Hconv; eauto with renaming.
      asimpl in Hconv. exact Hconv.
Qed.

(* Cross-substitution conv: if M is typed at A in Γ, and σ ≈ σ' pointwise
   (both as ConvSub and well-typed), then M[σ] is conv to M[σ'] at A[σ].
   This is the syntactic analog of EqValSub's effect at any well-typed M.
   Proof would go by induction on typing — admitted here, to be developed
   alongside the other syntactic substitution lemmas. *)
Fixpoint subst_conv_cross {n} (Γ : Ctx n) (M A : Tm n) (h : typing Γ M A) {struct h} :
  forall m (Δ : Ctx m) (σ σ' : Sub n m),
    ctx Δ ->
    typing_subst Δ σ Γ ->
    typing_subst Δ σ' Γ ->
    ConvSub Δ Γ σ σ' ->
    conv Δ M[σ] M[σ'] A[σ].
Proof.
  destruct h as
    [ n0 Γ0 x cv                          (* t_var *)
    | n0 Γ0 M0 A0 B0 hM cAB               (* t_conv *)
    | n0 Γ0 A0 B0 N0 hA hB hN             (* t_abs *)
    | n0 Γ0 A0 B0 N0 M0 hA hB hN hM       (* t_app *)
    | n0 Γ0 cv                            (* t_nat *)
    | n0 Γ0 cv                            (* t_zero *)
    | n0 Γ0 M0 hM                         (* t_succ *)
    | n0 Γ0 T0 Mc Mc0 Mc1 hTc hMc hMc0 hMc1 (* t_case *)
    | n0 Γ0 A0 B0 hA hB                   (* t_tpi *)
    | n0 Γ0 cv ];                         (* t_univ *)
  move=> m Δ σ σ' CΔ TS TS' CS.
  - (* t_var *) cbn. exact (CS x).
  - (* t_conv *)
    eapply c_conv.
    + exact (subst_conv_cross _ _ _ _ hM m Δ σ σ' CΔ TS TS' CS).
    + eapply substitution_conv with (A := Core.tuniv); eauto.
  - (* t_abs *)
    have CAσ : typing Δ A0[σ] Core.tuniv
      by (eapply substitution_tm with (A := Core.tuniv); eauto).
    have ECA : ctx (Δ ++ A0[σ]) by (eapply c_cons; [ exact CΔ | exact CAσ ]).
    have convA : conv Δ A0[σ] A0[σ'] Core.tuniv
      := subst_conv_cross _ _ _ _ hA m Δ σ σ' CΔ TS TS' CS.
    have TSl : typing_subst (Δ ++ A0[σ]) (⇑ σ) (Γ0 ++ A0)
      by (eapply typing_subst_lift; eauto).
    have TSl' : typing_subst (Δ ++ A0[σ]) (⇑ σ') (Γ0 ++ A0)
      by (eapply typing_subst_lift_conv; eauto).
    have CSl : ConvSub (Δ ++ A0[σ]) (Γ0 ++ A0) (⇑ σ) (⇑ σ')
      by (eapply ConvSub_lift; eauto).
    have convN : conv (Δ ++ A0[σ]) N0[⇑ σ] N0[⇑ σ'] B0[⇑ σ]
      := subst_conv_cross _ _ _ _ hN _ (Δ ++ A0[σ]) (⇑ σ) (⇑ σ') ECA TSl TSl' CSl.
    have CAσ' : typing Δ A0[σ'] Core.tuniv
      by (eapply substitution_tm with (A := Core.tuniv); eauto).
    have TBσ : typing (Δ ++ A0[σ]) B0[⇑ σ] Core.tuniv
      by (eapply substitution_tm with (A := Core.tuniv); eauto).
    have TMσ : typing (Δ ++ A0[σ]) N0[⇑ σ] B0[⇑ σ]
      by (eapply substitution_tm with (A := B0); eauto).
    have TMσ'0 : typing (Δ ++ A0[σ]) N0[⇑ σ'] B0[⇑ σ']
      by (eapply substitution_tm with (A := B0); eauto).
    have convBB : conv (Δ ++ A0[σ]) B0[⇑ σ] B0[⇑ σ'] Core.tuniv
      := subst_conv_cross _ _ _ _ hB _ (Δ ++ A0[σ]) (⇑ σ) (⇑ σ') ECA TSl TSl' CSl.
    have TMσ' : typing (Δ ++ A0[σ]) N0[⇑ σ'] B0[⇑ σ]
      by (eapply t_conv; [ exact TMσ'0 | eapply c_sym; exact convBB ]).
    cbn. eapply c_abs;
      [ exact CAσ | exact CAσ' | exact TBσ | exact TMσ | exact TMσ' | exact convA | exact convN ].
  - (* t_app *)
    have CAσ : typing Δ A0[σ] Core.tuniv
      by (eapply substitution_tm with (A := Core.tuniv); eauto).
    have ECA : ctx (Δ ++ A0[σ]) by (eapply c_cons; [ exact CΔ | exact CAσ ]).
    have convA : conv Δ A0[σ] A0[σ'] Core.tuniv
      := subst_conv_cross _ _ _ _ hA m Δ σ σ' CΔ TS TS' CS.
    have TSl : typing_subst (Δ ++ A0[σ]) (⇑ σ) (Γ0 ++ A0)
      by (eapply typing_subst_lift; eauto).
    have TSl' : typing_subst (Δ ++ A0[σ]) (⇑ σ') (Γ0 ++ A0)
      by (eapply typing_subst_lift_conv; eauto).
    have CSl : ConvSub (Δ ++ A0[σ]) (Γ0 ++ A0) (⇑ σ) (⇑ σ')
      by (eapply ConvSub_lift; eauto).
    have convB : conv (Δ ++ A0[σ]) B0[⇑ σ] B0[⇑ σ'] Core.tuniv
      := subst_conv_cross _ _ _ _ hB _ (Δ ++ A0[σ]) (⇑ σ) (⇑ σ') ECA TSl TSl' CSl.
    have TBσ : typing (Δ ++ A0[σ]) B0[⇑ σ] Core.tuniv
      by (eapply substitution_tm with (A := Core.tuniv); eauto).
    have TMσ : typing Δ M0[σ] A0[σ]
      by (eapply substitution_tm with (A := A0); eauto).
    (* function [N0[σ']] retyped to the [σ]-domain Pi type *)
    have TNσ' : typing Δ N0[σ'] (Core.tpi A0[σ] B0[⇑ σ]).
    { eapply t_conv with (A := (Core.tpi A0 B0)[σ']).
      - eapply substitution_tm with (A := Core.tpi A0 B0); eauto.
      - cbn.
        have CAσ' : typing Δ A0[σ'] Core.tuniv
          by (eapply substitution_tm with (A := Core.tuniv); eauto).
        have ECAσ' : ctx (Δ ++ A0[σ']) by (eapply c_cons; [ exact CΔ | exact CAσ' ]).
        have TSlσ' : typing_subst (Δ ++ A0[σ']) (⇑ σ') (Γ0 ++ A0)
          by (eapply typing_subst_lift; [ exact ECAσ' | exact TS' ]).
        have TBσ' : typing (Δ ++ A0[σ']) B0[⇑ σ'] Core.tuniv
          by (eapply substitution_tm with (A := Core.tuniv); eauto).
        eapply c_sym. eapply c_tpi;
          [ exact CAσ | exact CAσ' | exact TBσ | exact TBσ' | exact convA | exact convB ]. }
    cbn.
    eapply c_trans with (N := Core.app N0[σ'] M0[σ]).
    + (* function variation, via [c_app1] *)
      rewrite subst1_subst_comm.
      eapply c_app1; [ exact CAσ | exact TBσ | | exact TMσ ].
      have := subst_conv_cross _ _ _ _ hN m Δ σ σ' CΔ TS TS' CS. cbn. by [].
    + (* argument variation, via [c_app2] *)
      rewrite subst1_subst_comm.
      eapply c_app2; [ exact CAσ | exact TBσ | exact TNσ' | ].
      exact (subst_conv_cross _ _ _ _ hM m Δ σ σ' CΔ TS TS' CS).
  - (* t_nat *) cbn. eapply c_refl. eapply t_nat. exact CΔ.
  - (* t_zero *) cbn. eapply c_refl. eapply t_zero. exact CΔ.
  - (* t_succ *)
    cbn. eapply c_succ.
    exact (subst_conv_cross _ _ _ _ hM m Δ σ σ' CΔ TS TS' CS).
  - (* t_case — substitution congruence for ncase, via c_ncase *)
    have convMc : conv Δ Mc[σ] Mc[σ'] Core.tnat
      := subst_conv_cross _ _ _ _ hMc m Δ σ σ' CΔ TS TS' CS.
    have convMc0 : conv Δ Mc0[σ] Mc0[σ'] (T0[Core.zero..])[σ]
      := subst_conv_cross _ _ _ _ hMc0 m Δ σ σ' CΔ TS TS' CS.
    have Ctn : ctx (Δ ++ Core.tnat)
      by (eapply c_cons; [ exact CΔ | eapply t_nat; exact CΔ ]).
    have convTn : conv Δ Core.tnat[σ] Core.tnat[σ'] Core.tuniv
      by (cbn; eapply c_refl; eapply t_nat; exact CΔ).
    have TSl : typing_subst (Δ ++ Core.tnat) (⇑ σ) (Γ0 ++ Core.tnat)
      by (eapply typing_subst_lift with (τ := Core.tnat); [ exact Ctn | exact TS ]).
    have TSl' : typing_subst (Δ ++ Core.tnat) (⇑ σ') (Γ0 ++ Core.tnat)
      by (eapply typing_subst_lift_conv with (A := Core.tnat);
            [ exact Ctn | exact TS' | exact convTn ]).
    have CSl : ConvSub (Δ ++ Core.tnat) (Γ0 ++ Core.tnat) (⇑ σ) (⇑ σ')
      by (eapply ConvSub_lift with (A := Core.tnat); [ exact Ctn | exact TS | exact CS ]).
    have TT : typing (Δ ++ Core.tnat) (T0[⇑ σ]) Core.tuniv
      by (eapply substitution_tm with (A := Core.tuniv); [ exact hTc | exact TSl | exact Ctn ]).
    have convMc1 : conv (Δ ++ Core.tnat) Mc1[⇑ σ] Mc1[⇑ σ'] (T0[rho])[⇑ σ]
      := subst_conv_cross _ _ _ _ hMc1 _ (Δ ++ Core.tnat) (⇑ σ) (⇑ σ') Ctn TSl TSl' CSl.
    cbn.
    have EQg : (T0[Mc..])[σ] = (T0[⇑ σ])[Mc[σ]..] by asimpl.
    rewrite EQg.
    eapply c_ncase; [ exact TT | exact convMc | | ].
    + have EQ0 : (T0[⇑ σ])[Core.zero..] = (T0[Core.zero..])[σ] by asimpl.
      rewrite EQ0; exact convMc0.
    + have EQ1 : (T0[⇑ σ])[rho] = (T0[rho])[⇑ σ].
      { unfold rho. asimpl. setoid_rewrite rinstInst'_Tm_pointwise. reflexivity. }
      rewrite EQ1; exact convMc1.
  - (* t_tpi *)
    have CAσ : typing Δ A0[σ] Core.tuniv
      by (eapply substitution_tm with (A := Core.tuniv); eauto).
    have ECA : ctx (Δ ++ A0[σ]) by (eapply c_cons; [ exact CΔ | exact CAσ ]).
    have convA : conv Δ A0[σ] A0[σ'] Core.tuniv
      := subst_conv_cross _ _ _ _ hA m Δ σ σ' CΔ TS TS' CS.
    have TSl : typing_subst (Δ ++ A0[σ]) (⇑ σ) (Γ0 ++ A0)
      by (eapply typing_subst_lift; eauto).
    have TSl' : typing_subst (Δ ++ A0[σ]) (⇑ σ') (Γ0 ++ A0)
      by (eapply typing_subst_lift_conv; eauto).
    have CSl : ConvSub (Δ ++ A0[σ]) (Γ0 ++ A0) (⇑ σ) (⇑ σ')
      by (eapply ConvSub_lift; eauto).
    have convB : conv (Δ ++ A0[σ]) B0[⇑ σ] B0[⇑ σ'] Core.tuniv
      := subst_conv_cross _ _ _ _ hB _ (Δ ++ A0[σ]) (⇑ σ) (⇑ σ') ECA TSl TSl' CSl.
    have TBσ : typing (Δ ++ A0[σ]) B0[⇑ σ] Core.tuniv
      by (eapply substitution_tm with (A := Core.tuniv); eauto).
    have CAσ' : typing Δ A0[σ'] Core.tuniv
      by (eapply substitution_tm with (A := Core.tuniv); eauto).
    have ECAσ' : ctx (Δ ++ A0[σ']) by (eapply c_cons; [ exact CΔ | exact CAσ' ]).
    have TSlσ' : typing_subst (Δ ++ A0[σ']) (⇑ σ') (Γ0 ++ A0)
      by (eapply typing_subst_lift; [ exact ECAσ' | exact TS' ]).
    have TBσ' : typing (Δ ++ A0[σ']) B0[⇑ σ'] Core.tuniv
      by (eapply substitution_tm with (A := Core.tuniv); eauto).
    cbn. eapply c_tpi;
      [ exact CAσ | exact CAσ' | exact TBσ | exact TBσ' | exact convA | exact convB ].
  - (* t_univ *) cbn. eapply c_refl. eapply t_univ. exact CΔ.
Qed.

(** [semantic_typing Γ M A] (≈ Agda [AdqV2]) bundles the two value results over
    a well-typed [M : A]: for any pair of related substitutions, [Val] at [M[σ]]
    (Agda [adequacySub2]) and [EqVal] at [M[σ]]/[M[σ']] (Agda
    [adequacyConvSub2]).  It takes [ValSub σ], [ValSub σ'] and [EqValSub σ σ']
    as separate hypotheses, at all above-rank fuels [RB]. *)
Definition semantic_typing {n} (Γ : Ctx n) (M : Tm n) (A : Tm n) :=
  forall ρ m (Δ : Ctx m) (σ σ': Sub n m) (TS : typing_subst Δ σ Γ)
    (TS' : typing_subst Δ σ' Γ)
    (CS : ConvSub Δ Γ σ σ')
    (F : fits Γ ρ)
    (VS : ValSub Δ Γ σ ρ)
    (VS' : ValSub Δ Γ σ' ρ)
    (EVS : EqValSub Δ Γ σ σ' ρ) (cΔ : ctx Δ),
  forall u a (WT : wt u a),
    EvalRel M ρ u ->
    EvalRel A ρ a ->
    (forall RB, max (rk u) (rk a) < RB -> Val RB Δ M[σ] A[σ] WT) /\
    (forall RB, max (rk u) (rk a) < RB -> EqVal RB Δ M[σ] M[σ'] A[σ] WT).

(** [semantic_conv2 Γ M N A] (≈ Agda [AdqE2] / [adequacyEqSub2]): from a
    conversion [M ≡ N : A], a *single* substitution [σ] gives [EqVal] at
    [M[σ]]/[N[σ]].  Using one substitution (rather than two) is what keeps
    [sc_sym]/[sc_trans] provable. *)
Definition semantic_conv2 {n} (Γ : Ctx n) (M N: Tm n) (A : Tm n) :=
  forall ρ m (Δ : Ctx m) (σ : Sub n m) (TS : typing_subst Δ σ Γ)
    (F : fits Γ ρ)
    (VS : ValSub Δ Γ σ ρ) (cΔ : ctx Δ),
  forall u a (WT : wt u a),
    EvalRel M ρ u ->
    EvalRel A ρ a ->
    (forall RB, max (rk u) (rk a) < RB -> EqVal RB Δ M[σ] N[σ] A[σ] WT).

Lemma EqValSub_ValSub_left {n} (Γ : Ctx n) ρ {m} (Δ : Ctx m) σ1 σ2 :
  EqValSub Δ Γ σ1 σ2 ρ ->
  ValSub Δ Γ σ1 ρ.
Proof.
  move=> EVS i u Vu LE a E1 h RB Hrank.
  specialize (EVS i u Vu LE a E1 h RB Hrank).
  eapply EqVal_Val1; eauto.
Qed.

Lemma ValSub_EqValSub {n} (Γ : Ctx n) ρ {m} (Δ : Ctx m) σ :
  ValSub Δ Γ σ ρ ->
    EqValSub Δ Γ σ σ ρ .
Proof.
  move=> VS.
  unfold EqValSub.
  move=> i u Vu LE a E1 h RB Hrank.
  specialize (VS i u Vu LE a E1 h RB Hrank).
  eapply Val_EqVal.
  auto.
Qed.




(* dom_transport: the domain-type transport (Agda [transportVal2']).  The
   argument [N], in the relation at the domain value [u'] (type code [b]), is in
   the relation at every smaller value [u''] AND every domain type code [a]
   (any [EvalRel A ρ a]).  PROVEN: the two domain codes [a], [b] are compatible
   (both evaluate the domain [A]), so route through their join [lub a b]; the
   join [ValTy] comes from the domain IH [STA] (domain-type adequacy at the
   join code, itself an evaluation of [A]); then [Val_app_transport] moves
   [(u',b) -> (u'',a)] at a high fuel and [Val_fuel_down_to] drops back to the
   target [RB].  This is exactly the [hyp0] premise of [ValSub_cons]. *)
Lemma dom_transport {g} (Γ : Ctx g) (A : Tm g) ρ {m} (Δ : Ctx m) (σ : Sub g m)
  (STA : semantic_typing Γ A Core.tuniv)
  (Fρ : fits Γ ρ) (TS : typing_subst Δ σ Γ) (VS : ValSub Δ Γ σ ρ) (CΔ : ctx Δ)
  (N : Tm m) b u' (WTu' : wt u' b) (evAdom : EvalRel A ρ b)
  (VN : forall RB, max (rk u') (rk b) < RB -> Val RB Δ N A[σ] WTu') :
  forall u'', valid u'' -> le u'' u' -> forall a (hh : wt u'' a),
    EvalRel A ρ a -> forall RB, max (rk u'') (rk a) < RB -> Val RB Δ N A[σ] hh.
Proof.
  move=> u'' Vu'' LEu a hh evAa RB Hrank.
  have Vρ : valid_env ρ := fits_valid_env Fρ.
  have Cab : compatible a b := EvalRel_compatible Vρ evAa evAdom.
  have ELub : EvalRel A ρ (lub a b) := proj2 (EvalRel_compatible_lub Vρ evAa evAdom) _ erefl.
  have Wb : wt b tuniv := wt_ty_tuniv WTu'.
  have Wa : wt a tuniv := wt_ty_tuniv hh.
  have hUc : wt (lub a b) tuniv := wt_lub Wa Cab Wb.
  have evU : EvalRel Core.tuniv ρ tuniv by (cbn; apply le_refl).
  pose RBh := S (max RB (max (max (rk u') (rk b)) (max (rk (lub a b)) (rk tuniv)))).
  have HhVN  : max (rk u') (rk b) < RBh by (unfold RBh; lia).
  have HhLub : max (rk (lub a b)) (rk tuniv) < RBh by (unfold RBh; lia).
  have HleR  : RB <= RBh by (unfold RBh; lia).
  have [valLub _] :=
    STA ρ m Δ σ σ TS TS (ConvSub_refl TS) Fρ VS VS (ValSub_EqValSub VS) CΔ
        (lub a b) tuniv hUc ELub evU.
  have VTc : Val RBh Δ A[σ] Core.tuniv hUc := valLub RBh HhLub.
  have Vtr : Val RBh Δ N A[σ] hh.
  { eapply (@Val_app_transport _ Δ N A[σ] u'' u' a b WTu' hh hUc);
      [ exact Cab | exact LEu | exact VTc | exact (VN RBh HhVN) ]. }
  eapply (@Val_fuel_down_to _ Δ N A[σ] u'' a hh RBh RB);
    [ exact HleR | lia | lia | exact Vtr ].
Qed.

(* dom_transport_eq: the [EqVal] analog of [dom_transport] (Agda's
   [transportEqVal2']).  PROVEN by the same route — route the two compatible
   domain codes [a]/[b] through their join [lub a b] with the join [ValTy] from
   the domain IH [STA], move [EqVal] via [EqVal_app_transport] at a high fuel,
   then [EqVal_fuel_down_to] back.  Matches the [hyp0] premise of
   [EqValSub_cons]. *)
Lemma dom_transport_eq {g} (Γ : Ctx g) (A : Tm g) ρ {m} (Δ : Ctx m) (σ : Sub g m)
  (STA : semantic_typing Γ A Core.tuniv)
  (Fρ : fits Γ ρ) (TS : typing_subst Δ σ Γ) (VS : ValSub Δ Γ σ ρ) (CΔ : ctx Δ)
  (N1 N2 : Tm m) b u' (WTu' : wt u' b) (evAdom : EvalRel A ρ b)
  (EV : forall RB, max (rk u') (rk b) < RB -> EqVal RB Δ N1 N2 A[σ] WTu') :
  forall u'', valid u'' -> le u'' u' -> forall a (hh : wt u'' a),
    EvalRel A ρ a -> forall RB, max (rk u'') (rk a) < RB -> EqVal RB Δ N1 N2 A[σ] hh.
Proof.
  move=> u'' Vu'' LEu a hh evAa RB Hrank.
  have Vρ : valid_env ρ := fits_valid_env Fρ.
  have Cab : compatible a b := EvalRel_compatible Vρ evAa evAdom.
  have ELub : EvalRel A ρ (lub a b) := proj2 (EvalRel_compatible_lub Vρ evAa evAdom) _ erefl.
  have Wb : wt b tuniv := wt_ty_tuniv WTu'.
  have Wa : wt a tuniv := wt_ty_tuniv hh.
  have hUc : wt (lub a b) tuniv := wt_lub Wa Cab Wb.
  have evU : EvalRel Core.tuniv ρ tuniv by (cbn; apply le_refl).
  pose RBh := S (max RB (max (max (rk u') (rk b)) (max (rk (lub a b)) (rk tuniv)))).
  have HhEV  : max (rk u') (rk b) < RBh by (unfold RBh; lia).
  have HhLub : max (rk (lub a b)) (rk tuniv) < RBh by (unfold RBh; lia).
  have HleR  : RB <= RBh by (unfold RBh; lia).
  have [valLub _] :=
    STA ρ m Δ σ σ TS TS (ConvSub_refl TS) Fρ VS VS (ValSub_EqValSub VS) CΔ
        (lub a b) tuniv hUc ELub evU.
  have VTc : Val RBh Δ A[σ] Core.tuniv hUc := valLub RBh HhLub.
  have Etr : EqVal RBh Δ N1 N2 A[σ] hh.
  { eapply (@EqVal_app_transport _ Δ N1 N2 A[σ] u'' u' a b WTu' hh hUc);
      [ exact Cab | exact LEu | exact VTc | exact (EV RBh HhEV) ]. }
  eapply (@EqVal_fuel_down_to _ Δ N1 N2 A[σ] u'' a hh RBh RB);
    [ exact HleR | lia | lia | exact Etr ].
Qed.


(* cod_subst_conv: the codomain-level instance of [subst_conv_cross] — a body
   [B] typed in [Γ++A] is convertible under the two lifted substitutions, in
   the extended target context [Δ++A[σ]].  A corollary of [subst_conv_cross]
   plus a [ConvSub] lift / context conversion; ADMITTED alongside the other
   syntactic substitution gaps. *)
Lemma cod_subst_conv {n} (Γ : Ctx n) (A : Tm n) (B : Tm (S n)) :
  typing Γ A Core.tuniv ->
  typing (Γ ++ A) B Core.tuniv ->
  forall m (Δ : Ctx m) (σ σ' : Sub n m),
    ctx Δ -> typing_subst Δ σ Γ -> typing_subst Δ σ' Γ -> ConvSub Δ Γ σ σ' ->
    conv (Δ ++ A[σ]) B[⇑ σ] B[⇑ σ'] Core.tuniv.
Proof.
  move=> TA TB m Δ σ σ' CΔ TS TS' CS.
  (* lift the substitutions/conversion into the extended context [Δ ++ A[σ]] *)
  have CAσ : typing Δ A[σ] Core.tuniv
    by (eapply substitution_tm with (A := Core.tuniv); eauto).
  have ECA : ctx (Δ ++ A[σ]) by (eapply c_cons; eauto).
  have convA : conv Δ A[σ] A[σ'] Core.tuniv := subst_conv_cross TA CΔ TS TS' CS.
  have TSl : typing_subst (Δ ++ A[σ]) (⇑ σ) (Γ ++ A) by (eapply typing_subst_lift; eauto).
  have TSl' : typing_subst (Δ ++ A[σ]) (⇑ σ') (Γ ++ A)
    by (eapply typing_subst_lift_conv; eauto).
  have CSl : ConvSub (Δ ++ A[σ]) (Γ ++ A) (⇑ σ) (⇑ σ') by (eapply ConvSub_lift; eauto).
  (* the codomain conversion is [subst_conv_cross] at the lifted substitution *)
  exact (subst_conv_cross TB ECA TSl TSl' CSl).
Qed.

(* codomain_type_ValTy: adequacy for the codomain *type* [B[N..]] — it is a
   valid type ([ValTy], i.e. [Val … tuniv]) at any of its semantic evaluations
   [c].  This is the [ValTy]-at-join input threaded into [st_app]'s
   [Val_app_transport] / [EqVal_app_transport] (with [c := lub a (app f u_sel)],
   the join of the two codomain evals, itself an evaluation by
   [EvalRel_compatible_lub]).  PROVEN from the App rule's own premise IHs
   [STB]/[STN]: split [N]'s value off the codomain evaluation
   ([EvalRel_subst1_forward]), type it by soundness ([typing_EvalRel]), extend
   the substitution at that value ([STN] + [dom_transport] + [ValSub_cons]),
   and apply the codomain IH [STB] at the extended substitution
   [(N[σ] .: σ)] — whose action on [B] is [B[N..][σ]] by [subst_cons_eq]. *)
Lemma codomain_type_ValTy {n} (Γ : Ctx n) (A : Tm n) (B : Tm (S n)) (N : Tm n)
  (TA : typing Γ A Core.tuniv) (TN : typing Γ N A)
  (STA : semantic_typing Γ A Core.tuniv)
  (STB : semantic_typing (Γ ++ A) B Core.tuniv)
  ρ {m} (Δ : Ctx m) (σ : Sub n m) c (hUc : wt c tuniv)
  (Fρ : fits Γ ρ) (TS : typing_subst Δ σ Γ) (VS : ValSub Δ Γ σ ρ) (CΔ : ctx Δ)
  (VNarg : forall v c0 (h : wt v c0), EvalRel N ρ v -> EvalRel A ρ c0 ->
            forall RB, max (rk v) (rk c0) < RB -> Val RB Δ N[σ] A[σ] h)
  (EC : EvalRel (B[N..]) ρ c) :
  forall RB, max (rk c) (rk tuniv) < RB -> Val RB Δ (B[⇑ σ][N[σ] .: var]) Core.tuniv hUc.
Proof.
  move=> RB HrC.
  have Vρ : valid_env ρ := fits_valid_env Fρ.
  have [vN [evN evBvN]] := EvalRel_subst1_forward Vρ EC.
  have VvN : valid vN := EvalRel_valid evN.
  (* type [N]'s value via soundness *)
  have IT : InvTyped Γ N A ρ. { apply typing_EvalRel. exact TN. exact Fρ. }
  have [vbig [abig [WTbig [LEvN [evNbig evAbig]]]]] := IT vN evN.
  have Vvbig : valid vbig := wt_valid_tm WTbig.
  (* lift the codomain evaluation to the enlarged env value *)
  have evBvbig : EvalRel B (vbig .: ρ) c.
  { eapply EvalRel_mono_env;
      [ exact evBvN | apply valid_cons; [ exact VvN | exact Vρ ]
      | apply valid_cons; [ exact Vvbig | exact Vρ ]
      | apply le_env_cons; [ exact LEvN | apply le_env_refl; exact Vρ ] ]. }
  (* extend the substitution at [N]'s value via the argument IH [STN] *)
  have TNσ : typing Δ N[σ] A[σ] by (eapply substitution_tm; [ exact TN | exact TS | exact CΔ ]).
  have valNbig : forall RB, max (rk vbig) (rk abig) < RB -> Val RB Δ N[σ] A[σ] WTbig
    by (move=> RB0 Hr0; exact (VNarg vbig abig WTbig evNbig evAbig RB0 Hr0)).
  have HYP0 := dom_transport (A := A) STA Fρ TS VS CΔ (ρ := ρ) (Δ := Δ) (σ := σ) (N := N[σ])
                 (b := abig) (u' := vbig) (WTu' := WTbig) evAbig valNbig.
  have VS1 : ValSub Δ (Γ ++ A) (N[σ] .: σ) (vbig .: ρ)
    by (eapply ValSub_cons; [ exact HYP0 | exact VS ]).
  have TS1 : typing_subst Δ (N[σ] .: σ) (Γ ++ A)
    by (eapply typing_subst_cons; [ exact TNσ | exact TS ]).
  have Fits : fits (Γ ++ A) (vbig .: ρ)
    by (eapply fits_cons; [ exact TA | exact evAbig | eapply wt_ty_tuniv; exact WTbig | exact WTbig | exact Fρ ]).
  have evU' : EvalRel Core.tuniv (vbig .: ρ) tuniv by (cbn; apply le_refl).
  (* apply the codomain IH at the extended substitution *)
  have [valB _] :=
    STB (vbig .: ρ) m Δ (N[σ] .: σ) (N[σ] .: σ) TS1 TS1 (ConvSub_refl TS1)
        Fits VS1 VS1 (ValSub_EqValSub VS1) CΔ c tuniv hUc evBvbig evU'.
  move: (valB RB HrC) => HvB.
  rewrite (subst_cons_eq B (N[σ]) σ) in HvB.
  exact HvB.
Qed.


(** ** Semantic typing/conversion rules (the fundamental theorem, rule by rule)

    Each [st_*] lemma below states that [semantic_typing] is closed under one
    typing rule (Agda [adequacyV2-*]); each [sc_*] that [semantic_conv2] is
    closed under one conversion rule (Agda [adequacyE2-*]).  Assembling them by
    induction over a derivation gives adequacy for the whole judgment. *)

(* ------------------ semantic typing rules ----------- *)

(* Scrutinee congruence for multi-step head reduction: reducing the scrutinee
   reduces the whole case expression.  Mirrors [HeadRed_app]; used by [st_case]
   to lift the scrutinee's reduction to numeral form up to the case redex. *)
Lemma HeadRed_ncase {n} (M M' M0 : Tm n) (M1 : Tm (S n)) :
  HeadRed M M' -> HeadRed (Core.ncase M M0 M1) (Core.ncase M' M0 M1).
Proof.
  intro h. induction h.
  - eapply ms_refl.
  - eapply ms_trans; [ eapply hr_case; eassumption | eassumption ].
Qed.

(* [zero] is a maximal-below-itself nat value: anything compatible with it is
   below it.  (Not true of [succ v]: [succ bot] and [succ zero] are compatible
   but unordered.  This is what makes the zero branch of [st_case] simpler than
   the successor branch.) *)
Lemma compatible_zero_le (v : elt) : compatible zero v -> le v zero.
Proof. destruct v; cbn; done. Qed.

(* Inversion of [le] at a successor: anything above [succ u] is a successor. *)
Lemma le_succ_inv (u v : elt) : le (succ u) v -> exists v', v = succ v' /\ le u v'.
Proof.
  destruct v as [ | | | | v' | | ]; try (autorewrite with le; done).
  move=> h. exists v'. split; [ reflexivity | ]. by rewrite le_succ in h.
Qed.

(* [Val] is trivial at the [bot] *type* code (the outer match of [Val] is on
   the type code). *)
Lemma Val_bot_ty {n} (Γ : Ctx n) (M A : Tm n) u (h : wt u bot) k :
  Val k Γ M A h.
Proof. destruct k as [ | k' ]; exact I. Qed.

Lemma EqVal_Bot_ty {n} (Γ : Ctx n) (M N A : Tm n) u (h : wt u bot) k :
  EqVal k Γ M N A h.
Proof. destruct k as [ | k' ]; exact I. Qed.

(* [rho] (the [succ (var 0)] shift used by the successor branch's motive)
   commutes with a lifted substitution.  Extracted from the inline [EQ1] of
   [tpi_PiEdgeEqTy_cross]. *)
Lemma rho_subst_comm {g mm} (T : Tm (S g)) (σ : Sub g mm) :
  (T[⇑ σ])[rho] = (T[rho])[⇑ σ].
Proof. unfold rho. asimpl. setoid_rewrite rinstInst'_Tm_pointwise. reflexivity. Qed.

(* Instantiating a [rho]-shifted motive: [rho] followed by [P .: σ] is
   [succ P .: σ].  This is what makes the successor branch's motive
   [(T[rho])[P .: σ]] equal to [T[(succ P) .: σ]]. *)
Lemma rho_subst_cons {g mm} (T : Tm (S g)) (P : Tm mm) (σ : Sub g mm) :
  (T[rho])[P .: σ] = T[(Core.succ P) .: σ].
Proof. unfold rho. asimpl. reflexivity. Qed.

(* Substituted domain/codomain typings, for the [c_beta]/[conv_subst_arg]
   plumbing of the lambda edges. *)
Lemma subst_dom_typing {g0} {Γ0 : Ctx g0} (A : Tm g0) {m0} {Δ0 : Ctx m0} (σ : Sub g0 m0) :
  typing Γ0 A Core.tuniv -> typing_subst Δ0 σ Γ0 -> ctx Δ0 ->
  typing Δ0 A[σ] Core.tuniv.
Proof.
  move=> TA TS CΔ.
  move: (substitution_tm _ A Core.tuniv _ σ TA TS CΔ) => hh. asimpl in hh. exact hh.
Qed.

Lemma subst_cod_typing {g0} {Γ0 : Ctx g0} (A : Tm g0) (B : Tm (S g0))
  {m0} {Δ0 : Ctx m0} (σ : Sub g0 m0) :
  typing Γ0 A Core.tuniv -> typing (Γ0 ++ A) B Core.tuniv ->
  typing_subst Δ0 σ Γ0 -> ctx Δ0 ->
  typing (Δ0 ++ A[σ]) B[⇑ σ] Core.tuniv.
Proof.
  move=> TA TB TS CΔ.
  have TAσ : typing Δ0 A[σ] Core.tuniv := ltac:(eapply subst_dom_typing; [ exact TA | exact TS | exact CΔ ]).
  have CΔA : ctx (Δ0 ++ A[σ]) by (eapply c_cons; [ exact CΔ | exact TAσ ]).
  have TSl : typing_subst (Δ0 ++ A[σ]) (⇑ σ) (Γ0 ++ A)
    by (eapply typing_subst_lift; [ exact CΔA | exact TS ]).
  move: (substitution_tm _ B Core.tuniv _ (⇑ σ) TB TSl CΔA) => hh.
  asimpl in hh. exact hh.
Qed.

(** The β step conversion that justifies head-expanding a [Val] across a
    lambda application: [app (abs Alam M)[σ] P ≡ M[⇑σ][P..] : B[⇑σ][P..]].
    This is the [Red3] step conversion Agda's [Val2-beta-expand] takes as an
    argument.  The lambda's annotation [Alam] need only be *convertible* to the
    Π-domain [A] — that is the generality the off-diagonal lambda edge
    ([sc_abs]) needs. *)
Lemma beta_step_conv {g0} {Γ0 : Ctx g0} (Alam A : Tm g0) (B M : Tm (S g0))
  {m0} {Δ0 : Ctx m0} (σ : Sub g0 m0) (P : Tm m0) :
  typing Γ0 Alam Core.tuniv ->
  typing Γ0 A Core.tuniv ->
  conv Γ0 A Alam Core.tuniv ->
  typing (Γ0 ++ A) B Core.tuniv ->
  typing (Γ0 ++ A) M B ->
  typing_subst Δ0 σ Γ0 -> ctx Δ0 -> typing Δ0 P A[σ] ->
  conv Δ0 (Core.app (Core.abs Alam M)[σ] P) (M[⇑ σ][P..]) (B[⇑ σ][P..]).
Proof.
  move=> TAlam TA CAAlam TB TM TS CΔ TP.
  have TAlamσ : typing Δ0 Alam[σ] Core.tuniv := ltac:(eapply subst_dom_typing; [ exact TAlam | exact TS | exact CΔ ]).
  have TAσ : typing Δ0 A[σ] Core.tuniv := ltac:(eapply subst_dom_typing; [ exact TA | exact TS | exact CΔ ]).
  have CAσ : conv Δ0 A[σ] Alam[σ] Core.tuniv.
  { move: (substitution_conv _ A Alam Core.tuniv _ σ CAAlam TS CΔ) => hh.
    asimpl in hh. exact hh. }
  have CΔA : ctx (Δ0 ++ A[σ]) by (eapply c_cons; [ exact CΔ | exact TAσ ]).
  have TSl : typing_subst (Δ0 ++ A[σ]) (⇑ σ) (Γ0 ++ A)
    by (eapply typing_subst_lift; [ exact CΔA | exact TS ]).
  have TBσ : typing (Δ0 ++ A[σ]) B[⇑ σ] Core.tuniv
    := ltac:(eapply subst_cod_typing; [ exact TA | exact TB | exact TS | exact CΔ ]).
  have TMσ : typing (Δ0 ++ A[σ]) M[⇑ σ] B[⇑ σ]
    := substitution_tm _ M B _ (⇑ σ) TM TSl CΔA.
  (* move the body/codomain into the *annotation's* context *)
  have TBσ' : typing (Δ0 ++ Alam[σ]) B[⇑ σ] Core.tuniv
    by (eapply ctx_conv_typing; [ exact CAσ | exact TBσ ]).
  have TMσ' : typing (Δ0 ++ Alam[σ]) M[⇑ σ] B[⇑ σ]
    by (eapply ctx_conv_typing; [ exact CAσ | exact TMσ ]).
  have TPl : typing Δ0 P Alam[σ] by (eapply t_conv; [ exact TP | exact CAσ ]).
  cbn.
  eapply c_beta; [ exact TAlamσ | exact TBσ' | exact TMσ' | exact TPl ].
Qed.

Section SemanticTyping.

Local Notation "Γ ⊨ M ∈ A" := (semantic_typing Γ M A).
Local Notation "Γ ⊨ M ≡ N ∈ A" := (semantic_conv2 Γ M N A).

Variable (n:nat) (Γ : Ctx n).

(** Variable rule (Agda [adequacyV2-var]): a variable is semantically typed at
    its declared type — read straight off the substitution relations. *)
Lemma st_var (x : fin n) :
  ctx Γ ->
(* ------------------------- *)
  (semantic_typing Γ (var x) (lookup x Γ)).
Proof.
  move=> h.
  move=> ρ m Δ σ σ' TS TS' CS FR VS VS' EVS CD u1 a1 WT1 Ex ER.
  cbn in *. move: Ex => [Vu1 Le1].
  split.
  - move=> RB. eapply (VS x); eauto.
  - move=> RB. eapply (EVS x); eauto.
Qed.

(** Conversion rule (Agda [adequacyV2-conv]): semantic typing transports along
    a semantic type conversion [A ≡ B]. *)
Lemma st_conv M A B :
  typing Γ M A ->
  conv Γ A B Core.tuniv ->
  semantic_typing Γ M A ->
  semantic_conv2 Γ A B Core.tuniv ->
(* ------------------------- *)
  semantic_typing Γ M B.
Proof.
  (* With the leaf-[forall RB] design, the codomain equality [EqValTy RB]
     is obtained from [EqVal (S RB)] (off-by-one [EqVal_EqValTy]) directly:
     [EqValSub] provides [EqVal] at *every* fuel, so [SCA] gives the type
     equality at [S RB] with no fuel-monotonicity step.  We then transport
     [Val M:A] -> [Val M:B] (resp. [EqVal]) via [Val_EqVal_fwd] /
     [EqVal_EqVal_fwd] at fuel [RB]. *)
  move=> TA CA STA SCA.
  move=> ρ m Δ s s' Ts Ts' CS Fρ VS VS' EVS CΔ u a WT evM evB.
  (* bridge EvalRel B ρ a -> EvalRel A ρ a *)
  move: (conv_EvalRel CA Fρ) => [_ [_ [_ bwd]]].
  have evA : EvalRel A ρ a by (apply bwd; exact evB).
  have WTa : wt a tuniv by (eapply wt_ty_tuniv; exact WT).
  have evU : EvalRel Core.tuniv ρ tuniv by [].
  have [valMA eqvalMA] := STA ρ _ Δ s s' Ts Ts' CS Fρ VS VS' EVS CΔ u a WT evM evA.
  have eqAB := SCA ρ _ Δ s Ts Fρ VS CΔ a tuniv WTa evA evU.
  (* the *syntactic* type conversion, substituted: [Val_EqVal_fwd] needs it to
     retype the [Red3] leaf conversions carried by [Val] at the [tnat] codes *)
  have cvABs : conv Δ A[s] B[s] Core.tuniv.
  { move: (substitution_conv _ A B Core.tuniv _ s CA Ts CΔ) => hh.
    asimpl in hh. exact hh. }
  asimpl. asimpl in valMA. asimpl in eqvalMA. asimpl in eqAB. asimpl in cvABs.
  split.
  - move=> RB Hrank. eapply Val_EqVal_fwd;
      [ cbn in Hrank; lia | cbn in Hrank; lia | exact cvABs | exact (valMA RB Hrank)
      | eapply EqVal_EqValTy; eapply (eqAB (S RB)); cbn in Hrank |- *; lia ].
  - move=> RB Hrank. eapply EqVal_EqVal_fwd;
      [ cbn in Hrank; lia | cbn in Hrank; lia | exact cvABs | exact (eqvalMA RB Hrank)
      | eapply EqVal_EqValTy; eapply (eqAB (S RB)); cbn in Hrank |- *; lia ].
Qed.


(** Application rule (Agda [adequacyV2-ty-App]): applying a semantically typed
    function to a semantically typed argument is semantically typed at the
    substituted codomain. *)
Lemma st_app A B N M :
  typing Γ A Core.tuniv ->
  typing (Γ ++ A) B Core.tuniv ->
  typing Γ M (Core.tpi A B) ->
  typing Γ N A  ->
  semantic_typing Γ A Core.tuniv -> 
  semantic_typing (Γ ++ A) B Core.tuniv -> 
  semantic_typing Γ M (Core.tpi A B) -> 
  semantic_typing Γ N A  -> 
(* ------------------------ *)
  semantic_typing Γ (Core.app M N) B[N..].
Proof.
  move=> TA TB TM TN STA STB STM STN.
  move=> ρ m Δ σ σ' TS TS' CS Fρ VS VS' EVS CΔ u a WT evMN evBN.
  have Vρ : valid_env ρ := fits_valid_env Fρ.
  split; move=> RB Hrank.
  - (* Val conjunct (adequacySub2-App) *)
    destruct (is_bot u) eqn:Hu.
    + (* result is bot: trivial *)
      have Eu : u = bot by apply is_bot_eq; rewrite Hu.
      subst u. apply Val_Bot.
    + (* informative: M evaluates to a singleton [v0 ↦ u] *)
      cbn in evMN. rewrite Hu in evMN.
      move: evMN => [v0 [evM_sing evN]].
      (* enlarge the function value to a well-typed one via soundness *)
      have IT : InvTyped Γ M (Core.tpi A B) ρ.
      { apply typing_EvalRel. exact TM. exact Fρ. }
      have [vbig [abig [WTbig [LEbig [evMbig evTpi]]]]] := IT (v0 ↦ u) evM_sing.
      (* the function value is an [abs g] (from [le (abs[(v0,u)]) vbig]) *)
      unfold singleton in LEbig. rewrite Hu in LEbig.
      have [g [Evbig LEfun]] := le_abs_inv LEbig. subst vbig.
      (* the function's type code must be a Pi [tpi b f] *)
      destruct abig as [ | | | | | b f | ];
        try solve [ exfalso; clear -WTbig; inversion WTbig ].
      (* domain/value-graph facts *)
      have evTpiC := evTpi. cbn in evTpiC. move: evTpiC => [Vb [Vf [evA_b _]]].
      have Vg : valid_fun g := proj1 (andb_prop _ _ (wt_valid_tm WTbig)).
      have Vv0 : valid v0 := EvalRel_valid evN.
      (* canonical selection of [g] below the argument value [v0] *)
      have [u_sel [v_sel [Sel [Le_usel Eq_vsel]]]] := selectionBelow Vg Vv0.
      have [WTu_sel WTv_sel] :
        wt u_sel b /\ wt v_sel (app f u_sel).
      { eapply wt_Selection_cod;
          [ exact (wt_abs_ty WTbig) | exact (wt_abs_inv1 WTbig)
          | move=> ui vi Hin; exact (wt_abs_inv2 WTbig Hin erefl)
          | exact Vg | exact Sel ]. }
      have Vusel : valid u_sel := wt_valid_tm WTu_sel.
      have evN_usel : EvalRel N ρ u_sel
        by (eapply EvalRel_down; [ exact Vρ | exact Vusel | exact evN | exact Le_usel ]).
      (* a working fuel [RBf] above the FUNCTION's rank (and the result rank):
         the value edge / function IH live at the function's rank, which the
         result-rank guard [Hrank] does not bound — so we run the edge at [RBf]
         and [Val_fuel_any] the result down to [RB]. *)
      pose RBf := S (max (max (rk (abs g)) (rk (tpi b f))) (max (rk u) (rk a))).
      have RKusel : rk u_sel <= rk_fun g := rk_Selection_key Sel.
      have RKb : rk b < rk (tpi b f) by (cbn; lia).
      have RKfg : rk_fun g < rk (abs g) by (cbn; lia).
      have HfM : max (rk (abs g)) (rk (tpi b f)) < S RBf by (unfold RBf; lia).
      have HfN : max (rk u_sel) (rk b) < RBf by (unfold RBf; lia).
      (* argument IH at the selection key *)
      have [valN _] :=
        STN ρ m Δ σ σ' TS TS' CS Fρ VS VS' EVS CΔ u_sel b WTu_sel evN_usel evA_b.
      (* function IH, exposing its value edge *)
      have [valMbig _] :=
        STM ρ m Δ σ σ' TS TS' CS Fρ VS VS' EVS CΔ (abs g) (tpi b f) WTbig evMbig evTpi.
      have TNσ : typing Δ N[σ] A[σ]
        by (eapply substitution_tm; [ exact TN | exact TS | exact CΔ ]).
      have VM := valMbig (S RBf) HfM. rewrite Val_abs in VM. move: VM => [_ VPi].
      move: VPi => [A0 [B0 [HRpi [CTpi [pav _]]]]].
      asimpl in HRpi.
      have [EA0 EB0] := HeadRed_tpi_eq HRpi. subst A0 B0.
      (* apply the value edge to the argument *)
      have Vapp := pav u_sel v_sel Sel WTu_sel N[σ] TNσ (valN RBf HfN).
      (* the edge codomain [app f u_sel] also evaluates [B[N..]] *)
      have evB_af : EvalRel B[N..] ρ (app f u_sel).
      { destruct (is_bot (app f u_sel)) eqn:Hbaf.
        - have -> : app f u_sel = bot by apply is_bot_eq; rewrite Hbaf. apply EvalRel_bot.
        - have NB : ~ is_bot (app f u_sel) by rewrite Hbaf.
          eapply EvalRel_Pi_app_type;
            [ exact evTpi | exact Vρ | exact Vusel | reflexivity | exact NB | exact evN_usel ]. }
      have Caaf : compatible a (app f u_sel)
        by (eapply EvalRel_compatible; [ exact Vρ | exact evBN | exact evB_af ]).
      (* the join [lub a (app f u_sel)] is itself an evaluation of [B[N..]] *)
      have ELub : EvalRel B[N..] ρ (lub a (app f u_sel))
        by (exact (proj2 (EvalRel_compatible_lub Vρ evBN evB_af) _ erefl)).
      (* [ValTy] at the join: codomain-type adequacy (the threaded input) *)
      have Waf : wt (app f u_sel) tuniv := wt_ty_tuniv (wt_Selection_abs WTbig Sel).
      have hUc : wt (lub a (app f u_sel)) tuniv := wt_lub (wt_ty_tuniv WT) Caaf Waf.
      have HrC : max (rk (lub a (app f u_sel))) (rk tuniv) < RBf.
      { have L1 := rk_lub a (app f u_sel). have L2 := rk_app f u_sel.
        have Hf : rk_fun f < rk (tpi b f) by (cbn; lia).
        have Htu : rk tuniv <= rk (tpi b f) by (cbn; lia).
        unfold RBf; lia. }
      have VNarg : forall v c0 (h : wt v c0), EvalRel N ρ v -> EvalRel A ρ c0 ->
          forall RB0, max (rk v) (rk c0) < RB0 -> Val RB0 Δ N[σ] A[σ] h
        by (move=> v c0 h ev ea;
            exact (proj1 (STN ρ m Δ σ σ TS TS (ConvSub_refl TS) Fρ VS VS (ValSub_EqValSub VS) CΔ v c0 h ev ea))).
      have VTc : Val RBf Δ (B[⇑ σ][N[σ] .: var]) Core.tuniv hUc
        by (eapply codomain_type_ValTy;
              [ exact TA | exact TN | exact STA | exact STB | exact Fρ | exact TS
              | exact VS | exact CΔ | exact VNarg | exact ELub | exact HrC ]).
      (* the result element [u] is below the selection value [v_sel] *)
      have LEu_vsel : le u v_sel.
      { rewrite le_fun_cons in LEfun.
        have LEua := proj1 (andb_prop _ _ LEfun).
        rewrite Eq_vsel in LEua. exact LEua. }
      (* drop from the function-rank fuel [RBf] down to the result fuel [RB] *)
      apply (Val_fuel_any (k := RBf) (k' := RB));
        [ unfold RBf; lia | unfold RBf; lia | lia | lia | ].
      (* transport the edge result to the goal codomain *)
      asimpl in Vapp.
      match goal with
      | |- Val _ _ _ ?T _ => replace T with (B[⇑ σ][N[σ] .: var])
      end;
        [ exact (@Val_app_transport _ Δ _ _ u v_sel a (app f u_sel)
                   (wt_Selection_abs WTbig Sel) WT hUc Caaf LEu_vsel RBf VTc Vapp)
        | solve [ apply subst1_subst_comm | symmetry; apply subst1_subst_comm ] ].
  - (* EqVal cross conjunct (adequacyConvSub2-App) *)
    destruct (is_bot u) eqn:Hu.
    + have Eu : u = bot by apply is_bot_eq; rewrite Hu.
      subst u. apply EqVal_Bot.
    + cbn in evMN. rewrite Hu in evMN.
      move: evMN => [v0 [evM_sing evN]].
      have IT : InvTyped Γ M (Core.tpi A B) ρ.
      { apply typing_EvalRel. exact TM. exact Fρ. }
      have [vbig [abig [WTbig [LEbig [evMbig evTpi]]]]] := IT (v0 ↦ u) evM_sing.
      unfold singleton in LEbig. rewrite Hu in LEbig.
      have [g [Evbig LEfun]] := le_abs_inv LEbig. subst vbig.
      destruct abig as [ | | | | | b f | ];
        try solve [ exfalso; clear -WTbig; inversion WTbig ].
      have evTpiC := evTpi. cbn in evTpiC. move: evTpiC => [Vb [Vf [evA_b _]]].
      have Vg : valid_fun g := proj1 (andb_prop _ _ (wt_valid_tm WTbig)).
      have Vv0 : valid v0 := EvalRel_valid evN.
      have [u_sel [v_sel [Sel [Le_usel Eq_vsel]]]] := selectionBelow Vg Vv0.
      have [WTu_sel WTv_sel] :
        wt u_sel b /\ wt v_sel (app f u_sel).
      { eapply wt_Selection_cod;
          [ exact (wt_abs_ty WTbig) | exact (wt_abs_inv1 WTbig)
          | move=> ui vi Hin; exact (wt_abs_inv2 WTbig Hin erefl)
          | exact Vg | exact Sel ]. }
      have Vusel : valid u_sel := wt_valid_tm WTu_sel.
      have evN_usel : EvalRel N ρ u_sel
        by (eapply EvalRel_down; [ exact Vρ | exact Vusel | exact evN | exact Le_usel ]).
      (* work at a fuel [RBf] above the FUNCTION's rank, then [EqVal_fuel_any]
         down to [RB] (the function/edge rank is not bounded by [Hrank]). *)
      pose RBf := S (max (max (rk (abs g)) (rk (tpi b f))) (max (rk u) (rk a))).
      have RKusel : rk u_sel <= rk_fun g := rk_Selection_key Sel.
      have RKb : rk b < rk (tpi b f) by (cbn; lia).
      have RKfg : rk_fun g < rk (abs g) by (cbn; lia).
      have HfM : max (rk (abs g)) (rk (tpi b f)) < S RBf by (unfold RBf; lia).
      have HfN : max (rk u_sel) (rk b) < RBf by (unfold RBf; lia).
      have [valN eqvalN] :=
        STN ρ m Δ σ σ' TS TS' CS Fρ VS VS' EVS CΔ u_sel b WTu_sel evN_usel evA_b.
      have [_ eqvalMbig] :=
        STM ρ m Δ σ σ' TS TS' CS Fρ VS VS' EVS CΔ (abs g) (tpi b f) WTbig evMbig evTpi.
      have TNσ : typing Δ N[σ] A[σ]
        by (eapply substitution_tm; [ exact TN | exact TS | exact CΔ ]).
      have convNN' : conv Δ N[σ] N[σ'] A[σ].
      { eapply subst_conv_cross;
          [ exact TN | exact CΔ | exact TS | exact TS' | exact CS ]. }
      (* expose the function's EqValPi (function variation) and the second
         ValPi (argument variation) from the cross EqVal of [M] *)
      have EM := eqvalMbig (S RBf) HfM. rewrite EqVal_abs in EM.
      move: EM => [_ [_ [VPiM' EPi]]].
      move: EPi => [A0 [B0 [HRpi [CTpi paev]]]].
      move: VPiM' => [A0' [B0' [HRpi' [CTpi' [_ pae']]]]].
      asimpl in HRpi. asimpl in HRpi'.
      have [EA0 EB0] := HeadRed_tpi_eq HRpi. subst A0 B0.
      have [EA0' EB0'] := HeadRed_tpi_eq HRpi'. subst A0' B0'.
      (* function variation: [App sf sa] vs [App sf' sa] *)
      have Efun := paev u_sel v_sel Sel WTu_sel N[σ] TNσ (valN RBf HfN).
      (* argument variation: [App sf' sa] vs [App sf' sa'] *)
      have Earg := pae' u_sel v_sel Sel WTu_sel N[σ] N[σ'] convNN' (eqvalN RBf HfN).
      (* combine by transitivity *)
      have Hvsel : rk v_sel < RBf.
      { have L := rk_Selection_val Sel. have Hf : rk_fun f < rk (tpi b f) by (cbn; lia).
        unfold RBf; lia. }
      have Ecomb := EqVal_trans Hvsel Efun Earg.
      (* the edge codomain [app f u_sel] also evaluates [B[N..]] *)
      have evB_af : EvalRel B[N..] ρ (app f u_sel).
      { destruct (is_bot (app f u_sel)) eqn:Hbaf.
        - have -> : app f u_sel = bot by apply is_bot_eq; rewrite Hbaf. apply EvalRel_bot.
        - have NB : ~ is_bot (app f u_sel) by rewrite Hbaf.
          eapply EvalRel_Pi_app_type;
            [ exact evTpi | exact Vρ | exact Vusel | reflexivity | exact NB | exact evN_usel ]. }
      have Caaf : compatible a (app f u_sel)
        by (eapply EvalRel_compatible; [ exact Vρ | exact evBN | exact evB_af ]).
      have ELub : EvalRel B[N..] ρ (lub a (app f u_sel))
        by (exact (proj2 (EvalRel_compatible_lub Vρ evBN evB_af) _ erefl)).
      have Waf : wt (app f u_sel) tuniv := wt_ty_tuniv (wt_Selection_abs WTbig Sel).
      have hUc : wt (lub a (app f u_sel)) tuniv := wt_lub (wt_ty_tuniv WT) Caaf Waf.
      have HrC : max (rk (lub a (app f u_sel))) (rk tuniv) < RBf.
      { have L1 := rk_lub a (app f u_sel). have L2 := rk_app f u_sel.
        have Hf : rk_fun f < rk (tpi b f) by (cbn; lia).
        have Htu : rk tuniv <= rk (tpi b f) by (cbn; lia).
        unfold RBf; lia. }
      have VNarg : forall v c0 (h : wt v c0), EvalRel N ρ v -> EvalRel A ρ c0 ->
          forall RB0, max (rk v) (rk c0) < RB0 -> Val RB0 Δ N[σ] A[σ] h
        by (move=> v c0 h ev ea;
            exact (proj1 (STN ρ m Δ σ σ TS TS (ConvSub_refl TS) Fρ VS VS (ValSub_EqValSub VS) CΔ v c0 h ev ea))).
      have VTc : Val RBf Δ (B[⇑ σ][N[σ] .: var]) Core.tuniv hUc
        by (eapply codomain_type_ValTy;
              [ exact TA | exact TN | exact STA | exact STB | exact Fρ | exact TS
              | exact VS | exact CΔ | exact VNarg | exact ELub | exact HrC ]).
      have LEu_vsel : le u v_sel.
      { rewrite le_fun_cons in LEfun.
        have LEua := proj1 (andb_prop _ _ LEfun).
        rewrite Eq_vsel in LEua. exact LEua. }
      (* drop from the function-rank fuel [RBf] down to the result fuel [RB] *)
      apply (EqVal_fuel_any (k := RBf) (k' := RB));
        [ unfold RBf; lia | unfold RBf; lia | lia | lia | ].
      (* transport the combined edge result to the goal codomain *)
      asimpl in Ecomb.
      match goal with
      | |- EqVal _ _ _ _ ?T _ => replace T with (B[⇑ σ][N[σ] .: var])
      end;
        [ exact (@EqVal_app_transport _ Δ _ _ _ u v_sel a (app f u_sel)
                   (wt_Selection_abs WTbig Sel) WT hUc Caaf LEu_vsel RBf VTc Ecomb)
        | solve [ apply subst1_subst_comm | symmetry; apply subst1_subst_comm ] ].
Qed.

(** Nat formation: [tnat] is semantically a type.  (No Agda counterpart — the
    MIN fragment omits ℕ.) *)
Lemma st_nat :
  ctx Γ ->
(* ------------------------- *)
  semantic_typing Γ Core.tnat Core.tuniv.
Proof.
  intros CG.
  unfold semantic_typing.
  intros ρ m Δ s s' Ts Ts' CS F VSs VSs' ES CD u a WT EN EU.
  cbn in EN.
  split; intros RB.
  - destruct (is_bot u) eqn:IB; destruct u; try done.
    + destruct RB; try done. cbn.
      destruct a; try done.
    + destruct RB; try done. cbn.
      destruct a; try done.
  - destruct (is_bot u) eqn:IB; destruct u; try done.
    + destruct RB; try done. cbn.
      destruct a; try done.  
    + destruct RB; try done. cbn.
      destruct a; try done.
Qed.

(** Nat introduction: [zero] is semantically typed at [tnat] (ℕ; no Agda
    counterpart). *)
Lemma st_zero :
  ctx Γ ->
(* ------------------------- *)
  semantic_typing Γ Core.zero Core.tnat.
Proof.
  intros CG.
  unfold semantic_typing.
  intros ρ m Δ s s' Ts Ts' CS F VSs VSs' ES CD u a WT EN EU.
  cbn in EN.
  (* the [Red3] leaf conversion for the numeral [zero] is just reflexivity *)
  have Czero : conv Δ Core.zero Core.zero Core.tnat
    by (apply c_refl; apply t_zero; exact CD).
  split; intros RB.
  - destruct (is_bot u) eqn:IB; destruct u; try done.
    + destruct RB; try done. cbn.
      destruct a; try done.
    + destruct RB; try done. cbn.
      destruct a; try done. cbn.
      move=> h. split; [ eapply ms_refl | exact Czero ].
  - destruct (is_bot u) eqn:IB; destruct u; try done.
    + destruct RB; try done. cbn.
      destruct a; try done.  
    + cbn. destruct a; cbn; try done.
      move=> h. destruct RB. done. cbn. done.
      move=> h. destruct RB. done. cbn. 
      repeat split; first [ eapply ms_refl | exact Czero ].
Qed.

(** Nat successor: [succ M] is semantically typed at [tnat] when [M] is (ℕ; no
    Agda counterpart). *)
Lemma st_succ M :
  typing Γ M Core.tnat ->
  semantic_typing Γ M Core.tnat ->
(* ------------------------- *)
  semantic_typing Γ (Core.succ M) Core.tnat.
Proof.
  move=> TM SM.
  intros ρ m Δ s s' Ts Ts' CS F VSs VSs' ES CD u a WT EN EU.
  have Vρ : valid_env ρ := fits_valid_env F.
  specialize (SM ρ m Δ s s' Ts Ts' CS F VSs VSs' ES CD).
  (* [u = bot] is trivial in both conjuncts *)
  destruct (is_bot u) eqn:Bu.
  { have Eu : u = bot by (apply is_bot_eq; rewrite Bu). subst u.
    split; intros RB Hrank; [ apply Val_Bot | apply EqVal_Bot ]. }
  (* [u <> bot]: [EvalRel (succ M) ρ u] gives [u <= succ v] and [EvalRel M ρ v] *)
  move: EN. cbn. rewrite Bu. move=> [Vu [v [LEuv EMv]]].
  destruct u as [ | | | | w | b f | g ];
    try discriminate; try (exfalso; move: LEuv; done).
  (* only [u = succ w] survives *)
  have Ea : a = tnat by (inversion WT; reflexivity). subst a.
  move: LEuv. rewrite le_succ. move=> Lwv.
  have Vw : valid w by (eapply wt_valid_tm; eapply wt_succ_inv; exact WT).
  have EMw : EvalRel M ρ w by (eapply EvalRel_down; [ exact Vρ | exact Vw | exact EMv | exact Lwv ]).
  have evN : EvalRel Core.tnat ρ tnat by (cbn; apply le_refl).
  (* the [Red3] leaf conversion: the term already *is* a successor, so the
     conversion to its own numeral form is reflexivity *)
  have TsuccΓ : typing Γ (Core.succ M) Core.tnat by (apply t_succ; exact TM).
  have TsuccS : typing Δ (Core.succ M[s]) Core.tnat.
  { move: (substitution_tm _ (Core.succ M) Core.tnat _ s TsuccΓ Ts CD) => hh.
    asimpl in hh. exact hh. }
  have TsuccS' : typing Δ (Core.succ M[s']) Core.tnat.
  { move: (substitution_tm _ (Core.succ M) Core.tnat _ s' TsuccΓ Ts' CD) => hh.
    asimpl in hh. exact hh. }
  (* the predecessors' conversion, from the cross-substitution conversion *)
  have cvPred : conv Δ M[s] M[s'] Core.tnat.
  { move: (subst_conv_cross TM CD Ts Ts' CS) => hh. asimpl in hh. exact hh. }
  split.
  - (* Val (succ M)[σ] : tnat, at value [succ w] *)
    intros RB Hrank. destruct RB as [ | RB' ]; [ cbn in Hrank; lia | ].
    rewrite Val_succ. exists M[s]. split; [ apply ms_refl | ].
    split; [ apply c_refl; exact TsuccS | ].
    destruct (is_bot w) eqn:Bw.
    { have Ew : w = bot by (apply is_bot_eq; rewrite Bw).
      move: (wt_succ_inv WT). rewrite Ew. move=> wb. apply Val_Bot. }
    have RPw : 1 <= rk w := rk_pos Bw.
    apply (proj1 (SM w tnat (wt_succ_inv WT) EMw evN) RB').
    cbn in Hrank |- *. lia.
  - (* EqVal (succ M)[σ] (succ M)[σ'] : tnat *)
    intros RB Hrank. destruct RB as [ | RB' ]; [ cbn in Hrank; lia | ].
    rewrite EqVal_succ. exists M[s]. split; [ apply ms_refl | ].
    split; [ apply c_refl; exact TsuccS | ].
    exists M[s']. split; [ apply ms_refl | ].
    split; [ apply c_refl; exact TsuccS' | ].
    split; [ exact cvPred | ].
    destruct (is_bot w) eqn:Bw.
    { have Ew : w = bot by (apply is_bot_eq; rewrite Bw).
      move: (wt_succ_inv WT). rewrite Ew. move=> wb. apply EqVal_Bot. }
    have RPw : 1 <= rk w := rk_pos Bw.
    apply (proj2 (SM w tnat (wt_succ_inv WT) EMw evN) RB').
    cbn in Hrank |- *. lia.
Qed.

(** The zero branch of [st_case] (Agda [adequacyV-ty-Case-dep], zero case).

    This is where the [Red3] refactor pays off: the scrutinee's [Val] at the
    value code [zero] now carries [conv Δ M[σ] zero tnat] alongside
    [HeadRed M[σ] zero], and *that conversion* is what lets the dependent
    motive be transported from [T[zero..]] to [T[M..]] — both semantically
    (an [EqValTy] obtained from the motive's own semantic typing at the two
    substitutions [zero .: σ] and [M[σ] .: σ]) and syntactically (the
    [conv] argument of [Val_EqVal_fwd]).  No confluence, no Π-injectivity, no
    appeal to [adequacyEqSub] — hence no circularity. *)
Lemma st_case_Val_zero (T : Tm (S n)) M M0 M1
  (TT : typing (Γ ++ Core.tnat) T Core.tuniv)
  (TM : typing Γ M Core.tnat)
  (TM0 : typing Γ M0 (T[Core.zero..]))
  (TM1 : typing (Γ ++ Core.tnat) M1 T[rho])
  (STT : semantic_typing (Γ ++ Core.tnat) T Core.tuniv)
  (SM : semantic_typing Γ M Core.tnat)
  (SM0 : semantic_typing Γ M0 (T[Core.zero..]))
  ρ m (Δ : Ctx m) (σ σ' : Sub n m)
  (TS : typing_subst Δ σ Γ) (TS' : typing_subst Δ σ' Γ) (CS : ConvSub Δ Γ σ σ')
  (Fρ : fits Γ ρ) (VS : ValSub Δ Γ σ ρ) (VS' : ValSub Δ Γ σ' ρ)
  (EVS : EqValSub Δ Γ σ σ' ρ) (CΔ : ctx Δ) u a (WT : wt u a)
  (evMz : EvalRel M ρ zero) (evM0 : EvalRel M0 ρ u)
  (evT : EvalRel T[M..] ρ a) :
  forall RB, max (rk u) (rk a) < RB ->
    Val RB Δ (Core.ncase M M0 M1)[σ] (T[M..])[σ] WT.
Proof.
  have Vρ : valid_env ρ := fits_valid_env Fρ.
  have cΓ : ctx Γ by (eapply typing_ctx; exact TM).
  have evTn : EvalRel Core.tnat ρ tnat by (cbn; apply le_refl).
  (* ---- 1. the scrutinee's [Val] at the code [zero]: [HeadRed] + [Red3] ---- *)
  have [valSc _] :=
    SM ρ m Δ σ σ' TS TS' CS Fρ VS VS' EVS CΔ zero tnat wt_zero evMz evTn.
  have VSc := valSc (S (max (rk zero) (rk tnat))) ltac:(lia).
  rewrite Val_zero in VSc. move: VSc => [HRz cvM].
  (* ---- 2. the motive at the environment [zero .: ρ] ---- *)
  have [v' [evMv' evTv']] := EvalRel_subst1_forward Vρ evT.
  have Vv' : valid v' := EvalRel_valid evMv'.
  have Lev' : le v' zero := compatible_zero_le (EvalRel_compatible Vρ evMz evMv').
  have evTρ : EvalRel T (zero .: ρ) a.
  { eapply EvalRel_mono_env;
      [ exact evTv' | apply valid_cons; [ exact Vv' | exact Vρ ]
      | apply valid_cons; [ done | exact Vρ ]
      | apply le_env_cons; [ exact Lev' | apply le_env_refl; exact Vρ ] ]. }
  have evTz : EvalRel T[Core.zero..] ρ a
    by (eapply EvalRel_subst1_backwards;
        [ exact Vρ | cbn; apply le_refl | exact evTρ ]).
  (* ---- 3. the zero branch's [Val], at the *zero* motive ---- *)
  have [valBr _] :=
    SM0 ρ m Δ σ σ' TS TS' CS Fρ VS VS' EVS CΔ u a WT evM0 evTz.
  (* ---- 4. the two substitutions [zero .: σ] and [M[σ] .: σ] agree on the
             motive, semantically ([EqValTy]) and syntactically ([conv]) ---- *)
  have Tzero : typing Δ Core.zero Core.tnat by (apply t_zero; exact CΔ).
  have TMσ : typing Δ M[σ] Core.tnat.
  { move: (substitution_tm _ M Core.tnat _ σ TM TS CΔ) => hh. asimpl in hh. exact hh. }
  have TS0 : typing_subst Δ (Core.zero .: σ) (Γ ++ Core.tnat)
    by (eapply typing_subst_cons; [ asimpl; exact Tzero | exact TS ]).
  have TS0' : typing_subst Δ (M[σ] .: σ) (Γ ++ Core.tnat)
    by (eapply typing_subst_cons; [ asimpl; exact TMσ | exact TS ]).
  have CS0 : ConvSub Δ (Γ ++ Core.tnat) (Core.zero .: σ) (M[σ] .: σ)
    by (eapply ConvSub_cons;
        [ asimpl; apply c_sym; exact cvM | exact (ConvSub_refl TS) ]).
  have Fits0 : fits (Γ ++ Core.tnat) (zero .: ρ)
    by (eapply fits_cons with (a := tnat);
        [ apply t_nat; exact cΓ | cbn; apply le_refl | apply wt_tnat
        | apply wt_zero | exact Fρ ]).
  have HZhead : forall u0, valid u0 -> le u0 zero -> forall a0 (h0 : wt u0 a0),
      EvalRel Core.tnat ρ a0 -> forall RB0, max (rk u0) (rk a0) < RB0 ->
      Val RB0 Δ Core.zero Core.tnat[σ] h0.
  { move=> u0 Vu0 Le0 a0 h0 Ea0 RB0 Hr0.
    destruct u0 as [ | | | | w0 | b0 f0 | g0 ];
      try solve [ autorewrite with le in Le0; done ].
    - apply Val_Bot.
    - have Ea : a0 = tnat by (inversion h0; reflexivity). subst a0.
      destruct RB0 as [ | RB0' ]; [ cbn in Hr0; lia | ].
      rewrite Val_zero. split; [ apply ms_refl | apply c_refl; exact Tzero ]. }
  have HMhead : forall u0, valid u0 -> le u0 zero -> forall a0 (h0 : wt u0 a0),
      EvalRel Core.tnat ρ a0 -> forall RB0, max (rk u0) (rk a0) < RB0 ->
      Val RB0 Δ M[σ] Core.tnat[σ] h0.
  { move=> u0 Vu0 Le0 a0 h0 Ea0 RB0 Hr0.
    have evMu0 : EvalRel M ρ u0
      by (eapply EvalRel_down; [ exact Vρ | exact Vu0 | exact evMz | exact Le0 ]).
    exact (proj1 (SM ρ m Δ σ σ' TS TS' CS Fρ VS VS' EVS CΔ u0 a0 h0
                    evMu0 Ea0) RB0 Hr0). }
  have HEhead : forall u0, valid u0 -> le u0 zero -> forall a0 (h0 : wt u0 a0),
      EvalRel Core.tnat ρ a0 -> forall RB0, max (rk u0) (rk a0) < RB0 ->
      EqVal RB0 Δ Core.zero M[σ] Core.tnat[σ] h0.
  { move=> u0 Vu0 Le0 a0 h0 Ea0 RB0 Hr0.
    destruct u0 as [ | | | | w0 | b0 f0 | g0 ];
      try solve [ autorewrite with le in Le0; done ].
    - apply EqVal_Bot.
    - have Ea : a0 = tnat by (inversion h0; reflexivity). subst a0.
      destruct RB0 as [ | RB0' ]; [ cbn in Hr0; lia | ].
      rewrite EqVal_zero.
      split; [ apply ms_refl | ]. split; [ apply c_refl; exact Tzero | ].
      split; [ exact HRz | exact cvM ]. }
  have VS0 : ValSub Δ (Γ ++ Core.tnat) (Core.zero .: σ) (zero .: ρ)
    by (eapply ValSub_cons; [ exact HZhead | exact VS ]).
  have VS0' : ValSub Δ (Γ ++ Core.tnat) (M[σ] .: σ) (zero .: ρ)
    by (eapply ValSub_cons; [ exact HMhead | exact VS ]).
  have EVS0 : EqValSub Δ (Γ ++ Core.tnat) (Core.zero .: σ) (M[σ] .: σ) (zero .: ρ)
    by (eapply EqValSub_cons; [ exact HEhead | exact (ValSub_EqValSub VS) ]).
  have WTa : wt a tuniv := wt_ty_tuniv WT.
  have evU0 : EvalRel Core.tuniv (zero .: ρ) tuniv by (cbn; apply le_refl).
  have [_ eqT] :=
    STT (zero .: ρ) m Δ (Core.zero .: σ) (M[σ] .: σ) TS0 TS0' CS0 Fits0
        VS0 VS0' EVS0 CΔ a tuniv WTa evTρ evU0.
  have cvTT : conv Δ T[Core.zero .: σ] T[M[σ] .: σ] Core.tuniv
    := subst_conv_cross TT CΔ TS0 TS0' CS0.
  (* ---- 5. syntactic pieces of the [c_ncase_Z] step conversion ---- *)
  have TTσ : typing (Δ ++ Core.tnat) T[⇑ σ] Core.tuniv.
  { exact (@subst_cod_typing n Γ Core.tnat T m Δ σ
             ltac:(apply t_nat; exact cΓ) TT TS CΔ). }
  have TM0σ : typing Δ M0[σ] (T[⇑ σ][Core.zero..]).
  { move: (substitution_tm _ M0 (T[Core.zero..]) _ σ TM0 TS CΔ) => hh.
    asimpl in hh. asimpl. exact hh. }
  have CΔn : ctx (Δ ++ Core.tnat)
    by (eapply c_cons; [ exact CΔ | apply t_nat; exact CΔ ]).
  have TSl : typing_subst (Δ ++ Core.tnat) (⇑ σ) (Γ ++ Core.tnat).
  { exact (@typing_subst_lift m Δ n σ Γ Core.tnat CΔn TS). }
  have TM1σ : typing (Δ ++ Core.tnat) M1[⇑ σ] (T[⇑ σ])[rho].
  { rewrite rho_subst_comm.
    exact (substitution_tm _ M1 (T[rho]) _ (⇑ σ) TM1 TSl CΔn). }
  (* ---- 6. assemble: transport the branch's [Val], then head-expand ---- *)
  move=> RB Hrank.
  have cvTs : conv Δ (T[⇑ σ][Core.zero..]) (T[⇑ σ][M[σ]..]) Core.tuniv.
  { rewrite -(subst_cons_eq T Core.zero σ) -(subst_cons_eq T M[σ] σ). exact cvTT. }
  have VBrM : Val RB Δ M0[σ] (T[⇑ σ][M[σ]..]) WT.
  { eapply Val_EqVal_fwd;
      [ cbn in Hrank; lia | cbn in Hrank; lia | exact cvTs
      | (* [Val] of the branch at [(T[zero..])[σ]] = [T[⇑σ][zero..]] *)
        move: (valBr RB Hrank); rewrite subst1_subst_comm; done
      | rewrite -(subst_cons_eq T Core.zero σ) -(subst_cons_eq T M[σ] σ);
        eapply EqVal_EqValTy;
        exact (eqT (S RB) ltac:(cbn in Hrank |- *; lia)) ]. }
  have HRstep : HeadRed (Core.ncase M M0 M1)[σ] M0[σ].
  { cbn. eapply relations.ms_app;
      [ eapply HeadRed_ncase; exact HRz
      | eapply ms_trans; [ apply hr_zero | apply ms_refl ] ]. }
  have cvStep : conv Δ (Core.ncase M M0 M1)[σ] M0[σ] (T[⇑ σ][M[σ]..]).
  { cbn. eapply c_trans.
    - eapply c_ncase;
        [ exact TTσ | exact cvM | apply c_refl; exact TM0σ | apply c_refl; exact TM1σ ].
    - eapply c_conv;
        [ eapply c_ncase_Z; [ exact TTσ | exact TM0σ | exact TM1σ ] | exact cvTs ]. }
  move: VBrM.
  have EQg : (T[M..])[σ] = T[⇑ σ][M[σ]..] by (asimpl; reflexivity).
  rewrite EQg.
  move=> VBrM'.
  eapply Val_beta_expand; [ exact HRstep | exact cvStep | exact VBrM' ].
Qed.

(** The successor branch of [st_case].  Same skeleton as
    [st_case_Val_zero], with two extra wrinkles:

    - the scrutinee's value [succ vp] and the value [v'] that witnesses the
      motive's evaluation must first be **joined**.  Unlike [zero], a successor
      is not maximal among its compatible elements ([succ bot] and [succ zero]
      are compatible but unordered), so [compatible_zero_le] has no analogue;
      we go through [EvalRel_compatible_lub] and [le_succ_inv] to land on a
      single successor value [succ vpp] above both.
    - the substitution head is the **predecessor term** [P] delivered by the
      scrutinee's [Val_succ], which is not the image of any [Γ]-term.  Its
      [ValSub] obligations are discharged by re-running the scrutinee's IH at
      the code [succ u0] and identifying the predecessor with
      [HeadRed_succ_det]; the obligations at [succ vpp] are discharged by
      head-*contracting* the scrutinee's own [Val] along [HeadRed M[σ] (succ P)]
      (which needs the [Red3] conversion, again). *)
Lemma st_case_Val_succ (T : Tm (S n)) M M0 M1
  (TT : typing (Γ ++ Core.tnat) T Core.tuniv)
  (TM : typing Γ M Core.tnat)
  (TM0 : typing Γ M0 (T[Core.zero..]))
  (TM1 : typing (Γ ++ Core.tnat) M1 T[rho])
  (STT : semantic_typing (Γ ++ Core.tnat) T Core.tuniv)
  (SM : semantic_typing Γ M Core.tnat)
  (SM1 : semantic_typing (Γ ++ Core.tnat) M1 T[rho])
  ρ m (Δ : Ctx m) (σ σ' : Sub n m)
  (TS : typing_subst Δ σ Γ) (TS' : typing_subst Δ σ' Γ) (CS : ConvSub Δ Γ σ σ')
  (Fρ : fits Γ ρ) (VS : ValSub Δ Γ σ ρ) (VS' : ValSub Δ Γ σ' ρ)
  (EVS : EqValSub Δ Γ σ σ' ρ) (CΔ : ctx Δ) u a (WT : wt u a)
  vp (evMs : EvalRel M ρ (succ vp)) (evM1 : EvalRel M1 (vp .: ρ) u)
  (evT : EvalRel T[M..] ρ a) :
  forall RB, max (rk u) (rk a) < RB ->
    Val RB Δ (Core.ncase M M0 M1)[σ] (T[M..])[σ] WT.
Proof.
  have Vρ : valid_env ρ := fits_valid_env Fρ.
  have cΓ : ctx Γ by (eapply typing_ctx; exact TM).
  have evTn : EvalRel Core.tnat ρ tnat by (cbn; apply le_refl).
  (* ---- 1. join the scrutinee's value with the motive's witness value ---- *)
  have [v' [evMv' evTv']] := EvalRel_subst1_forward Vρ evT.
  have Vsvp : valid (succ vp) := EvalRel_valid evMs.
  have Vv' : valid v' := EvalRel_valid evMv'.
  have [Cmp Hlub] := EvalRel_compatible_lub Vρ evMs evMv'.
  have evMc := Hlub _ erefl.
  have Lecl : le (succ vp) (lub (succ vp) v')
    by (apply le_lub_left; [ exact Cmp | exact Vsvp | exact Vv' ]).
  have Lecr : le v' (lub (succ vp) v')
    by (apply le_lub_right; [ exact Cmp | exact Vsvp | exact Vv' ]).
  have [vpp [Ec Levp]] := le_succ_inv Lecl.
  rewrite Ec in evMc Lecr.
  have Vsvpp : valid (succ vpp) := EvalRel_valid evMc.
  have Vvpp : valid vpp by (move: Vsvpp; cbn; done).
  have Vvp : valid vp by (move: Vsvp; cbn; done).
  have evTc : EvalRel T (succ vpp .: ρ) a.
  { eapply EvalRel_mono_env;
      [ exact evTv' | apply valid_cons; [ exact Vv' | exact Vρ ]
      | apply valid_cons; [ exact Vsvpp | exact Vρ ]
      | apply le_env_cons; [ exact Lecr | apply le_env_refl; exact Vρ ] ]. }
  (* ---- 2. well-typedness of the joined value, from typing soundness ---- *)
  have IT : InvTyped Γ M Core.tnat ρ by (apply typing_EvalRel; [ exact TM | exact Fρ ]).
  have [vv [aa [hwt [Lsv [_ Etn]]]]] := IT (succ vpp) evMc.
  cbn in Etn.
  have wtvv : wt vv tnat := wt_le hwt Etn (wt_ty_tuniv hwt) wt_tnat.
  have wtsvpp : wt (succ vpp) tnat := wt_tnat_down wtvv Lsv.
  set wtvpp := wt_succ_inv wtsvpp.
  (* ---- 3. the scrutinee's [Val] at the code [succ vpp]: the [Red3]
             conversion to a successor, plus the predecessor term ---- *)
  have [valSc _] :=
    SM ρ m Δ σ σ' TS TS' CS Fρ VS VS' EVS CΔ (succ vpp) tnat wtsvpp evMc evTn.
  have VSc := valSc (S (S (max (rk (succ vpp)) (rk tnat)))) ltac:(lia).
  rewrite Val_succ in VSc. move: VSc => [P [HRs [cvM VP]]].
  have [TMσ TsP] := conv_typing cvM.
  have TP : typing Δ P Core.tnat := typing_succ_arg_inv TsP.
  (* ---- 4. [ValSub]/[EqValSub] heads at the value [succ vpp] ---- *)
  have HMhead : forall u0, valid u0 -> le u0 (succ vpp) -> forall a0 (h0 : wt u0 a0),
      EvalRel Core.tnat ρ a0 -> forall RB0, max (rk u0) (rk a0) < RB0 ->
      Val RB0 Δ M[σ] Core.tnat[σ] h0.
  { move=> u0 Vu0 Le0 a0 h0 Ea0 RB0 Hr0.
    have evMu0 : EvalRel M ρ u0
      by (eapply EvalRel_down; [ exact Vρ | exact Vu0 | exact evMc | exact Le0 ]).
    exact (proj1 (SM ρ m Δ σ σ' TS TS' CS Fρ VS VS' EVS CΔ u0 a0 h0
                    evMu0 Ea0) RB0 Hr0). }
  have HPhead : forall u0, valid u0 -> le u0 (succ vpp) -> forall a0 (h0 : wt u0 a0),
      EvalRel Core.tnat ρ a0 -> forall RB0, max (rk u0) (rk a0) < RB0 ->
      Val RB0 Δ (Core.succ P) Core.tnat[σ] h0.
  { move=> u0 Vu0 Le0 a0 h0 Ea0 RB0 Hr0.
    eapply Val_headred_contract;
      [ exact HRs | apply c_sym; exact cvM
      | exact (HMhead u0 Vu0 Le0 a0 h0 Ea0 RB0 Hr0) ]. }
  have HEhead : forall u0, valid u0 -> le u0 (succ vpp) -> forall a0 (h0 : wt u0 a0),
      EvalRel Core.tnat ρ a0 -> forall RB0, max (rk u0) (rk a0) < RB0 ->
      EqVal RB0 Δ (Core.succ P) M[σ] Core.tnat[σ] h0.
  { move=> u0 Vu0 Le0 a0 h0 Ea0 RB0 Hr0.
    eapply EqVal_headred_contract;
      [ exact HRs | apply ms_refl | apply c_sym; exact cvM
      | apply c_refl; exact TMσ
      | eapply Val_EqVal; exact (HMhead u0 Vu0 Le0 a0 h0 Ea0 RB0 Hr0) ]. }
  (* ---- 5. the [ValSub] head for the predecessor term [P] ---- *)
  have HPPhead : forall u0, valid u0 -> le u0 vpp -> forall a0 (h0 : wt u0 a0),
      EvalRel Core.tnat ρ a0 -> forall RB0, max (rk u0) (rk a0) < RB0 ->
      Val RB0 Δ P Core.tnat[σ] h0.
  { move=> u0 Vu0 Le0 a0 h0 Ea0 RB0 Hr0. cbn in Ea0.
    destruct a0 as [ | | | | z0 | b0 f0 | g0 ];
      try solve [ autorewrite with le in Ea0; done ].
    - apply Val_bot_ty.
    - have Vsu0 : valid (succ u0) by (cbn; exact Vu0).
      have Lesu0 : le (succ u0) (succ vpp) by (rewrite le_succ; exact Le0).
      have evMsu0 : EvalRel M ρ (succ u0)
        by (eapply EvalRel_down; [ exact Vρ | exact Vsu0 | exact evMc | exact Lesu0 ]).
      have VM0 := proj1 (SM ρ m Δ σ σ' TS TS' CS Fρ VS VS' EVS CΔ
                           (succ u0) tnat (wt_succ h0) evMsu0 evTn)
                    (S RB0) ltac:(cbn in Hr0 |- *; lia).
      rewrite Val_succ in VM0. move: VM0 => [P0 [HRs0 [cv0 VP0]]].
      have EP : P0 = P by (eapply HeadRed_succ_det; [ exact HRs0 | exact HRs ]).
      subst P0. eapply Val_irr; exact VP0. }
  (* ---- 6. the successor branch's [Val], at the [rho]-shifted motive ---- *)
  have evM1' : EvalRel M1 (vpp .: ρ) u.
  { eapply EvalRel_mono_env;
      [ exact evM1 | apply valid_cons; [ exact Vvp | exact Vρ ]
      | apply valid_cons; [ exact Vvpp | exact Vρ ]
      | apply le_env_cons; [ exact Levp | apply le_env_refl; exact Vρ ] ]. }
  have SRrho : SubRel rho (succ vpp .: ρ) (vpp .: ρ).
  { move=> [j|]; cbn.
    - split; [ exact (Vρ j) | apply le_refl; exact (Vρ j) ].
    - split; [ exact Vsvpp | ].
      exists vpp. split; [ apply le_refl; exact Vsvpp | ].
      split; [ exact Vvpp | apply le_refl; exact Vvpp ]. }
  have evTrho : EvalRel T[rho] (vpp .: ρ) a.
  { eapply EvalRel_subst;
      [ apply valid_cons; [ exact Vsvpp | exact Vρ ]
      | apply valid_cons; [ exact Vvpp | exact Vρ ]
      | exact SRrho | exact evTc ]. }
  have Fits1 : fits (Γ ++ Core.tnat) (vpp .: ρ)
    by (eapply fits_cons with (a := tnat);
        [ apply t_nat; exact cΓ | cbn; apply le_refl | apply wt_tnat
        | exact wtvpp | exact Fρ ]).
  have TS1 : typing_subst Δ (P .: σ) (Γ ++ Core.tnat)
    by (eapply typing_subst_cons; [ asimpl; exact TP | exact TS ]).
  have VS1 : ValSub Δ (Γ ++ Core.tnat) (P .: σ) (vpp .: ρ)
    by (eapply ValSub_cons; [ exact HPPhead | exact VS ]).
  have [valBr _] :=
    SM1 (vpp .: ρ) m Δ (P .: σ) (P .: σ) TS1 TS1 (ConvSub_refl TS1) Fits1
        VS1 VS1 (ValSub_EqValSub VS1) CΔ u a WT evM1' evTrho.
  (* ---- 7. the motive transport, from the motive's own semantic typing ---- *)
  have TS2 : typing_subst Δ (Core.succ P .: σ) (Γ ++ Core.tnat)
    by (eapply typing_subst_cons; [ asimpl; exact TsP | exact TS ]).
  have TS2' : typing_subst Δ (M[σ] .: σ) (Γ ++ Core.tnat)
    by (eapply typing_subst_cons; [ asimpl; exact TMσ | exact TS ]).
  have CS2 : ConvSub Δ (Γ ++ Core.tnat) (Core.succ P .: σ) (M[σ] .: σ)
    by (eapply ConvSub_cons;
        [ asimpl; apply c_sym; exact cvM | exact (ConvSub_refl TS) ]).
  have Fits2 : fits (Γ ++ Core.tnat) (succ vpp .: ρ)
    by (eapply fits_cons with (a := tnat);
        [ apply t_nat; exact cΓ | cbn; apply le_refl | apply wt_tnat
        | exact wtsvpp | exact Fρ ]).
  have VS2 : ValSub Δ (Γ ++ Core.tnat) (Core.succ P .: σ) (succ vpp .: ρ)
    by (eapply ValSub_cons; [ exact HPhead | exact VS ]).
  have VS2' : ValSub Δ (Γ ++ Core.tnat) (M[σ] .: σ) (succ vpp .: ρ)
    by (eapply ValSub_cons; [ exact HMhead | exact VS ]).
  have EVS2 : EqValSub Δ (Γ ++ Core.tnat) (Core.succ P .: σ) (M[σ] .: σ)
                (succ vpp .: ρ)
    by (eapply EqValSub_cons; [ exact HEhead | exact (ValSub_EqValSub VS) ]).
  have WTa : wt a tuniv := wt_ty_tuniv WT.
  have evU2 : EvalRel Core.tuniv (succ vpp .: ρ) tuniv by (cbn; apply le_refl).
  have [_ eqT] :=
    STT (succ vpp .: ρ) m Δ (Core.succ P .: σ) (M[σ] .: σ) TS2 TS2' CS2 Fits2
        VS2 VS2' EVS2 CΔ a tuniv WTa evTc evU2.
  have cvTT : conv Δ T[Core.succ P .: σ] T[M[σ] .: σ] Core.tuniv
    := subst_conv_cross TT CΔ TS2 TS2' CS2.
  (* ---- 8. syntactic pieces of the [c_ncase_S] step conversion ---- *)
  have TTσ : typing (Δ ++ Core.tnat) T[⇑ σ] Core.tuniv.
  { exact (@subst_cod_typing n Γ Core.tnat T m Δ σ
             ltac:(apply t_nat; exact cΓ) TT TS CΔ). }
  have TM0σ : typing Δ M0[σ] (T[⇑ σ][Core.zero..]).
  { move: (substitution_tm _ M0 (T[Core.zero..]) _ σ TM0 TS CΔ) => hh.
    asimpl in hh. asimpl. exact hh. }
  have CΔn : ctx (Δ ++ Core.tnat)
    by (eapply c_cons; [ exact CΔ | apply t_nat; exact CΔ ]).
  have TSl : typing_subst (Δ ++ Core.tnat) (⇑ σ) (Γ ++ Core.tnat).
  { exact (@typing_subst_lift m Δ n σ Γ Core.tnat CΔn TS). }
  have TM1σ : typing (Δ ++ Core.tnat) M1[⇑ σ] (T[⇑ σ])[rho].
  { rewrite rho_subst_comm.
    exact (substitution_tm _ M1 (T[rho]) _ (⇑ σ) TM1 TSl CΔn). }
  (* ---- 9. assemble: transport the branch's [Val], then head-expand ---- *)
  move=> RB Hrank.
  have cvTs : conv Δ (T[⇑ σ][(Core.succ P)..]) (T[⇑ σ][M[σ]..]) Core.tuniv.
  { rewrite -(subst_cons_eq T (Core.succ P) σ) -(subst_cons_eq T M[σ] σ).
    exact cvTT. }
  have VBrM : Val RB Δ (M1[⇑ σ][P..]) (T[⇑ σ][M[σ]..]) WT.
  { eapply Val_EqVal_fwd;
      [ cbn in Hrank; lia | cbn in Hrank; lia | exact cvTs
      | move: (valBr RB Hrank);
        rewrite rho_subst_cons (subst_cons_eq M1 P σ)
                (subst_cons_eq T (Core.succ P) σ); done
      | rewrite -(subst_cons_eq T (Core.succ P) σ) -(subst_cons_eq T M[σ] σ);
        eapply EqVal_EqValTy;
        exact (eqT (S RB) ltac:(cbn in Hrank |- *; lia)) ]. }
  have HRstep : HeadRed (Core.ncase M M0 M1)[σ] (M1[⇑ σ][P..]).
  { cbn. eapply relations.ms_app;
      [ eapply HeadRed_ncase; exact HRs
      | eapply ms_trans; [ apply hr_succ | apply ms_refl ] ]. }
  have cvStep : conv Δ (Core.ncase M M0 M1)[σ] (M1[⇑ σ][P..]) (T[⇑ σ][M[σ]..]).
  { cbn. eapply c_trans.
    - eapply c_ncase;
        [ exact TTσ | exact cvM | apply c_refl; exact TM0σ | apply c_refl; exact TM1σ ].
    - eapply c_conv;
        [ eapply c_ncase_S; [ exact TTσ | exact TP | exact TM0σ | exact TM1σ ]
        | exact cvTs ]. }
  have EQg : (T[M..])[σ] = T[⇑ σ][M[σ]..] by (asimpl; reflexivity).
  rewrite EQg.
  eapply Val_beta_expand; [ exact HRstep | exact cvStep | exact VBrM ].
Qed.

(** The successor branch of [st_case]'s cross ([EqVal]) conjunct.

    The extra difficulty over [st_case_Val_succ] is that the two sides reduce
    to the branch instantiated at *different* predecessor terms, [P] (from
    [M[σ]]) and [P'] (from [M[σ']]), so the branch IH has to be run at the two
    substitutions [P .: σ] and [P' .: σ'] — which needs a *syntactic*
    [conv Δ P P' tnat].  Conversion has no successor-injectivity rule, so that
    cannot be recovered from [conv Δ (succ P) (succ P') tnat]; it is exactly
    the predecessor conversion now stored in [EqVal]'s successor leaf. *)
Lemma st_case_EqVal_succ (T : Tm (S n)) M M0 M1
  (TT : typing (Γ ++ Core.tnat) T Core.tuniv)
  (TM : typing Γ M Core.tnat)
  (TM0 : typing Γ M0 (T[Core.zero..]))
  (TM1 : typing (Γ ++ Core.tnat) M1 T[rho])
  (STT : semantic_typing (Γ ++ Core.tnat) T Core.tuniv)
  (SM : semantic_typing Γ M Core.tnat)
  (SM1 : semantic_typing (Γ ++ Core.tnat) M1 T[rho])
  ρ m (Δ : Ctx m) (σ σ' : Sub n m)
  (TS : typing_subst Δ σ Γ) (TS' : typing_subst Δ σ' Γ) (CS : ConvSub Δ Γ σ σ')
  (Fρ : fits Γ ρ) (VS : ValSub Δ Γ σ ρ) (VS' : ValSub Δ Γ σ' ρ)
  (EVS : EqValSub Δ Γ σ σ' ρ) (CΔ : ctx Δ) u a (WT : wt u a)
  vp (evMs : EvalRel M ρ (succ vp)) (evM1 : EvalRel M1 (vp .: ρ) u)
  (evT : EvalRel T[M..] ρ a) :
  forall RB, max (rk u) (rk a) < RB ->
    EqVal RB Δ (Core.ncase M M0 M1)[σ] (Core.ncase M M0 M1)[σ'] (T[M..])[σ] WT.
Proof.
  have Vρ : valid_env ρ := fits_valid_env Fρ.
  have cΓ : ctx Γ by (eapply typing_ctx; exact TM).
  have evTn : EvalRel Core.tnat ρ tnat by (cbn; apply le_refl).
  (* ---- 1. join the scrutinee's value with the motive's witness value ---- *)
  have [v' [evMv' evTv']] := EvalRel_subst1_forward Vρ evT.
  have Vsvp : valid (succ vp) := EvalRel_valid evMs.
  have Vv' : valid v' := EvalRel_valid evMv'.
  have [Cmp Hlub] := EvalRel_compatible_lub Vρ evMs evMv'.
  have evMc := Hlub _ erefl.
  have Lecl : le (succ vp) (lub (succ vp) v')
    by (apply le_lub_left; [ exact Cmp | exact Vsvp | exact Vv' ]).
  have Lecr : le v' (lub (succ vp) v')
    by (apply le_lub_right; [ exact Cmp | exact Vsvp | exact Vv' ]).
  have [vpp [Ec Levp]] := le_succ_inv Lecl.
  rewrite Ec in evMc Lecr.
  have Vsvpp : valid (succ vpp) := EvalRel_valid evMc.
  have Vvpp : valid vpp by (move: Vsvpp; cbn; done).
  have Vvp : valid vp by (move: Vsvp; cbn; done).
  have evTc : EvalRel T (succ vpp .: ρ) a.
  { eapply EvalRel_mono_env;
      [ exact evTv' | apply valid_cons; [ exact Vv' | exact Vρ ]
      | apply valid_cons; [ exact Vsvpp | exact Vρ ]
      | apply le_env_cons; [ exact Lecr | apply le_env_refl; exact Vρ ] ]. }
  (* ---- 2. well-typedness of the joined value ---- *)
  have IT : InvTyped Γ M Core.tnat ρ by (apply typing_EvalRel; [ exact TM | exact Fρ ]).
  have [vv [aa [hwt [Lsv [_ Etn]]]]] := IT (succ vpp) evMc.
  cbn in Etn.
  have wtvv : wt vv tnat := wt_le hwt Etn (wt_ty_tuniv hwt) wt_tnat.
  have wtsvpp : wt (succ vpp) tnat := wt_tnat_down wtvv Lsv.
  set wtvpp := wt_succ_inv wtsvpp.
  (* ---- 3. the scrutinee's cross [EqVal] at the code [succ vpp]: the two
             predecessor terms, their [Red3] conversions, *and* the
             predecessor conversion [cvPP] ---- *)
  have [_ eqSc] :=
    SM ρ m Δ σ σ' TS TS' CS Fρ VS VS' EVS CΔ (succ vpp) tnat wtsvpp evMc evTn.
  have ESc := eqSc (S (S (max (rk (succ vpp)) (rk tnat)))) ltac:(lia).
  rewrite EqVal_succ in ESc.
  move: ESc => [P [HRs [cvM [P' [HRs' [cvM' [cvPP EP]]]]]]].
  have [TMσ TsP] := conv_typing cvM.
  have [TMσ' TsP'] := conv_typing cvM'.
  have TP : typing Δ P Core.tnat := typing_succ_arg_inv TsP.
  have TP' : typing Δ P' Core.tnat := typing_succ_arg_inv TsP'.
  (* ---- 4. the [Sub] heads at the value [succ vpp] (σ and σ' sides) ---- *)
  have HMhead : forall u0, valid u0 -> le u0 (succ vpp) -> forall a0 (h0 : wt u0 a0),
      EvalRel Core.tnat ρ a0 -> forall RB0, max (rk u0) (rk a0) < RB0 ->
      Val RB0 Δ M[σ] Core.tnat[σ] h0.
  { move=> u0 Vu0 Le0 a0 h0 Ea0 RB0 Hr0.
    have evMu0 : EvalRel M ρ u0
      by (eapply EvalRel_down; [ exact Vρ | exact Vu0 | exact evMc | exact Le0 ]).
    exact (proj1 (SM ρ m Δ σ σ' TS TS' CS Fρ VS VS' EVS CΔ u0 a0 h0
                    evMu0 Ea0) RB0 Hr0). }
  have HEMhead : forall u0, valid u0 -> le u0 (succ vpp) -> forall a0 (h0 : wt u0 a0),
      EvalRel Core.tnat ρ a0 -> forall RB0, max (rk u0) (rk a0) < RB0 ->
      EqVal RB0 Δ M[σ] M[σ'] Core.tnat[σ] h0.
  { move=> u0 Vu0 Le0 a0 h0 Ea0 RB0 Hr0.
    have evMu0 : EvalRel M ρ u0
      by (eapply EvalRel_down; [ exact Vρ | exact Vu0 | exact evMc | exact Le0 ]).
    exact (proj2 (SM ρ m Δ σ σ' TS TS' CS Fρ VS VS' EVS CΔ u0 a0 h0
                    evMu0 Ea0) RB0 Hr0). }
  have HM'head : forall u0, valid u0 -> le u0 (succ vpp) -> forall a0 (h0 : wt u0 a0),
      EvalRel Core.tnat ρ a0 -> forall RB0, max (rk u0) (rk a0) < RB0 ->
      Val RB0 Δ M[σ'] Core.tnat[σ] h0.
  { move=> u0 Vu0 Le0 a0 h0 Ea0 RB0 Hr0.
    eapply EqVal_Val2; exact (HEMhead u0 Vu0 Le0 a0 h0 Ea0 RB0 Hr0). }
  have HPhead : forall u0, valid u0 -> le u0 (succ vpp) -> forall a0 (h0 : wt u0 a0),
      EvalRel Core.tnat ρ a0 -> forall RB0, max (rk u0) (rk a0) < RB0 ->
      Val RB0 Δ (Core.succ P) Core.tnat[σ] h0.
  { move=> u0 Vu0 Le0 a0 h0 Ea0 RB0 Hr0.
    eapply Val_headred_contract;
      [ exact HRs | apply c_sym; exact cvM
      | exact (HMhead u0 Vu0 Le0 a0 h0 Ea0 RB0 Hr0) ]. }
  have HP'head : forall u0, valid u0 -> le u0 (succ vpp) -> forall a0 (h0 : wt u0 a0),
      EvalRel Core.tnat ρ a0 -> forall RB0, max (rk u0) (rk a0) < RB0 ->
      Val RB0 Δ (Core.succ P') Core.tnat[σ] h0.
  { move=> u0 Vu0 Le0 a0 h0 Ea0 RB0 Hr0.
    eapply Val_headred_contract;
      [ exact HRs' | apply c_sym; exact cvM'
      | exact (HM'head u0 Vu0 Le0 a0 h0 Ea0 RB0 Hr0) ]. }
  have HEhead : forall u0, valid u0 -> le u0 (succ vpp) -> forall a0 (h0 : wt u0 a0),
      EvalRel Core.tnat ρ a0 -> forall RB0, max (rk u0) (rk a0) < RB0 ->
      EqVal RB0 Δ (Core.succ P) M[σ] Core.tnat[σ] h0.
  { move=> u0 Vu0 Le0 a0 h0 Ea0 RB0 Hr0.
    eapply EqVal_headred_contract;
      [ exact HRs | apply ms_refl | apply c_sym; exact cvM
      | apply c_refl; exact TMσ
      | eapply Val_EqVal; exact (HMhead u0 Vu0 Le0 a0 h0 Ea0 RB0 Hr0) ]. }
  (* ---- 5. the [Sub] heads for the two predecessor terms ---- *)
  have HPPhead : forall u0, valid u0 -> le u0 vpp -> forall a0 (h0 : wt u0 a0),
      EvalRel Core.tnat ρ a0 -> forall RB0, max (rk u0) (rk a0) < RB0 ->
      EqVal RB0 Δ P P' Core.tnat[σ] h0.
  { move=> u0 Vu0 Le0 a0 h0 Ea0 RB0 Hr0. cbn in Ea0.
    destruct a0 as [ | | | | z0 | b0 f0 | g0 ];
      try solve [ autorewrite with le in Ea0; done ].
    - apply EqVal_Bot_ty.
    - have Vsu0 : valid (succ u0) by (cbn; exact Vu0).
      have Lesu0 : le (succ u0) (succ vpp) by (rewrite le_succ; exact Le0).
      have evMsu0 : EvalRel M ρ (succ u0)
        by (eapply EvalRel_down; [ exact Vρ | exact Vsu0 | exact evMc | exact Lesu0 ]).
      have EM0 := proj2 (SM ρ m Δ σ σ' TS TS' CS Fρ VS VS' EVS CΔ
                           (succ u0) tnat (wt_succ h0) evMsu0 evTn)
                    (S RB0) ltac:(cbn in Hr0 |- *; lia).
      rewrite EqVal_succ in EM0.
      move: EM0 => [P0 [HR0 [c0 [P0' [HR0' [c0' [cp0 EV0]]]]]]].
      have E1 : P0 = P by (eapply HeadRed_succ_det; [ exact HR0 | exact HRs ]).
      have E2 : P0' = P' by (eapply HeadRed_succ_det; [ exact HR0' | exact HRs' ]).
      subst P0 P0'. eapply EqVal_irr; exact EV0. }
  have HPvhead : forall u0, valid u0 -> le u0 vpp -> forall a0 (h0 : wt u0 a0),
      EvalRel Core.tnat ρ a0 -> forall RB0, max (rk u0) (rk a0) < RB0 ->
      Val RB0 Δ P Core.tnat[σ] h0.
  { move=> u0 Vu0 Le0 a0 h0 Ea0 RB0 Hr0.
    eapply EqVal_Val1; exact (HPPhead u0 Vu0 Le0 a0 h0 Ea0 RB0 Hr0). }
  have HPv'head : forall u0, valid u0 -> le u0 vpp -> forall a0 (h0 : wt u0 a0),
      EvalRel Core.tnat ρ a0 -> forall RB0, max (rk u0) (rk a0) < RB0 ->
      Val RB0 Δ P' Core.tnat[σ'] h0.
  { move=> u0 Vu0 Le0 a0 h0 Ea0 RB0 Hr0.
    eapply EqVal_Val2; exact (HPPhead u0 Vu0 Le0 a0 h0 Ea0 RB0 Hr0). }
  (* ---- 6. the successor branch's cross [EqVal] ---- *)
  have evM1' : EvalRel M1 (vpp .: ρ) u.
  { eapply EvalRel_mono_env;
      [ exact evM1 | apply valid_cons; [ exact Vvp | exact Vρ ]
      | apply valid_cons; [ exact Vvpp | exact Vρ ]
      | apply le_env_cons; [ exact Levp | apply le_env_refl; exact Vρ ] ]. }
  have SRrho : SubRel rho (succ vpp .: ρ) (vpp .: ρ).
  { move=> [j|]; cbn.
    - split; [ exact (Vρ j) | apply le_refl; exact (Vρ j) ].
    - split; [ exact Vsvpp | ].
      exists vpp. split; [ apply le_refl; exact Vsvpp | ].
      split; [ exact Vvpp | apply le_refl; exact Vvpp ]. }
  have evTrho : EvalRel T[rho] (vpp .: ρ) a.
  { eapply EvalRel_subst;
      [ apply valid_cons; [ exact Vsvpp | exact Vρ ]
      | apply valid_cons; [ exact Vvpp | exact Vρ ]
      | exact SRrho | exact evTc ]. }
  have Fits1 : fits (Γ ++ Core.tnat) (vpp .: ρ)
    by (eapply fits_cons with (a := tnat);
        [ apply t_nat; exact cΓ | cbn; apply le_refl | apply wt_tnat
        | exact wtvpp | exact Fρ ]).
  have TS1 : typing_subst Δ (P .: σ) (Γ ++ Core.tnat)
    by (eapply typing_subst_cons; [ asimpl; exact TP | exact TS ]).
  have TS1' : typing_subst Δ (P' .: σ') (Γ ++ Core.tnat)
    by (eapply typing_subst_cons; [ asimpl; exact TP' | exact TS' ]).
  have CS1 : ConvSub Δ (Γ ++ Core.tnat) (P .: σ) (P' .: σ')
    by (eapply ConvSub_cons; [ asimpl; exact cvPP | exact CS ]).
  have VS1 : ValSub Δ (Γ ++ Core.tnat) (P .: σ) (vpp .: ρ)
    by (eapply ValSub_cons; [ exact HPvhead | exact VS ]).
  have VS1' : ValSub Δ (Γ ++ Core.tnat) (P' .: σ') (vpp .: ρ)
    by (eapply ValSub_cons; [ exact HPv'head | exact VS' ]).
  have EVS1 : EqValSub Δ (Γ ++ Core.tnat) (P .: σ) (P' .: σ') (vpp .: ρ)
    by (eapply EqValSub_cons; [ exact HPPhead | exact EVS ]).
  have [_ eqBr] :=
    SM1 (vpp .: ρ) m Δ (P .: σ) (P' .: σ') TS1 TS1' CS1 Fits1
        VS1 VS1' EVS1 CΔ u a WT evM1' evTrho.
  (* ---- 7. the motive transports ---- *)
  have TS2 : typing_subst Δ (Core.succ P .: σ) (Γ ++ Core.tnat)
    by (eapply typing_subst_cons; [ asimpl; exact TsP | exact TS ]).
  have TS2' : typing_subst Δ (M[σ] .: σ) (Γ ++ Core.tnat)
    by (eapply typing_subst_cons; [ asimpl; exact TMσ | exact TS ]).
  have CS2 : ConvSub Δ (Γ ++ Core.tnat) (Core.succ P .: σ) (M[σ] .: σ)
    by (eapply ConvSub_cons;
        [ asimpl; apply c_sym; exact cvM | exact (ConvSub_refl TS) ]).
  have Fits2 : fits (Γ ++ Core.tnat) (succ vpp .: ρ)
    by (eapply fits_cons with (a := tnat);
        [ apply t_nat; exact cΓ | cbn; apply le_refl | apply wt_tnat
        | exact wtsvpp | exact Fρ ]).
  have VS2 : ValSub Δ (Γ ++ Core.tnat) (Core.succ P .: σ) (succ vpp .: ρ)
    by (eapply ValSub_cons; [ exact HPhead | exact VS ]).
  have VS2' : ValSub Δ (Γ ++ Core.tnat) (M[σ] .: σ) (succ vpp .: ρ)
    by (eapply ValSub_cons; [ exact HMhead | exact VS ]).
  have EVS2 : EqValSub Δ (Γ ++ Core.tnat) (Core.succ P .: σ) (M[σ] .: σ)
                (succ vpp .: ρ)
    by (eapply EqValSub_cons; [ exact HEhead | exact (ValSub_EqValSub VS) ]).
  have WTa : wt a tuniv := wt_ty_tuniv WT.
  have evU2 : EvalRel Core.tuniv (succ vpp .: ρ) tuniv by (cbn; apply le_refl).
  have [_ eqT] :=
    STT (succ vpp .: ρ) m Δ (Core.succ P .: σ) (M[σ] .: σ) TS2 TS2' CS2 Fits2
        VS2 VS2' EVS2 CΔ a tuniv WTa evTc evU2.
  have cvTT : conv Δ T[Core.succ P .: σ] T[M[σ] .: σ] Core.tuniv
    := subst_conv_cross TT CΔ TS2 TS2' CS2.
  (* the σ'-side motive conversion, and the cross-substitution one *)
  have TS3 : typing_subst Δ (Core.succ P' .: σ') (Γ ++ Core.tnat)
    by (eapply typing_subst_cons; [ asimpl; exact TsP' | exact TS' ]).
  have TS3' : typing_subst Δ (M[σ'] .: σ') (Γ ++ Core.tnat)
    by (eapply typing_subst_cons; [ asimpl; exact TMσ' | exact TS' ]).
  have CS3 : ConvSub Δ (Γ ++ Core.tnat) (Core.succ P' .: σ') (M[σ'] .: σ')
    by (eapply ConvSub_cons;
        [ asimpl; apply c_sym; exact cvM' | exact (ConvSub_refl TS') ]).
  have cvTT' : conv Δ T[Core.succ P' .: σ'] T[M[σ'] .: σ'] Core.tuniv
    := subst_conv_cross TT CΔ TS3 TS3' CS3.
  have cvMx : conv Δ M[σ] M[σ'] Core.tnat.
  { move: (subst_conv_cross TM CΔ TS TS' CS) => hh. asimpl in hh. exact hh. }
  have CSx : ConvSub Δ (Γ ++ Core.tnat) (M[σ] .: σ) (M[σ'] .: σ')
    by (eapply ConvSub_cons; [ asimpl; exact cvMx | exact CS ]).
  have cvTcross : conv Δ T[M[σ] .: σ] T[M[σ'] .: σ'] Core.tuniv
    := subst_conv_cross TT CΔ TS2' TS3' CSx.
  (* ---- 8. syntactic pieces at σ and σ' ---- *)
  have TTσ : typing (Δ ++ Core.tnat) T[⇑ σ] Core.tuniv.
  { exact (@subst_cod_typing n Γ Core.tnat T m Δ σ
             ltac:(apply t_nat; exact cΓ) TT TS CΔ). }
  have TTσ' : typing (Δ ++ Core.tnat) T[⇑ σ'] Core.tuniv.
  { exact (@subst_cod_typing n Γ Core.tnat T m Δ σ'
             ltac:(apply t_nat; exact cΓ) TT TS' CΔ). }
  have TM0σ : typing Δ M0[σ] (T[⇑ σ][Core.zero..]).
  { move: (substitution_tm _ M0 (T[Core.zero..]) _ σ TM0 TS CΔ) => hh.
    asimpl in hh. asimpl. exact hh. }
  have TM0σ' : typing Δ M0[σ'] (T[⇑ σ'][Core.zero..]).
  { move: (substitution_tm _ M0 (T[Core.zero..]) _ σ' TM0 TS' CΔ) => hh.
    asimpl in hh. asimpl. exact hh. }
  have CΔn : ctx (Δ ++ Core.tnat)
    by (eapply c_cons; [ exact CΔ | apply t_nat; exact CΔ ]).
  have TSl : typing_subst (Δ ++ Core.tnat) (⇑ σ) (Γ ++ Core.tnat).
  { exact (@typing_subst_lift m Δ n σ Γ Core.tnat CΔn TS). }
  have TSl' : typing_subst (Δ ++ Core.tnat) (⇑ σ') (Γ ++ Core.tnat).
  { exact (@typing_subst_lift m Δ n σ' Γ Core.tnat CΔn TS'). }
  have TM1σ : typing (Δ ++ Core.tnat) M1[⇑ σ] (T[⇑ σ])[rho].
  { rewrite rho_subst_comm.
    exact (substitution_tm _ M1 (T[rho]) _ (⇑ σ) TM1 TSl CΔn). }
  have TM1σ' : typing (Δ ++ Core.tnat) M1[⇑ σ'] (T[⇑ σ'])[rho].
  { rewrite rho_subst_comm.
    exact (substitution_tm _ M1 (T[rho]) _ (⇑ σ') TM1 TSl' CΔn). }
  (* ---- 9. assemble ---- *)
  move=> RB Hrank.
  have cvTs : conv Δ (T[⇑ σ][(Core.succ P)..]) (T[⇑ σ][M[σ]..]) Core.tuniv.
  { rewrite -(subst_cons_eq T (Core.succ P) σ) -(subst_cons_eq T M[σ] σ).
    exact cvTT. }
  have cvTs' : conv Δ (T[⇑ σ'][(Core.succ P')..]) (T[⇑ σ'][M[σ']..]) Core.tuniv.
  { rewrite -(subst_cons_eq T (Core.succ P') σ') -(subst_cons_eq T M[σ'] σ').
    exact cvTT'. }
  have cvTx : conv Δ (T[⇑ σ'][M[σ']..]) (T[⇑ σ][M[σ]..]) Core.tuniv.
  { rewrite -(subst_cons_eq T M[σ'] σ') -(subst_cons_eq T M[σ] σ).
    apply c_sym. exact cvTcross. }
  have EBrM : EqVal RB Δ (M1[⇑ σ][P..]) (M1[⇑ σ'][P'..]) (T[⇑ σ][M[σ]..]) WT.
  { eapply EqVal_EqVal_fwd;
      [ cbn in Hrank; lia | cbn in Hrank; lia | exact cvTs
      | move: (eqBr RB Hrank);
        rewrite rho_subst_cons (subst_cons_eq M1 P σ) (subst_cons_eq M1 P' σ')
                (subst_cons_eq T (Core.succ P) σ); done
      | rewrite -(subst_cons_eq T (Core.succ P) σ) -(subst_cons_eq T M[σ] σ);
        eapply EqVal_EqValTy;
        exact (eqT (S RB) ltac:(cbn in Hrank |- *; lia)) ]. }
  have HRstep : HeadRed (Core.ncase M M0 M1)[σ] (M1[⇑ σ][P..]).
  { cbn. eapply relations.ms_app;
      [ eapply HeadRed_ncase; exact HRs
      | eapply ms_trans; [ apply hr_succ | apply ms_refl ] ]. }
  have HRstep' : HeadRed (Core.ncase M M0 M1)[σ'] (M1[⇑ σ'][P'..]).
  { cbn. eapply relations.ms_app;
      [ eapply HeadRed_ncase; exact HRs'
      | eapply ms_trans; [ apply hr_succ | apply ms_refl ] ]. }
  have cvStep : conv Δ (Core.ncase M M0 M1)[σ] (M1[⇑ σ][P..]) (T[⇑ σ][M[σ]..]).
  { cbn. eapply c_trans.
    - eapply c_ncase;
        [ exact TTσ | exact cvM | apply c_refl; exact TM0σ | apply c_refl; exact TM1σ ].
    - eapply c_conv;
        [ eapply c_ncase_S; [ exact TTσ | exact TP | exact TM0σ | exact TM1σ ]
        | exact cvTs ]. }
  have cvStep' : conv Δ (Core.ncase M M0 M1)[σ'] (M1[⇑ σ'][P'..]) (T[⇑ σ][M[σ]..]).
  { eapply c_conv; [ | exact cvTx ]. cbn. eapply c_trans.
    - eapply c_ncase;
        [ exact TTσ' | exact cvM' | apply c_refl; exact TM0σ' | apply c_refl; exact TM1σ' ].
    - eapply c_conv;
        [ eapply c_ncase_S; [ exact TTσ' | exact TP' | exact TM0σ' | exact TM1σ' ]
        | exact cvTs' ]. }
  have EQg : (T[M..])[σ] = T[⇑ σ][M[σ]..] by (asimpl; reflexivity).
  rewrite EQg.
  eapply EqVal_headred_expand;
    [ exact HRstep | exact HRstep' | exact cvStep | exact cvStep' | exact EBrM ].
Qed.

(** The [Val] conjunct of [st_case], assembled: the [ncase] semantics selects
    the scrutinee's value, which is either [bot] (the whole case is [bot]),
    [zero] (zero branch) or a successor (successor branch). *)
Lemma st_case_Val (T : Tm (S n)) M M0 M1
  (TT : typing (Γ ++ Core.tnat) T Core.tuniv)
  (TM : typing Γ M Core.tnat)
  (TM0 : typing Γ M0 (T[Core.zero..]))
  (TM1 : typing (Γ ++ Core.tnat) M1 T[rho])
  (STT : semantic_typing (Γ ++ Core.tnat) T Core.tuniv)
  (SM : semantic_typing Γ M Core.tnat)
  (SM0 : semantic_typing Γ M0 (T[Core.zero..]))
  (SM1 : semantic_typing (Γ ++ Core.tnat) M1 T[rho])
  ρ m (Δ : Ctx m) (σ σ' : Sub n m)
  (TS : typing_subst Δ σ Γ) (TS' : typing_subst Δ σ' Γ) (CS : ConvSub Δ Γ σ σ')
  (Fρ : fits Γ ρ) (VS : ValSub Δ Γ σ ρ) (VS' : ValSub Δ Γ σ' ρ)
  (EVS : EqValSub Δ Γ σ σ' ρ) (CΔ : ctx Δ) u a (WT : wt u a)
  (evNcase : EvalRel (Core.ncase M M0 M1) ρ u)
  (evT : EvalRel T[M..] ρ a) :
  forall RB, max (rk u) (rk a) < RB ->
    Val RB Δ (Core.ncase M M0 M1)[σ] (T[M..])[σ] WT.
Proof.
  cbn in evNcase. move: evNcase => [w [evMw Hbr]].
  destruct w as [ | | | | vp | b0 f0 | g0 ]; cbn in Hbr; try done.
  - (* scrutinee is [bot]: so is the result *)
    move: Hbr => [Vu Leu].
    have Eu : u = bot by (apply le_bot_inv; exact Leu).
    move=> RB Hrank. subst u. apply Val_Bot.
  - (* scrutinee is [zero] *)
    eapply st_case_Val_zero; eassumption.
  - (* scrutinee is a successor *)
    eapply st_case_Val_succ; eassumption.
Qed.

(* t_nrec: T : (Γ ++ tnat) ⊢ tuniv i, M0 : T[zero..], M1 : tpi tnat (tpi T U⟨↑⟩)
   ⟹ nrec T M0 M1 : tpi tnat T *)
(*
Lemma st_nrec (T U : Tm (S n)) M0 M1 :
  typing (Γ ++ Core.tnat) T Core.tuniv ->
  typing Γ M0 (T[Core.zero..]) ->
  U = T[rho] ->
  typing Γ M1 (Core.tpi Core.tnat (Core.tpi T U⟨↑⟩)) ->
  semantic_typing (Γ ++ Core.tnat) T Core.tuniv ->
  semantic_typing Γ M0 (T[Core.zero..]) ->
  semantic_typing Γ M1 (Core.tpi Core.tnat (Core.tpi T U⟨↑⟩)) ->
(* ------------------------- *)
  semantic_typing Γ (Core.nrec T M0 M1) (Core.tpi Core.tnat T).
*)

(* t_tpi: A : tuniv i, (Γ ++ A) ⊢ B : tuniv i ⟹ tpi A B : tuniv i *)
(* The Pi-type edge bundles (Agda Pi.agda / VE.agda: adequacy of [Pi A B : U]).
   Each builds the [ValTy]/[EqValTy] structure of the Pi type code [tpi b f]:
   [HeadRed]-refl, the syntactic [typing] of [A[σ]]/[B[⇑σ]] (substitution_tm),
   [valid (tpi b f)] (from WT), the domain [Val]/[EqVal] (from the domain IH
   STA), and the codomain *type* edges [PiEdgeVal]/[PiEdgeEq] (Val conjunct) /
   [PiEdgeEqTy] (EqVal conjunct) built from the codomain IH STB with an extended
   substitution.  ADMITTED: the codomain edges rest on the same domain-type
   [Sup] transport (the [ValTy_Sup] family, Aborted) and the [subst1_subst_comm]
   autosubst gap as st_app/st_abs.  See [[finelt-adequacy-coq-gotchas]]. *)

(* The two codomain *type* edges of the Pi type, built from the codomain IH
   [STB] applied at an extended substitution.  These are the genuinely-hard
   part (extended [ValSub] via [ValSub_cons] + the domain-[Sup] transport +
   [subst1_subst_comm]); ADMITTED here so the surrounding [ValTy] assembly is
   real.  PiEdgeVal: any domain argument gives a valid codomain type;
   PiEdgeEq: convertible arguments give equal codomain types. *)
Lemma tpi_PiEdgeVal (A : Tm n) (B : Tm (S n))
  (TA : typing Γ A Core.tuniv) (TB : typing (Γ ++ A) B Core.tuniv)
  (STA : semantic_typing Γ A Core.tuniv)
  (STB : semantic_typing (Γ ++ A) B Core.tuniv)
  ρ m (Δ : Ctx m) (σ : Sub n m)
  (TS : typing_subst Δ σ Γ) (Fρ : fits Γ ρ) (VS : ValSub Δ Γ σ ρ) (CΔ : ctx Δ)
  b f (WT : wt (tpi b f) tuniv)
  (evAN : EvalRel (Core.tpi A B) ρ (tpi b f)) RB
  (Hguard : max (rk (tpi b f)) (rk tuniv) < S RB) :
  PiEdgeVal RB Δ A[σ] B[⇑ σ] WT.
(* Canonical-fuel design (above-rank [Hguard]): with the leaf [ValSub] guarded
   to above-rank fuels, the edge's single-fuel argument [VN] lifts to all
   above-rank fuels via [Val_fuel_any], which is exactly what [ValSub_cons]
   (via [dom_transport]) now needs.  Structure: extract the body eval from the
   [EvalRel_fun B] in [evAN]; push it down to the Selection value-join [v]
   ([EvalRel_down] using [Selection_le_app]); lift the env value to [u]
   ([EvalRel_mono_env]); build the extended [ValSub] ([dom_transport]+
   [ValSub_cons]); apply the codomain IH [STB] at [(N.:σ)]/[(u.:ρ)]; rewrite
   [subst_cons_eq].  Rests on the admitted [dom_transport]/[subst_cons_eq]. *)
Proof.
  have Vρ : valid_env ρ := fits_valid_env Fρ.
  cbn in Hguard.
  cbn [Rec.PiEdgeVal].
  move=> u v Sel WT0 N TN VN.
  (* unfold the [EvalRel] of the Pi type *)
  move: (evAN) => Hpi. cbn in Hpi.
  move: Hpi => [Vb [Vf [evAdom [a' [evAdom' EFun]]]]].
  have Vu : valid u := wt_valid_tm WT0.
  (* a [bot] value-join short-circuits via [Val_Bot]; this also discharges the
     rank-1 ([tuniv]) fuel boundary, where the off-by-one between the edge fuel
     [RB] and the surrounding [ValTy] fuel [S RB] would otherwise bite. *)
  destruct (is_bot v) eqn:Bv.
  { have Ev : v = bot by (apply is_bot_eq; rewrite Bv). subst v. apply Val_Bot. }
  have RPv : 1 <= rk v := rk_pos Bv.
  have RKu : rk u <= rk_fun f := rk_Selection_key Sel.
  have RKv : rk v <= rk_fun f := rk_Selection_val Sel.
  set WT_ := (wt_Selection_codU WT Sel).
  have Vv : valid v := wt_valid_tm WT_.
  (* lift the single-fuel argument to all above-rank fuels *)
  have VNall : forall RB0, max (rk u) (rk b) < RB0 -> Val RB0 Δ N A[σ] WT0.
  { move=> RB0 Hr0. eapply (Val_fuel_any (k := RB)); [ lia | lia | lia | lia | exact VN ]. }
  (* the [hyp0] premise of [ValSub_cons], via the domain-[Sup] transport *)
  have HYP0 : forall u0, valid u0 -> le u0 u -> forall a0 (h0 : wt u0 a0),
      EvalRel A ρ a0 -> forall RB0, max (rk u0) (rk a0) < RB0 -> Val RB0 Δ N A[σ] h0.
  { exact (dom_transport (A := A) STA Fρ TS VS CΔ (ρ := ρ) (Δ := Δ) (σ := σ) (N := N)
             (b := b) (u' := u) (WTu' := WT0) evAdom VNall). }
  have VScons : ValSub Δ (Γ ++ A) (N .: σ) (u .: ρ).
  { eapply ValSub_cons; [ exact HYP0 | exact VS ]. }
  (* extract the body evaluation and bring it to env value [u] at result [v] *)
  have leV : le v (app f u)
    by (eapply Selection_le_app; [ exact Vf | exact Vf | apply le_fun_refl; exact Vf | exact Vu | exact Sel ]).
  destruct (EFun u (app f u) Vu erefl) as [x [WTx [Lexu EBxa]]].
  have Vx : valid x := wt_valid_tm WTx.
  have EBxv : EvalRel B (x .: ρ) v.
  { eapply EvalRel_down;
      [ apply valid_cons; [ exact Vx | exact Vρ ] | exact Vv | exact EBxa | exact leV ]. }
  have EBuv : EvalRel B (u .: ρ) v.
  { eapply EvalRel_mono_env;
      [ exact EBxv
      | apply valid_cons; [ exact Vx | exact Vρ ]
      | apply valid_cons; [ exact Vu | exact Vρ ]
      | apply le_env_cons; [ exact Lexu | apply le_env_refl; exact Vρ ] ]. }
  have evU' : EvalRel Core.tuniv (u .: ρ) tuniv by (cbn; apply le_refl).
  (* extended substitution typings *)
  have TScons : typing_subst Δ (N .: σ) (Γ ++ A)
    by (eapply typing_subst_cons; [ exact TN | exact TS ]).
  have Fits : fits (Γ ++ A) (u .: ρ)
    by (eapply fits_cons; [ exact TA | exact evAdom | eapply wt_ty_tuniv; exact WT0 | exact WT0 | exact Fρ ]).
  (* apply the codomain IH at the extended substitution *)
  have [valB _] :=
    STB (u .: ρ) m Δ (N .: σ) (N .: σ) TScons TScons (ConvSub_refl TScons)
        Fits VScons VScons (ValSub_EqValSub VScons) CΔ v tuniv WT_ EBuv evU'.
  have HrV : max (rk v) (rk tuniv) < RB by (cbn; lia).
  move: (valB RB HrV) => HvB.
  rewrite (subst_cons_eq B N σ) in HvB.
  exact HvB.
Qed.

Lemma tpi_PiEdgeEq (A : Tm n) (B : Tm (S n))
  (TA : typing Γ A Core.tuniv) (TB : typing (Γ ++ A) B Core.tuniv)
  (STA : semantic_typing Γ A Core.tuniv)
  (STB : semantic_typing (Γ ++ A) B Core.tuniv)
  ρ m (Δ : Ctx m) (σ : Sub n m)
  (TS : typing_subst Δ σ Γ) (Fρ : fits Γ ρ) (VS : ValSub Δ Γ σ ρ) (CΔ : ctx Δ)
  b f (WT : wt (tpi b f) tuniv)
  (evAN : EvalRel (Core.tpi A B) ρ (tpi b f)) RB
  (Hguard : max (rk (tpi b f)) (rk tuniv) < S RB) :
  PiEdgeEq RB Δ A[σ] B[⇑ σ] WT.
(* The [EqVal] sibling of [tpi_PiEdgeVal].  The codomain IH [STB]'s *EqVal*
   conjunct relates [B[σ1]] and [B[σ2]] for two substitutions, so we apply it
   at [σ1 := N1.:σ] / [σ2 := N2.:σ].  Building the extended [EqValSub] uses the
   [EqVal] domain transport [dom_transport_eq]; the two [ValSub]s use the
   [Val]s of [N1]/[N2] ([EqVal_Val1]/[EqVal_Val2]); typing of [N1]/[N2] comes
   from [conv_typing].  Same [v=bot] / [< S RB] boundary handling as the value
   edge.  Rests on the admitted [dom_transport]/[dom_transport_eq]/
   [subst_cons_eq]/[conv_typing]. *)
Proof.
  have Vρ : valid_env ρ := fits_valid_env Fρ.
  cbn in Hguard.
  cbn [Rec.PiEdgeEq].
  move=> u v Sel WT0 N1 N2 CN EV.
  move: (evAN) => Hpi. cbn in Hpi.
  move: Hpi => [Vb [Vf [evAdom [a' [evAdom' EFun]]]]].
  have Vu : valid u := wt_valid_tm WT0.
  destruct (is_bot v) eqn:Bv.
  { have Ev : v = bot by (apply is_bot_eq; rewrite Bv). subst v. apply EqVal_Bot. }
  have RPv : 1 <= rk v := rk_pos Bv.
  have RKu : rk u <= rk_fun f := rk_Selection_key Sel.
  have RKv : rk v <= rk_fun f := rk_Selection_val Sel.
  set WT_ := (wt_Selection_codU WT Sel).
  have Vv : valid v := wt_valid_tm WT_.
  (* typing of the two arguments from the conversion *)
  have [TN1 TN2] := conv_typing CN.
  (* [Val]/[EqVal] of the arguments at the single edge fuel, then lifted *)
  have VN1 : Val RB Δ N1 A[σ] WT0 by (eapply EqVal_Val1; exact EV).
  have VN2 : Val RB Δ N2 A[σ] WT0 by (eapply EqVal_Val2; exact EV).
  have VN1all : forall RB0, max (rk u) (rk b) < RB0 -> Val RB0 Δ N1 A[σ] WT0.
  { move=> RB0 Hr0. eapply (Val_fuel_any (k := RB)); [ lia | lia | lia | lia | exact VN1 ]. }
  have VN2all : forall RB0, max (rk u) (rk b) < RB0 -> Val RB0 Δ N2 A[σ] WT0.
  { move=> RB0 Hr0. eapply (Val_fuel_any (k := RB)); [ lia | lia | lia | lia | exact VN2 ]. }
  have EVall : forall RB0, max (rk u) (rk b) < RB0 -> EqVal RB0 Δ N1 N2 A[σ] WT0.
  { move=> RB0 Hr0. eapply (EqVal_fuel_any (k := RB)); [ lia | lia | lia | lia | exact EV ]. }
  (* the three [hyp0] premises (two [ValSub_cons], one [EqValSub_cons]) *)
  have HYP1 : forall u0, valid u0 -> le u0 u -> forall a0 (h0 : wt u0 a0),
      EvalRel A ρ a0 -> forall RB0, max (rk u0) (rk a0) < RB0 -> Val RB0 Δ N1 A[σ] h0.
  { exact (dom_transport (A := A) STA Fρ TS VS CΔ (ρ := ρ) (Δ := Δ) (σ := σ) (N := N1)
             (b := b) (u' := u) (WTu' := WT0) evAdom VN1all). }
  have HYP2 : forall u0, valid u0 -> le u0 u -> forall a0 (h0 : wt u0 a0),
      EvalRel A ρ a0 -> forall RB0, max (rk u0) (rk a0) < RB0 -> Val RB0 Δ N2 A[σ] h0.
  { exact (dom_transport (A := A) STA Fρ TS VS CΔ (ρ := ρ) (Δ := Δ) (σ := σ) (N := N2)
             (b := b) (u' := u) (WTu' := WT0) evAdom VN2all). }
  have HYPE : forall u0, valid u0 -> le u0 u -> forall a0 (h0 : wt u0 a0),
      EvalRel A ρ a0 -> forall RB0, max (rk u0) (rk a0) < RB0 -> EqVal RB0 Δ N1 N2 A[σ] h0.
  { exact (dom_transport_eq (A := A) STA Fρ TS VS CΔ (ρ := ρ) (Δ := Δ) (σ := σ) (N1 := N1) (N2 := N2)
             (b := b) (u' := u) (WTu' := WT0) evAdom EVall). }
  have VS1 : ValSub Δ (Γ ++ A) (N1 .: σ) (u .: ρ)
    by (eapply ValSub_cons; [ exact HYP1 | exact VS ]).
  have VS2 : ValSub Δ (Γ ++ A) (N2 .: σ) (u .: ρ)
    by (eapply ValSub_cons; [ exact HYP2 | exact VS ]).
  have EVS' : EqValSub Δ (Γ ++ A) (N1 .: σ) (N2 .: σ) (u .: ρ)
    by (eapply EqValSub_cons; [ exact HYPE | exact (ValSub_EqValSub VS) ]).
  (* extract the body evaluation and bring it to env value [u] at result [v] *)
  have leV : le v (app f u)
    by (eapply Selection_le_app; [ exact Vf | exact Vf | apply le_fun_refl; exact Vf | exact Vu | exact Sel ]).
  destruct (EFun u (app f u) Vu erefl) as [x [WTx [Lexu EBxa]]].
  have Vx : valid x := wt_valid_tm WTx.
  have EBxv : EvalRel B (x .: ρ) v.
  { eapply EvalRel_down;
      [ apply valid_cons; [ exact Vx | exact Vρ ] | exact Vv | exact EBxa | exact leV ]. }
  have EBuv : EvalRel B (u .: ρ) v.
  { eapply EvalRel_mono_env;
      [ exact EBxv
      | apply valid_cons; [ exact Vx | exact Vρ ]
      | apply valid_cons; [ exact Vu | exact Vρ ]
      | apply le_env_cons; [ exact Lexu | apply le_env_refl; exact Vρ ] ]. }
  have evU' : EvalRel Core.tuniv (u .: ρ) tuniv by (cbn; apply le_refl).
  (* extended substitution typings / conv *)
  have TS1 : typing_subst Δ (N1 .: σ) (Γ ++ A)
    by (eapply typing_subst_cons; [ exact TN1 | exact TS ]).
  have TS2 : typing_subst Δ (N2 .: σ) (Γ ++ A)
    by (eapply typing_subst_cons; [ exact TN2 | exact TS ]).
  have CS : ConvSub Δ (Γ ++ A) (N1 .: σ) (N2 .: σ)
    by (eapply ConvSub_cons; [ exact CN | exact (ConvSub_refl TS) ]).
  have Fits : fits (Γ ++ A) (u .: ρ)
    by (eapply fits_cons; [ exact TA | exact evAdom | eapply wt_ty_tuniv; exact WT0 | exact WT0 | exact Fρ ]).
  (* apply the codomain IH at the two extended substitutions, [EqVal] conjunct *)
  have [_ eqvalB] :=
    STB (u .: ρ) m Δ (N1 .: σ) (N2 .: σ) TS1 TS2 CS Fits VS1 VS2 EVS' CΔ v tuniv WT_ EBuv evU'.
  have HrV : max (rk v) (rk tuniv) < RB by (cbn; lia).
  move: (eqvalB RB HrV) => HvB.
  rewrite (subst_cons_eq B N1 σ) (subst_cons_eq B N2 σ) in HvB.
  exact HvB.
Qed.

(* The codomain *type-equality* edge of a Pi type ([PiEdgeEqTy]): a single
   argument [P] gives EQUAL codomain types under the two base substitutions
   [σ]/[σ'].  Like [tpi_PiEdgeVal]/[tpi_PiEdgeEq] but the two sides of the
   [EqVal] differ in the BASE substitution (not the argument), so we apply the
   codomain IH [STB]'s EqVal conjunct at [σ1 := P.:σ] / [σ2 := P.:σ'].  The
   [ValSub] for [σ'] needs [Val P] at [A[σ']], obtained from [Val P : A[σ]] by
   [Val_ty_conv] along [subst_conv_cross]. *)
Lemma tpi_PiEdgeEqTy (A : Tm n) (B : Tm (S n))
  (TA : typing Γ A Core.tuniv) (TB : typing (Γ ++ A) B Core.tuniv)
  (STA : semantic_typing Γ A Core.tuniv)
  (STB : semantic_typing (Γ ++ A) B Core.tuniv)
  ρ m (Δ : Ctx m) (σ σ' : Sub n m)
  (TS : typing_subst Δ σ Γ) (TS' : typing_subst Δ σ' Γ) (CS : ConvSub Δ Γ σ σ')
  (Fρ : fits Γ ρ) (VS : ValSub Δ Γ σ ρ) (VS' : ValSub Δ Γ σ' ρ)
  (EVS : EqValSub Δ Γ σ σ' ρ) (CΔ : ctx Δ)
  b f (WT : wt (tpi b f) tuniv)
  (evAN : EvalRel (Core.tpi A B) ρ (tpi b f)) RB
  (Hguard : max (rk (tpi b f)) (rk tuniv) < S RB) :
  PiEdgeEqTy RB Δ A[σ] B[⇑ σ] B[⇑ σ'] WT.
Proof.
  have Vρ : valid_env ρ := fits_valid_env Fρ.
  have convAA' : conv Δ A[σ] A[σ'] Core.tuniv :=
    subst_conv_cross TA CΔ TS TS' CS.
  cbn in Hguard.
  cbn [Rec.PiEdgeEqTy].
  move=> u v Sel WTu P TP VP.
  move: (evAN) => Hpi. cbn in Hpi.
  move: Hpi => [Vb [Vf [evAdom [a' [evAdom' EFun]]]]].
  have Vu : valid u := wt_valid_tm WTu.
  destruct (is_bot v) eqn:Bv.
  { have Ev : v = bot by (apply is_bot_eq; rewrite Bv). subst v. apply EqVal_Bot. }
  have RPv : 1 <= rk v := rk_pos Bv.
  have RKu : rk u <= rk_fun f := rk_Selection_key Sel.
  have RKv : rk v <= rk_fun f := rk_Selection_val Sel.
  set WT_ := (wt_Selection_codU WT Sel).
  have Vv : valid v := wt_valid_tm WT_.
  have TP' : typing Δ P A[σ'] by (eapply t_conv; [ exact TP | exact convAA' ]).
  have evU : EvalRel Core.tuniv ρ tuniv by (cbn; apply le_refl).
  (* the domain semantic type-equality [A[σ] ≡ A[σ']], from the domain IH [STA] *)
  have [_ eqA] :=
    STA ρ m Δ σ σ' TS TS' CS Fρ VS VS' EVS CΔ b tuniv (wt_ty_tuniv WTu) evAdom evU.
  (* [Val] of [P] (both base types), [EqVal P P], all lifted to above-rank fuels *)
  have VPall : forall RB0, max (rk u) (rk b) < RB0 -> Val RB0 Δ P A[σ] WTu.
  { move=> RB0 Hr0. eapply (Val_fuel_any (k := RB)); [ lia | lia | lia | lia | exact VP ]. }
  (* retype [Val P : A[σ]] to [A[σ']] via the *semantic* type-equality
     ([Val_EqVal_fwd]) — the Agda-faithful route (no syntactic-conv transport) *)
  have VPall' : forall RB0, max (rk u) (rk b) < RB0 -> Val RB0 Δ P A[σ'] WTu.
  { move=> RB0 Hr0. eapply Val_EqVal_fwd;
      [ cbn in Hr0; lia | cbn in Hr0; lia | exact convAA' | exact (VPall RB0 Hr0) | ].
    eapply EqVal_EqValTy. eapply (eqA (S RB0)). cbn in Hr0 |- *; lia. }
  have EVall : forall RB0, max (rk u) (rk b) < RB0 -> EqVal RB0 Δ P P A[σ] WTu.
  { move=> RB0 Hr0. eapply Val_EqVal; exact (VPall RB0 Hr0). }
  have HYP1 := dom_transport (A := A) STA Fρ TS VS CΔ (ρ := ρ) (Δ := Δ) (σ := σ) (N := P)
                 (b := b) (u' := u) (WTu' := WTu) evAdom VPall.
  have HYP2 := dom_transport (A := A) STA Fρ TS' VS' CΔ (ρ := ρ) (Δ := Δ) (σ := σ') (N := P)
                 (b := b) (u' := u) (WTu' := WTu) evAdom VPall'.
  have HYPE := dom_transport_eq (A := A) STA Fρ TS VS CΔ (ρ := ρ) (Δ := Δ) (σ := σ) (N1 := P) (N2 := P)
                 (b := b) (u' := u) (WTu' := WTu) evAdom EVall.
  have VS1 : ValSub Δ (Γ ++ A) (P .: σ) (u .: ρ)
    by (eapply ValSub_cons; [ exact HYP1 | exact VS ]).
  have VS2 : ValSub Δ (Γ ++ A) (P .: σ') (u .: ρ)
    by (eapply ValSub_cons; [ exact HYP2 | exact VS' ]).
  have EVS' : EqValSub Δ (Γ ++ A) (P .: σ) (P .: σ') (u .: ρ)
    by (eapply EqValSub_cons; [ exact HYPE | exact EVS ]).
  have leV : le v (app f u)
    by (eapply Selection_le_app; [ exact Vf | exact Vf | apply le_fun_refl; exact Vf | exact Vu | exact Sel ]).
  destruct (EFun u (app f u) Vu erefl) as [x [WTx [Lexu EBxa]]].
  have Vx : valid x := wt_valid_tm WTx.
  have EBxv : EvalRel B (x .: ρ) v.
  { eapply EvalRel_down;
      [ apply valid_cons; [ exact Vx | exact Vρ ] | exact Vv | exact EBxa | exact leV ]. }
  have EBuv : EvalRel B (u .: ρ) v.
  { eapply EvalRel_mono_env;
      [ exact EBxv
      | apply valid_cons; [ exact Vx | exact Vρ ]
      | apply valid_cons; [ exact Vu | exact Vρ ]
      | apply le_env_cons; [ exact Lexu | apply le_env_refl; exact Vρ ] ]. }
  have evU' : EvalRel Core.tuniv (u .: ρ) tuniv by (cbn; apply le_refl).
  have TS1 : typing_subst Δ (P .: σ) (Γ ++ A)
    by (eapply typing_subst_cons; [ exact TP | exact TS ]).
  have TS2 : typing_subst Δ (P .: σ') (Γ ++ A)
    by (eapply typing_subst_cons; [ exact TP' | exact TS' ]).
  have CS' : ConvSub Δ (Γ ++ A) (P .: σ) (P .: σ')
    by (eapply ConvSub_cons; [ eapply c_refl; exact TP | exact CS ]).
  have Fits : fits (Γ ++ A) (u .: ρ)
    by (eapply fits_cons; [ exact TA | exact evAdom | eapply wt_ty_tuniv; exact WTu | exact WTu | exact Fρ ]).
  have [_ eqvalB] :=
    STB (u .: ρ) m Δ (P .: σ) (P .: σ') TS1 TS2 CS' Fits VS1 VS2 EVS' CΔ v tuniv WT_ EBuv evU'.
  have HrV : max (rk v) (rk tuniv) < RB by (cbn; lia).
  move: (eqvalB RB HrV) => HvB.
  rewrite (subst_cons_eq B P σ) (subst_cons_eq B P σ') in HvB.
  exact HvB.
Qed.

Lemma st_tpi_Val_edge (A : Tm n) (B : Tm (S n))
  (TA : typing Γ A Core.tuniv) (TB : typing (Γ ++ A) B Core.tuniv)
  (STA : semantic_typing Γ A Core.tuniv)
  (STB : semantic_typing (Γ ++ A) B Core.tuniv)
  ρ m (Δ : Ctx m) (σ σ' : Sub n m)
  (TS : typing_subst Δ σ Γ) (TS' : typing_subst Δ σ' Γ) (CS : ConvSub Δ Γ σ σ')
  (Fρ : fits Γ ρ) (VS : ValSub Δ Γ σ ρ) (VS' : ValSub Δ Γ σ' ρ)
  (EVS : EqValSub Δ Γ σ σ' ρ) (CΔ : ctx Δ) u a (WT : wt u a)
  (evAN : EvalRel (Core.tpi A B) ρ u) (evAB : EvalRel Core.tuniv ρ a) :
  forall RB, max (rk u) (rk a) < RB -> Val RB Δ (Core.tpi A B)[σ] Core.tuniv[σ] WT.
Proof.
  have Vρ : valid_env ρ := fits_valid_env Fρ.
  (* shared substitution plumbing for the codomain typing (mirrors st_abs) *)
  move: (substitution_tm _ _ _ _ _ TA TS CΔ) => TAs. cbn in TAs.
  have CE : ctx (Δ ++ A[σ]). eapply c_cons; eauto.
  have TSE : typing_subst (Δ ++ A[σ]) (⇑ σ) (Γ ++ A). eapply typing_subst_lift; eauto.
  have TBs : typing (Δ ++ A[σ]) B[⇑ σ] Core.tuniv.
  { have CC : typing (Δ ++ A[σ]) B[⇑ σ] Core.tuniv[⇑ σ].
    eapply substitution_tm; eauto. cbn in CC. auto. }
  have evU : EvalRel Core.tuniv ρ tuniv by (cbn; apply le_refl).
  have evAN0 := evAN.            (* keep the folded [EvalRel] for the edges *)
  cbn in evAN.
  move=> RB Hrank. destruct RB; [ exact I | ].
  destruct u as [ | | | | | b f | ]; try done.
  - (* u = bot: trivial *) apply Val_Bot.
  - (* u = tpi b f *)
    move: evAN => [Vb [Vf [evAdom [a' [evAdom' EFun]]]]].
    have Eatu : a = tuniv by (inversion WT; auto).
    subst a.
    have [valA _] :=
      STA ρ m Δ σ σ' TS TS' CS Fρ VS VS' EVS CΔ b tuniv (wt_tpi_dom WT) evAdom evU.
    rewrite Val_tuniv. cbn [Rec.ValTy].
    exists A[σ], B[⇑ σ].
    (* domain Val, via [STA] above the domain rank; at the rank-1 boundary
       ([RB <= 1]) the domain code [b] must be [bot], handled by [Val_Bot]. *)
    have valDom : Val RB Δ A[σ] Core.tuniv[σ] (wt_tpi_dom WT).
    { destruct (le_lt_dec 2 RB) as [HRB|HRB].
      - eapply Val_irr; eapply valA; cbn in Hrank |- *; lia.
      - have Eb : b = bot by (apply rk_bot_inv; cbn in Hrank; lia).
        move: (wt_tpi_dom WT). rewrite Eb. move=> w. apply Val_Bot. }
    repeat split;
      [ apply ms_refl | exact TAs | exact TBs | exact (wt_valid_tm WT)
      | exact valDom | | ].
    + eapply tpi_PiEdgeVal; (try eassumption); exact Hrank.
    + eapply tpi_PiEdgeEq; (try eassumption); exact Hrank.
Qed.

Lemma st_tpi_EqVal_edge (A : Tm n) (B : Tm (S n))
  (TA : typing Γ A Core.tuniv) (TB : typing (Γ ++ A) B Core.tuniv)
  (STA : semantic_typing Γ A Core.tuniv)
  (STB : semantic_typing (Γ ++ A) B Core.tuniv)
  ρ m (Δ : Ctx m) (σ σ' : Sub n m)
  (TS : typing_subst Δ σ Γ) (TS' : typing_subst Δ σ' Γ) (CS : ConvSub Δ Γ σ σ')
  (Fρ : fits Γ ρ) (VS : ValSub Δ Γ σ ρ) (VS' : ValSub Δ Γ σ' ρ)
  (EVS : EqValSub Δ Γ σ σ' ρ) (CΔ : ctx Δ) u a (WT : wt u a)
  (evAN : EvalRel (Core.tpi A B) ρ u) (evAB : EvalRel Core.tuniv ρ a) :
  forall RB, max (rk u) (rk a) < RB -> EqVal RB Δ (Core.tpi A B)[σ] (Core.tpi A B)[σ'] Core.tuniv[σ] WT.
Proof.
  have Vρ : valid_env ρ := fits_valid_env Fρ.
  have evU : EvalRel Core.tuniv ρ tuniv by (cbn; apply le_refl).
  have evAN0 := evAN.            (* keep the folded [EvalRel] for the edges *)
  cbn in evAN.
  move=> RB Hrank. destruct RB; [ exact I | ].
  destruct u as [ | | | | | b f | ]; try done.
  - (* u = bot: trivial *) apply EqVal_Bot.
  - (* u = tpi b f *)
    move: evAN => [Vb [Vf [evAdom [a' [evAdom' EFun]]]]].
    have Eatu : a = tuniv by (inversion WT; auto). subst a.
    (* the two [ValTy]s, from the value edge at [(σ,σ)] and [(σ',σ')] *)
    have VMv : Val (S RB) Δ (Core.tpi A B)[σ] Core.tuniv[σ] WT.
    { eapply st_tpi_Val_edge; eassumption. }
    have VNv : Val (S RB) Δ (Core.tpi A B)[σ'] Core.tuniv[σ'] WT.
    { eapply st_tpi_Val_edge with (σ' := σ'); try eassumption.
      - exact (ConvSub_refl TS').
      - exact (ValSub_EqValSub VS'). }
    rewrite Val_tuniv in VMv. rewrite Val_tuniv in VNv.
    (* domain conv (syntactic) and domain EqVal (semantic, from STA) *)
    have convAA' : conv Δ A[σ] A[σ'] Core.tuniv := subst_conv_cross TA CΔ TS TS' CS.
    have codConv : conv (Δ ++ A[σ]) B[⇑ σ] B[⇑ σ'] Core.tuniv :=
      cod_subst_conv TA TB CΔ TS TS' CS.
    have [_ eqA] :=
      STA ρ m Δ σ σ' TS TS' CS Fρ VS VS' EVS CΔ b tuniv (wt_tpi_dom WT) evAdom evU.
    have eqDom : EqVal RB Δ A[σ] A[σ'] Core.tuniv (wt_tpi_dom WT).
    { destruct (le_lt_dec 2 RB) as [HRB|HRB].
      - eapply EqVal_irr; eapply eqA; cbn in Hrank |- *; lia.
      - have Eb : b = bot by (apply rk_bot_inv; cbn in Hrank; lia).
        move: (wt_tpi_dom WT). rewrite Eb. move=> w. apply EqVal_Bot. }
    rewrite EqVal_tuniv.
    split; [ exact VMv | ]. split; [ exact VNv | ].
    cbn [Rec.EqValTy].
    split; [ exact VMv | ]. split; [ exact VNv | ].
    exists A[σ], B[⇑ σ]. split; [ apply ms_refl | ].
    exists A[σ'], B[⇑ σ']. split; [ apply ms_refl | ].
    split; [ exact convAA' | ].
    split; [ exact codConv | ].
    split; [ exact (wt_valid_tm WT) | ].
    split; [ exact eqDom | ].
    eapply tpi_PiEdgeEqTy; (try eassumption); exact Hrank.
Qed.

(** Π-formation rule (Agda [adequacyV2-ty-Pi]): from semantic typing of the
    domain and codomain, the Π-type [tpi A B] is semantically a type.  The
    Selection-indexed type edges are supplied by [st_tpi_Val_edge] /
    [st_tpi_EqVal_edge] above. *)
Lemma st_tpi A B :
  typing Γ A Core.tuniv ->
  typing (Γ ++ A) B Core.tuniv ->
  semantic_typing Γ A Core.tuniv ->
  semantic_typing (Γ ++ A) B Core.tuniv ->
(* ------------------------- *)
  semantic_typing Γ (Core.tpi A B) Core.tuniv.
Proof.
  move=> TA TB STA STB.
  move=> ρ m Δ σ σ' TS TS' CS Fρ VS VS' EVS CΔ u a WT evAN evAB.
  split.
  - eapply st_tpi_Val_edge; eassumption.
  - eapply st_tpi_EqVal_edge; eassumption.
Qed.

(* The Lam-body edge bundles (Agda Lam.agda: adequacy-ty-Lam / adequacyV-ty-Lam).
   Each builds the [Selection]-indexed function edges of the lambda value:
   extract the body evaluation from [EvalRel_fun], lift via
   [EvalRel_mono_env]/[EvalRel_down], build the extended [ValSub] ([ValSub_cons])
   using the domain IH transport, apply the body IH [STM] at [Γ++A], then
   [Val_beta_expand] / [EqVal_headred_expand] across the lambda beta-redex.
   ADMITTED: these rest on the same domain-type [Sup] transport (the [ValTy_Sup]
   family, Aborted in raw_validity.v) and the autosubst [subst1_subst_comm] gap
   that the App case (st_app) isolates.  See [[finelt-adequacy-coq-gotchas]]. *)
Lemma st_abs_Val_edge (Alam A : Tm n) (B M : Tm (S n))
  (TAlam : typing Γ Alam Core.tuniv)
  (CAlam : conv Γ A Alam Core.tuniv)
  (TM : typing (Γ ++ A) M B)
  (TA : typing Γ A Core.tuniv) (TB : typing (Γ ++ A) B Core.tuniv)
  (STA : semantic_typing Γ A Core.tuniv)
  (STB : semantic_typing (Γ ++ A) B Core.tuniv)
  (STM : semantic_typing (Γ ++ A) M B)
  ρ m (Δ : Ctx m) (σ σ' : Sub n m)
  (TS : typing_subst Δ σ Γ) (TS' : typing_subst Δ σ' Γ) (CS : ConvSub Δ Γ σ σ')
  (Fρ : fits Γ ρ) (VS : ValSub Δ Γ σ ρ) (VS' : ValSub Δ Γ σ' ρ)
  (EVS : EqValSub Δ Γ σ σ' ρ) (CΔ : ctx Δ) u a (WT : wt u a)
  (evAN : EvalRel (Core.abs Alam M) ρ u) (evAB : EvalRel (Core.tpi A B) ρ a) :
  forall RB, max (rk u) (rk a) < RB -> Val RB Δ (Core.abs Alam M)[σ] (Core.tpi A B)[σ] WT.
Proof.
  have Vρ : valid_env ρ := fits_valid_env Fρ.
  have evU : EvalRel Core.tuniv ρ tuniv by (cbn; apply le_refl).
  (* the Π-code conversion stored by [ValPi]: here the type term *is* the
     Π-normal form, so it is reflexivity *)
  have CPiσ : conv Δ (Core.tpi A[σ] B[⇑ σ]) (Core.tpi A[σ] B[⇑ σ]) Core.tuniv.
  { apply c_refl.
    move: (substitution_tm _ (Core.tpi A B) Core.tuniv _ σ
             ltac:(apply t_tpi; [ exact TA | exact TB ]) TS CΔ) => hh.
    asimpl in hh. exact hh. }
  have evAN0 := evAN. have evAB0 := evAB.
  cbn in evAN. cbn in evAB.
  move=> RB Hrank. destruct RB; [ exact I | ].
  destruct u as [ | | | | | | g_val ]; try done.
  - (* u = bot *) apply Val_Bot.
  - (* u = abs g_val *)
    destruct a as [ | | | | | b f_ty | ];
      try solve [ cbn in evAB; done | exfalso; clear -WT; inversion WT ].
    move: evAN => [Vg [NBg [a_d [WTad [ERA_ad EFunM]]]]].
    move: evAB => [Vb [Vf_ty [ERA_b [a'_T [ERA_aT EFunB]]]]].
    (* the lambda's body value at the value-graph key, and the codomain type
       value at the type-graph key, both at env value [u0] *)
    have bodyM : forall u0 v0, Selection g_val u0 v0 -> valid u0 -> EvalRel M (u0 .: ρ) v0.
    { move=> u0 v0 Sel Vu0.
      have Vv0 : valid v0 := wt_valid_tm (wt_Selection_abs WT Sel).
      have leV : le v0 (app g_val u0)
        by (eapply Selection_le_app; [ exact Vg | exact Vg | apply le_fun_refl; exact Vg | exact Vu0 | exact Sel ]).
      destruct (EFunM u0 (app g_val u0) Vu0 erefl) as [x [WTx [Lex EBx]]].
      have Vx : valid x := wt_valid_tm WTx.
      have EBxv : EvalRel M (x .: ρ) v0
        by (eapply EvalRel_down; [ apply valid_cons; [ exact Vx | exact Vρ ] | exact Vv0 | exact EBx | exact leV ]).
      eapply EvalRel_mono_env;
        [ exact EBxv | apply valid_cons; [ exact Vx | exact Vρ ]
        | apply valid_cons; [ exact Vu0 | exact Vρ ]
        | apply le_env_cons; [ exact Lex | apply le_env_refl; exact Vρ ] ]. }
    have bodyB : forall u0, valid u0 -> EvalRel B (u0 .: ρ) (app f_ty u0).
    { move=> u0 Vu0.
      destruct (EFunB u0 (app f_ty u0) Vu0 erefl) as [y [WTy [Ley EBy]]].
      have Vy : valid y := wt_valid_tm WTy.
      eapply EvalRel_mono_env;
        [ exact EBy | apply valid_cons; [ exact Vy | exact Vρ ]
        | apply valid_cons; [ exact Vu0 | exact Vρ ]
        | apply le_env_cons; [ exact Ley | apply le_env_refl; exact Vρ ] ]. }
    rewrite Val_abs.
    split.
    + (* domain [ValTy] of the Pi type, from the Pi-type value edge *)
      have VTd : Val (S RB) Δ (Core.tpi A B)[σ] Core.tuniv[σ] (wt_abs_ty WT).
      { eapply st_tpi_Val_edge; try eassumption. cbn in Hrank |- *; lia. }
      rewrite Val_tuniv in VTd. exact VTd.
    + (* the function value edges *)
      exists A[σ], B[⇑ σ]. split; [ apply ms_refl | ]. split; [ exact CPiσ | ]. split.
      * (* PiAppVal *)
        cbn [Rec.PiAppVal]. move=> u0 v0 Sel WTu0 P TP VP.
        have Vu0 : valid u0 := wt_valid_tm WTu0.
        have RKu0 : rk u0 <= rk_fun g_val := rk_Selection_key Sel.
        have RKv0 : rk v0 <= rk_fun g_val := rk_Selection_val Sel.
        have RKapp : rk (app f_ty u0) <= rk_fun f_ty := rk_app f_ty u0.
        have VPall : forall RB0, max (rk u0) (rk b) < RB0 -> Val RB0 Δ P A[σ] WTu0.
        { move=> RB0 Hr0. eapply (Val_fuel_any (k := RB)); [ cbn in Hrank; lia | cbn in Hrank; lia | lia | lia | exact VP ]. }
        have HYP1 := dom_transport (A := A) STA Fρ TS VS CΔ (ρ := ρ) (Δ := Δ) (σ := σ) (N := P)
                       (b := b) (u' := u0) (WTu' := WTu0) ERA_b VPall.
        have VS1 : ValSub Δ (Γ ++ A) (P .: σ) (u0 .: ρ)
          by (eapply ValSub_cons; [ exact HYP1 | exact VS ]).
        have TS1 : typing_subst Δ (P .: σ) (Γ ++ A)
          by (eapply typing_subst_cons; [ exact TP | exact TS ]).
        have Fits : fits (Γ ++ A) (u0 .: ρ)
          by (eapply fits_cons; [ exact TA | exact ERA_b | eapply wt_ty_tuniv; exact WTu0 | exact WTu0 | exact Fρ ]).
        have [valBody _] :=
          STM (u0 .: ρ) m Δ (P .: σ) (P .: σ) TS1 TS1 (ConvSub_refl TS1)
              Fits VS1 VS1 (ValSub_EqValSub VS1) CΔ v0 (app f_ty u0)
              (wt_Selection_abs WT Sel) (bodyM u0 v0 Sel Vu0) (bodyB u0 Vu0).
        have HrB : max (rk v0) (rk (app f_ty u0)) < RB by (cbn in Hrank; lia).
        move: (valBody RB HrB) => HvB.
        rewrite (subst_cons_eq M P σ) (subst_cons_eq B P σ) in HvB.
        eapply Val_beta_expand;
          [ eapply ms_trans; [ apply hr_beta | apply ms_refl ]
          | eapply beta_step_conv;
              [ exact TAlam | exact TA | exact CAlam | exact TB | exact TM
              | exact TS | exact CΔ | exact TP ]
          | exact HvB ].
      * (* PiAppEq *)
        cbn [Rec.PiAppEq]. move=> u0 v0 Sel WTu0 N1 N2 CN EV.
        have Vu0 : valid u0 := wt_valid_tm WTu0.
        have RKu0 : rk u0 <= rk_fun g_val := rk_Selection_key Sel.
        have RKv0 : rk v0 <= rk_fun g_val := rk_Selection_val Sel.
        have RKapp : rk (app f_ty u0) <= rk_fun f_ty := rk_app f_ty u0.
        have [TN1 TN2] := conv_typing CN.
        have VN1 : Val RB Δ N1 A[σ] WTu0 by (eapply EqVal_Val1; exact EV).
        have VN2 : Val RB Δ N2 A[σ] WTu0 by (eapply EqVal_Val2; exact EV).
        have VN1all : forall RB0, max (rk u0) (rk b) < RB0 -> Val RB0 Δ N1 A[σ] WTu0.
        { move=> RB0 Hr0. eapply (Val_fuel_any (k := RB)); [ cbn in Hrank; lia | cbn in Hrank; lia | lia | lia | exact VN1 ]. }
        have VN2all : forall RB0, max (rk u0) (rk b) < RB0 -> Val RB0 Δ N2 A[σ] WTu0.
        { move=> RB0 Hr0. eapply (Val_fuel_any (k := RB)); [ cbn in Hrank; lia | cbn in Hrank; lia | lia | lia | exact VN2 ]. }
        have EVall : forall RB0, max (rk u0) (rk b) < RB0 -> EqVal RB0 Δ N1 N2 A[σ] WTu0.
        { move=> RB0 Hr0. eapply (EqVal_fuel_any (k := RB)); [ cbn in Hrank; lia | cbn in Hrank; lia | lia | lia | exact EV ]. }
        have HYP1 := dom_transport (A := A) STA Fρ TS VS CΔ (ρ := ρ) (Δ := Δ) (σ := σ) (N := N1)
                       (b := b) (u' := u0) (WTu' := WTu0) ERA_b VN1all.
        have HYP2 := dom_transport (A := A) STA Fρ TS VS CΔ (ρ := ρ) (Δ := Δ) (σ := σ) (N := N2)
                       (b := b) (u' := u0) (WTu' := WTu0) ERA_b VN2all.
        have HYPE := dom_transport_eq (A := A) STA Fρ TS VS CΔ (ρ := ρ) (Δ := Δ) (σ := σ) (N1 := N1) (N2 := N2)
                       (b := b) (u' := u0) (WTu' := WTu0) ERA_b EVall.
        have VS1 : ValSub Δ (Γ ++ A) (N1 .: σ) (u0 .: ρ)
          by (eapply ValSub_cons; [ exact HYP1 | exact VS ]).
        have VS2 : ValSub Δ (Γ ++ A) (N2 .: σ) (u0 .: ρ)
          by (eapply ValSub_cons; [ exact HYP2 | exact VS ]).
        have EVS' : EqValSub Δ (Γ ++ A) (N1 .: σ) (N2 .: σ) (u0 .: ρ)
          by (eapply EqValSub_cons; [ exact HYPE | exact (ValSub_EqValSub VS) ]).
        have TS1 : typing_subst Δ (N1 .: σ) (Γ ++ A)
          by (eapply typing_subst_cons; [ exact TN1 | exact TS ]).
        have TS2 : typing_subst Δ (N2 .: σ) (Γ ++ A)
          by (eapply typing_subst_cons; [ exact TN2 | exact TS ]).
        have CS' : ConvSub Δ (Γ ++ A) (N1 .: σ) (N2 .: σ)
          by (eapply ConvSub_cons; [ exact CN | exact (ConvSub_refl TS) ]).
        have Fits : fits (Γ ++ A) (u0 .: ρ)
          by (eapply fits_cons; [ exact TA | exact ERA_b | eapply wt_ty_tuniv; exact WTu0 | exact WTu0 | exact Fρ ]).
        have [_ eqvalBody] :=
          STM (u0 .: ρ) m Δ (N1 .: σ) (N2 .: σ) TS1 TS2 CS'
              Fits VS1 VS2 EVS' CΔ v0 (app f_ty u0)
              (wt_Selection_abs WT Sel) (bodyM u0 v0 Sel Vu0) (bodyB u0 Vu0).
        have HrB : max (rk v0) (rk (app f_ty u0)) < RB by (cbn in Hrank; lia).
        move: (eqvalBody RB HrB) => HvB.
        rewrite (subst_cons_eq M N1 σ) (subst_cons_eq M N2 σ) (subst_cons_eq B N1 σ) in HvB.
        have TAσ : typing Δ A[σ] Core.tuniv := ltac:(eapply subst_dom_typing; [ exact TA | exact TS | exact CΔ ]).
        have TBσ : typing (Δ ++ A[σ]) B[⇑ σ] Core.tuniv
          := ltac:(eapply subst_cod_typing; [ exact TA | exact TB | exact TS | exact CΔ ]).
        eapply EqVal_headred_expand;
          [ eapply ms_trans; [ apply hr_beta | apply ms_refl ]
          | eapply ms_trans; [ apply hr_beta | apply ms_refl ]
          | eapply beta_step_conv;
              [ exact TAlam | exact TA | exact CAlam | exact TB | exact TM
              | exact TS | exact CΔ | exact TN1 ]
          | (* the [N2] β-conversion lands at [B[⇑σ][N2..]]; retype it to the
               shared codomain [B[⇑σ][N1..]] *)
            eapply c_conv;
              [ eapply beta_step_conv;
                  [ exact TAlam | exact TA | exact CAlam | exact TB | exact TM
                  | exact TS | exact CΔ | exact TN2 ]
              | apply c_sym; eapply conv_subst_arg;
                  [ exact TAσ | exact TBσ | exact TN1 | exact TN2 | exact CN ] ]
          | exact HvB ].
Qed.

Lemma st_abs_EqVal_edge (A : Tm n) (B M : Tm (S n))
  (TM : typing (Γ ++ A) M B)
  (TA : typing Γ A Core.tuniv) (TB : typing (Γ ++ A) B Core.tuniv)
  (STA : semantic_typing Γ A Core.tuniv)
  (STB : semantic_typing (Γ ++ A) B Core.tuniv)
  (STM : semantic_typing (Γ ++ A) M B)
  ρ m (Δ : Ctx m) (σ σ' : Sub n m)
  (TS : typing_subst Δ σ Γ) (TS' : typing_subst Δ σ' Γ) (CS : ConvSub Δ Γ σ σ')
  (Fρ : fits Γ ρ) (VS : ValSub Δ Γ σ ρ) (VS' : ValSub Δ Γ σ' ρ)
  (EVS : EqValSub Δ Γ σ σ' ρ) (CΔ : ctx Δ) u a (WT : wt u a)
  (evAN : EvalRel (Core.abs A M) ρ u) (evAB : EvalRel (Core.tpi A B) ρ a) :
  forall RB, max (rk u) (rk a) < RB -> EqVal RB Δ (Core.abs A M)[σ] (Core.abs A M)[σ'] (Core.tpi A B)[σ] WT.
Proof.
  have Vρ : valid_env ρ := fits_valid_env Fρ.
  have evU : EvalRel Core.tuniv ρ tuniv by (cbn; apply le_refl).
  (* the Π-code conversion stored by [ValPi]: here the type term *is* the
     Π-normal form, so it is reflexivity *)
  have CPiσ : conv Δ (Core.tpi A[σ] B[⇑ σ]) (Core.tpi A[σ] B[⇑ σ]) Core.tuniv.
  { apply c_refl.
    move: (substitution_tm _ (Core.tpi A B) Core.tuniv _ σ
             ltac:(apply t_tpi; [ exact TA | exact TB ]) TS CΔ) => hh.
    asimpl in hh. exact hh. }
  (* the diagonal domain conversion, so the [Alam]-generalised lambda edge can
     be used at [Alam = A] *)
  have CAA : conv Γ A A Core.tuniv by (apply c_refl; exact TA).
  have TPiΓ : typing Γ (Core.tpi A B) Core.tuniv by (apply t_tpi; [ exact TA | exact TB ]).
  have evAN0 := evAN. have evAB0 := evAB.
  cbn in evAN. cbn in evAB.
  move=> RB Hrank. destruct RB; [ exact I | ].
  destruct u as [ | | | | | | g_val ]; try done.
  - (* u = bot *) apply EqVal_Bot.
  - (* u = abs g_val *)
    destruct a as [ | | | | | b f_ty | ];
      try solve [ cbn in evAB; done | exfalso; clear -WT; inversion WT ].
    move: evAN => [Vg [NBg [a_d [WTad [ERA_ad EFunM]]]]].
    move: evAB => [Vb [Vf_ty [ERA_b [a'_T [ERA_aT EFunB]]]]].
    have convAA' : conv Δ A[σ] A[σ'] Core.tuniv := subst_conv_cross TA CΔ TS TS' CS.
    have bodyM : forall u0 v0, Selection g_val u0 v0 -> valid u0 -> EvalRel M (u0 .: ρ) v0.
    { move=> u0 v0 Sel Vu0.
      have Vv0 : valid v0 := wt_valid_tm (wt_Selection_abs WT Sel).
      have leV : le v0 (app g_val u0)
        by (eapply Selection_le_app; [ exact Vg | exact Vg | apply le_fun_refl; exact Vg | exact Vu0 | exact Sel ]).
      destruct (EFunM u0 (app g_val u0) Vu0 erefl) as [x [WTx [Lex EBx]]].
      have Vx : valid x := wt_valid_tm WTx.
      have EBxv : EvalRel M (x .: ρ) v0
        by (eapply EvalRel_down; [ apply valid_cons; [ exact Vx | exact Vρ ] | exact Vv0 | exact EBx | exact leV ]).
      eapply EvalRel_mono_env;
        [ exact EBxv | apply valid_cons; [ exact Vx | exact Vρ ]
        | apply valid_cons; [ exact Vu0 | exact Vρ ]
        | apply le_env_cons; [ exact Lex | apply le_env_refl; exact Vρ ] ]. }
    have bodyB : forall u0, valid u0 -> EvalRel B (u0 .: ρ) (app f_ty u0).
    { move=> u0 Vu0.
      destruct (EFunB u0 (app f_ty u0) Vu0 erefl) as [y [WTy [Ley EBy]]].
      have Vy : valid y := wt_valid_tm WTy.
      eapply EvalRel_mono_env;
        [ exact EBy | apply valid_cons; [ exact Vy | exact Vρ ]
        | apply valid_cons; [ exact Vu0 | exact Vρ ]
        | apply le_env_cons; [ exact Ley | apply le_env_refl; exact Vρ ] ]. }
    rewrite EqVal_abs.
    (* the two [ValPi]s, from the Lam value edge at [σ] / [σ'] (the latter
       transported to the [σ]-type via [Val_ty_conv]) *)
    have VM : Val (S RB) Δ (Core.abs A M)[σ] (Core.tpi A B)[σ] WT.
    { eapply st_abs_Val_edge; eassumption. }
    have VN0 : Val (S RB) Δ (Core.abs A M)[σ'] (Core.tpi A B)[σ'] WT.
    { eapply st_abs_Val_edge with (σ' := σ'); try eassumption.
      - exact (ConvSub_refl TS').
      - exact (ValSub_EqValSub VS'). }
    (* semantic type-equality of the Pi type between σ and σ' (st_tpi_EqVal_edge),
       used to retype the σ'-lambda's [Val] to the σ-type via [Val_EqVal_fwd] —
       the Agda-faithful route (no syntactic-conv transport) *)
    have eqPi : EqVal (S (S RB)) Δ (Core.tpi A B)[σ] (Core.tpi A B)[σ'] Core.tuniv (wt_abs_ty WT).
    { eapply st_tpi_EqVal_edge; try eassumption.
      cbn in Hrank |- *; lia. }
    have eqPiSym : EqValTy (S RB) Δ (Core.tpi A B)[σ'] (Core.tpi A B)[σ] (wt_abs_ty WT).
    { eapply EqValTy_sym; [ | exact (EqVal_EqValTy eqPi) ]. cbn in Hrank |- *; lia. }
    have cvPiSym : conv Δ (Core.tpi A B)[σ'] (Core.tpi A B)[σ] Core.tuniv
      by (apply c_sym; exact (subst_conv_cross TPiΓ CΔ TS TS' CS)).
    have VN : Val (S RB) Δ (Core.abs A M)[σ'] (Core.tpi A B)[σ] WT
      by (eapply Val_EqVal_fwd;
          [ lia | lia | exact cvPiSym
          | exact VN0 | exact eqPiSym ]).
    rewrite Val_abs in VM. rewrite Val_abs in VN.
    move: VM => [VTd VPiM]. move: VN => [_ VPiN].
    split; [ exact VTd | ]. split; [ exact VPiM | ]. split; [ exact VPiN | ].
    (* the [EqValPi] edge *)
    exists A[σ], B[⇑ σ]. split; [ apply ms_refl | ]. split; [ exact CPiσ | ].
    cbn [Rec.PiAppEqVal]. move=> u0 v0 Sel WTu0 P TP VP.
    have Vu0 : valid u0 := wt_valid_tm WTu0.
    have RKu0 : rk u0 <= rk_fun g_val := rk_Selection_key Sel.
    have RKv0 : rk v0 <= rk_fun g_val := rk_Selection_val Sel.
    have RKapp : rk (app f_ty u0) <= rk_fun f_ty := rk_app f_ty u0.
    have TP' : typing Δ P A[σ'] by (eapply t_conv; [ exact TP | exact convAA' ]).
    have VPall : forall RB0, max (rk u0) (rk b) < RB0 -> Val RB0 Δ P A[σ] WTu0.
    { move=> RB0 Hr0. eapply (Val_fuel_any (k := RB)); [ cbn in Hrank; lia | cbn in Hrank; lia | lia | lia | exact VP ]. }
    have [_ eqA] :=
      STA ρ m Δ σ σ' TS TS' CS Fρ VS VS' EVS CΔ b tuniv (wt_ty_tuniv WTu0) ERA_b evU.
    have VPall' : forall RB0, max (rk u0) (rk b) < RB0 -> Val RB0 Δ P A[σ'] WTu0.
    { move=> RB0 Hr0. eapply Val_EqVal_fwd;
      [ cbn in Hr0; lia | cbn in Hr0; lia | exact convAA' | exact (VPall RB0 Hr0) | ].
      eapply EqVal_EqValTy. eapply (eqA (S RB0)). cbn in Hr0 |- *; lia. }
    have EVall : forall RB0, max (rk u0) (rk b) < RB0 -> EqVal RB0 Δ P P A[σ] WTu0.
    { move=> RB0 Hr0. eapply Val_EqVal; exact (VPall RB0 Hr0). }
    have HYP1 := dom_transport (A := A) STA Fρ TS VS CΔ (ρ := ρ) (Δ := Δ) (σ := σ) (N := P)
                   (b := b) (u' := u0) (WTu' := WTu0) ERA_b VPall.
    have HYP2 := dom_transport (A := A) STA Fρ TS' VS' CΔ (ρ := ρ) (Δ := Δ) (σ := σ') (N := P)
                   (b := b) (u' := u0) (WTu' := WTu0) ERA_b VPall'.
    have HYPE := dom_transport_eq (A := A) STA Fρ TS VS CΔ (ρ := ρ) (Δ := Δ) (σ := σ) (N1 := P) (N2 := P)
                   (b := b) (u' := u0) (WTu' := WTu0) ERA_b EVall.
    have VS1 : ValSub Δ (Γ ++ A) (P .: σ) (u0 .: ρ)
      by (eapply ValSub_cons; [ exact HYP1 | exact VS ]).
    have VS2 : ValSub Δ (Γ ++ A) (P .: σ') (u0 .: ρ)
      by (eapply ValSub_cons; [ exact HYP2 | exact VS' ]).
    have EVS' : EqValSub Δ (Γ ++ A) (P .: σ) (P .: σ') (u0 .: ρ)
      by (eapply EqValSub_cons; [ exact HYPE | exact EVS ]).
    have TS1 : typing_subst Δ (P .: σ) (Γ ++ A)
      by (eapply typing_subst_cons; [ exact TP | exact TS ]).
    have TS2 : typing_subst Δ (P .: σ') (Γ ++ A)
      by (eapply typing_subst_cons; [ exact TP' | exact TS' ]).
    have CS' : ConvSub Δ (Γ ++ A) (P .: σ) (P .: σ')
      by (eapply ConvSub_cons; [ eapply c_refl; exact TP | exact CS ]).
    have Fits : fits (Γ ++ A) (u0 .: ρ)
      by (eapply fits_cons; [ exact TA | exact ERA_b | eapply wt_ty_tuniv; exact WTu0 | exact WTu0 | exact Fρ ]).
    have [_ eqvalBody] :=
      STM (u0 .: ρ) m Δ (P .: σ) (P .: σ') TS1 TS2 CS'
          Fits VS1 VS2 EVS' CΔ v0 (app f_ty u0)
          (wt_Selection_abs WT Sel) (bodyM u0 v0 Sel Vu0) (bodyB u0 Vu0).
    have HrB : max (rk v0) (rk (app f_ty u0)) < RB by (cbn in Hrank; lia).
    move: (eqvalBody RB HrB) => HvB.
    rewrite (subst_cons_eq M P σ) (subst_cons_eq M P σ') (subst_cons_eq B P σ) in HvB.
    (* the codomain conversion between the two substitutions, instantiated at
       [P]: [B[⇑σ'][P..] ≡ B[⇑σ][P..]] *)
    have cvBcross : conv Δ B[⇑ σ'][P..] B[⇑ σ][P..] Core.tuniv.
    { have hh := subst_conv_cross TB CΔ TS1 TS2 CS'.
      rewrite (subst_cons_eq B P σ) (subst_cons_eq B P σ') in hh.
      apply c_sym; exact hh. }
    eapply EqVal_headred_expand;
      [ eapply ms_trans; [ apply hr_beta | apply ms_refl ]
      | eapply ms_trans; [ apply hr_beta | apply ms_refl ]
      | eapply beta_step_conv;
          [ exact TA | exact TA | exact CAA | exact TB | exact TM
          | exact TS | exact CΔ | exact TP ]
      | (* the σ'-side β-conversion lands at [B[⇑σ'][P..]]; retype it *)
        eapply c_conv;
          [ eapply beta_step_conv;
              [ exact TA | exact TA | exact CAA | exact TB | exact TM
              | exact TS' | exact CΔ | exact TP' ]
          | exact cvBcross ]
      | exact HvB ].
Qed.

(** Lambda rule (Agda [adequacyV2-ty-Lam]): from semantic typing of the domain,
    codomain, and body, the abstraction [abs A M] is semantically typed at
    [tpi A B].  The value-graph edges come from [st_abs_Val_edge] /
    [st_abs_EqVal_edge]. *)
Lemma st_abs A B M :
  typing Γ A Core.tuniv ->
  typing (Γ ++ A) B Core.tuniv ->
  typing (Γ ++ A) M B ->
  semantic_typing Γ A Core.tuniv ->
  semantic_typing (Γ ++ A) B Core.tuniv ->
  semantic_typing (Γ ++ A) M B ->
(* ------------------------- *)
  semantic_typing Γ (Core.abs A M) (Core.tpi A B).
Proof.
  move=> TA TB TM STA STB STM.
  move=> ρ m Δ σ σ' TS TS' CS Fρ VS VS' EVS CΔ u a WT evAN evAB.
  have CAA : conv Γ A A Core.tuniv by (apply c_refl; exact TA).
  split.
  - eapply st_abs_Val_edge; eassumption.
  - eapply st_abs_EqVal_edge; eassumption.
Qed.

(** Universe rule (Agda [adequacyV2-U]): [tuniv] is semantically typed at
    [tuniv] (type-in-type). *)
Lemma st_univ :
  ctx Γ ->
(* ------------------------- *)
  semantic_typing Γ Core.tuniv Core.tuniv.
Proof.
  move=> CG.
  unfold semantic_typing.
  intros ρ m Δ s s' Ts Ts' CS F VSs VSs' ES CD u a WT EN EU.
  cbn in EN.
  split; intros RB.
  - destruct (is_bot u) eqn:IB; destruct u; try done.
    + destruct RB; try done. cbn.
      destruct a; try done.
    + destruct RB; try done. cbn.
      destruct a; try done.
  - destruct (is_bot u) eqn:IB; destruct u; try done.
    + destruct RB; try done. cbn.
      destruct a; try done.  
    + destruct RB; try done. cbn.
      destruct a; try done.
Qed.

(* -------- semantic conversion rules -------- *)

(* c_conv: M ≡ N : A, A ≡ B : tuniv i ⟹ M ≡ N : B *)
(** Conversion congruence for [≡] (Agda [adequacyE2-conv]): a semantic
    conversion transports along a semantic type conversion. *)
Lemma sc_conv M N A B :
  conv Γ M N A ->
  conv Γ A B Core.tuniv ->
  semantic_conv2 Γ M N A ->
  semantic_conv2 Γ A B Core.tuniv ->
(* ------------------------- *)
  semantic_conv2 Γ M N B.
Proof.
  move=> CMN CAB SC1 SC2.
  move=> ρ m Δ σ TS FR VS CD u a WT EM EB.
  move: (conv_EvalRel CAB FR) => [_ [_ [_ bwd]]].
  have EA : EvalRel A ρ a by (apply bwd; exact EB).
  have WTa : wt a tuniv by (eapply wt_ty_tuniv; exact WT).
  have evU : EvalRel Core.tuniv ρ tuniv by [].
  have eqMN := SC1 ρ m Δ σ TS FR VS CD u a WT EM EA.
  have eqAB := SC2 ρ m Δ σ TS FR VS CD a tuniv WTa EA evU.
  have cvABs : conv Δ A[σ] B[σ] Core.tuniv.
  { move: (substitution_conv _ A B Core.tuniv _ σ CAB TS CD) => hh.
    asimpl in hh. exact hh. }
  move=> RB Hrank. eapply EqVal_EqVal_fwd;
    [ cbn in Hrank; lia | cbn in Hrank; lia | exact cvABs | exact (eqMN RB Hrank)
    | eapply EqVal_EqValTy; eapply (eqAB (S RB)); cbn in Hrank |- *; lia ].
Qed.

(** Reflexivity of [≡] (Agda [adequacyE2-refl]): a semantically typed term is
    semantically convertible to itself (the diagonal [Val → EqVal]). *)
Lemma sc_refl M A :
  typing Γ M A ->
  semantic_typing Γ M A ->
(* ------------------------- *)
  semantic_conv2 Γ M M A.
Proof.
  (* Following Adequacy2.agda's conv-refl case (lines 603-604):
       adequacyEqSub2 (conv-refl d) σ ... u hu a evA fm =
         Val2-to-EqVal2 u a (adequacySub2 d σ ... u hu a evA fm)
     Agda uses a single σ, so the diagonal Val→EqVal step suffices.
     Coq's semantic_conv2 takes (σ1, σ2) potentially different, so the
     diagonal case (σ1 ≡ σ2 pointwise via EqValSub) extends with a
     substitution-equivalence step.  We split as:
       (1) Apply h_typing at σ1 → Val Δ M[σ1] A[σ1] WT.
       (2) Val_EqVal → EqVal Δ M[σ1] M[σ1] A[σ1] WT.
       (3) Bridge the right-hand-side M[σ1] ↔ M[σ2] via the fundamental
           lemma for semantic substitution equivalence (admitted). *)
  (* [adequacyEqSub2 (conv-refl d)] = the [EqVal M[σ] M[σ']] conjunct of
     [semantic_typing] instantiated at the diagonal [σ' := σ]. *)
  move=> T1 h_typ.
  move=> ρ m Δ σ TS FR VS CD u a WT EM EA.
  have [_ eqMM] := h_typ ρ m Δ σ σ TS TS (ConvSub_refl TS) FR VS VS (ValSub_EqValSub VS) CD u a WT EM EA.
  exact eqMM.
Qed.

(* c_sym: M ≡ N : A ⟹ N ≡ M : A *)
(** Symmetry of [≡] (Agda [adequacyE2-sym]): from [EqVal_sym]. *)
Lemma sc_sym M N A :
  conv Γ M N A ->
  semantic_conv2 Γ M N A ->
(* ------------------------- *)
  semantic_conv2 Γ N M A.
Proof.
  (* Following Adequacy2.agda's conv-sym: bridge [EvalRel N -> EvalRel M]
     (conv_EvalRel's bwd), apply [h_conv] to get [EqVal M[σ] N[σ]], then
     [EqVal_sym].  With the single-σ [semantic_conv2] this is immediate. *)
  move=> C1 h_conv.
  move=> ρ m Δ σ TS FR VS CD u a WT EN EA.
  move: (conv_EvalRel C1 FR) => [_ [_ [_ bwd]]].
  have EM : EvalRel M ρ u by (apply bwd; exact EN).
  have h := h_conv ρ m Δ σ TS FR VS CD u a WT EM EA.
  move=> RB Hrank. eapply EqVal_sym; [ cbn in Hrank; lia | exact (h RB Hrank) ].
Qed.

(** Transitivity of [≡] (Agda [adequacyE2-trans]): from [EqVal_trans]. *)
Lemma sc_trans M N P A :
  conv Γ M N A ->
  conv Γ N P A ->
  semantic_conv2 Γ M N A ->
  semantic_conv2 Γ N P A ->
(* ------------------------- *)
  semantic_conv2 Γ M P A.
Proof.
  move=> CMN CNP SC1 SC2.
  move=> ρ m Δ σ TS FR VS CD u a WT EM EA.
  move: (conv_EvalRel CMN FR) => [_ [_ [fwd _]]].
  have EN : EvalRel N ρ u by (apply fwd; exact EM).
  have e1 := SC1 ρ m Δ σ TS FR VS CD u a WT EM EA.
  have e2 := SC2 ρ m Δ σ TS FR VS CD u a WT EN EA.
  move=> RB Hrank. eapply EqVal_trans; [ cbn in Hrank; lia | exact (e1 RB Hrank) | exact (e2 RB Hrank) ].
Qed.

(** Application congruence in the function position (Agda [adequacyE2-App-fun]):
    [N ≡ N' : tpi A B] and [M : A] give [app N M ≡ app N' M : B[M..]]. *)
Lemma sc_app1 A B N N' M :
  typing Γ A Core.tuniv ->
  typing (Γ ++ A) B Core.tuniv ->
  conv Γ N N' (Core.tpi A B) ->
  typing Γ M A ->
  semantic_typing Γ A Core.tuniv ->
  semantic_typing (Γ ++ A) B Core.tuniv ->
  semantic_conv2 Γ N N' (Core.tpi A B) ->
  semantic_typing Γ M A ->
(* ------------------------- *)
  semantic_conv2 Γ (Core.app N M) (Core.app N' M) B[M..].
Proof.
  move=> TA TB CNN' TM STA STB SCnn STM.
  move=> ρ m Δ σ TS FR VS CD u a WT Eapp EBM.
  have Vρ : valid_env ρ := fits_valid_env FR.
  move=> RB Hrank.
  destruct (is_bot u) eqn:Hu.
  { have Eu : u = bot by (apply is_bot_eq; rewrite Hu). subst u. apply EqVal_Bot. }
  (* [app N M] evaluates: [N]'s value is a singleton [w ↦ u], arg [M]'s value [w] *)
  cbn in Eapp. rewrite Hu in Eapp. move: Eapp => [w [evN_sing evMw]].
  have [TN _] := conv_typing CNN'.
  have IT : InvTyped Γ N (Core.tpi A B) ρ by (apply typing_EvalRel; [ exact TN | exact FR ]).
  have [vbig [abig [WTbig [LEbig [evMbig evTpi]]]]] := IT (w ↦ u) evN_sing.
  unfold singleton in LEbig. rewrite Hu in LEbig.
  have [g [Evbig LEfun]] := le_abs_inv LEbig. subst vbig.
  destruct abig as [ | | | | | b f | ]; try solve [ exfalso; clear -WTbig; inversion WTbig ].
  have evTpiC := evTpi. cbn in evTpiC. move: evTpiC => [Vb [Vf [evA_b _]]].
  have Vg : valid_fun g := proj1 (andb_prop _ _ (wt_valid_tm WTbig)).
  have Vw : valid w := EvalRel_valid evMw.
  have [u_sel [v_sel [Sel [Le_usel Eq_vsel]]]] := selectionBelow Vg Vw.
  have [WTu_sel WTv_sel] : wt u_sel b /\ wt v_sel (app f u_sel).
  { eapply wt_Selection_cod;
      [ exact (wt_abs_ty WTbig) | exact (wt_abs_inv1 WTbig)
      | move=> ui vi Hin; exact (wt_abs_inv2 WTbig Hin erefl) | exact Vg | exact Sel ]. }
  have Vusel : valid u_sel := wt_valid_tm WTu_sel.
  have evM_usel : EvalRel M ρ u_sel
    by (eapply EvalRel_down; [ exact Vρ | exact Vusel | exact evMw | exact Le_usel ]).
  pose RBf := S (max (max (rk (abs g)) (rk (tpi b f))) (max (rk u) (rk a))).
  have RKusel : rk u_sel <= rk_fun g := rk_Selection_key Sel.
  have RKb : rk b < rk (tpi b f) by (cbn; lia).
  have RKfg : rk_fun g < rk (abs g) by (cbn; lia).
  have HfM : max (rk (abs g)) (rk (tpi b f)) < S RBf by (unfold RBf; lia).
  have HfN : max (rk u_sel) (rk b) < RBf by (unfold RBf; lia).
  have [valM _] :=
    STM ρ m Δ σ σ TS TS (ConvSub_refl TS) FR VS VS (ValSub_EqValSub VS) CD
        u_sel b WTu_sel evM_usel evA_b.
  have eqvalNbig := SCnn ρ m Δ σ TS FR VS CD (abs g) (tpi b f) WTbig evMbig evTpi.
  have TMσ : typing Δ M[σ] A[σ] by (eapply substitution_tm; [ exact TM | exact TS | exact CD ]).
  (* expose the function's [EqValPi] (function variation) *)
  have EM := eqvalNbig (S RBf) HfM. rewrite EqVal_abs in EM.
  move: EM => [_ [_ [_ EPi]]]. move: EPi => [A0 [B0 [HRpi [CTpi paev]]]].
  asimpl in HRpi. have [EA0 EB0] := HeadRed_tpi_eq HRpi. subst A0 B0.
  have Efun := paev u_sel v_sel Sel WTu_sel M[σ] TMσ (valM RBf HfN).
  have VNarg : forall v c0 (h : wt v c0), EvalRel M ρ v -> EvalRel A ρ c0 ->
      forall RB0, max (rk v) (rk c0) < RB0 -> Val RB0 Δ M[σ] A[σ] h
    by (move=> v c0 h ev ea;
        exact (proj1 (STM ρ m Δ σ σ TS TS (ConvSub_refl TS) FR VS VS (ValSub_EqValSub VS) CD v c0 h ev ea))).
  (* the edge codomain [app f u_sel] also evaluates [B[M..]] *)
  have evB_af : EvalRel B[M..] ρ (app f u_sel).
  { destruct (is_bot (app f u_sel)) eqn:Hbaf.
    - have -> : app f u_sel = bot by apply is_bot_eq; rewrite Hbaf. apply EvalRel_bot.
    - have NB : ~ is_bot (app f u_sel) by rewrite Hbaf.
      eapply EvalRel_Pi_app_type;
        [ exact evTpi | exact Vρ | exact Vusel | reflexivity | exact NB | exact evM_usel ]. }
  have Caaf : compatible a (app f u_sel)
    by (eapply EvalRel_compatible; [ exact Vρ | exact EBM | exact evB_af ]).
  have ELub : EvalRel B[M..] ρ (lub a (app f u_sel))
    by (exact (proj2 (EvalRel_compatible_lub Vρ EBM evB_af) _ erefl)).
  have Waf : wt (app f u_sel) tuniv := wt_ty_tuniv (wt_Selection_abs WTbig Sel).
  have hUc : wt (lub a (app f u_sel)) tuniv := wt_lub (wt_ty_tuniv WT) Caaf Waf.
  have HrC : max (rk (lub a (app f u_sel))) (rk tuniv) < RBf.
  { have L1 := rk_lub a (app f u_sel). have L2 := rk_app f u_sel.
    have Hf : rk_fun f < rk (tpi b f) by (cbn; lia).
    have Htu : rk tuniv <= rk (tpi b f) by (cbn; lia).
    unfold RBf; lia. }
  have VTc : Val RBf Δ (B[⇑ σ][M[σ] .: var]) Core.tuniv hUc
    by (eapply codomain_type_ValTy;
          [ exact TA | exact TM | exact STA | exact STB | exact FR | exact TS
          | exact VS | exact CD | exact VNarg | exact ELub | exact HrC ]).
  have LEu_vsel : le u v_sel.
  { rewrite le_fun_cons in LEfun.
    have LEua := proj1 (andb_prop _ _ LEfun). rewrite Eq_vsel in LEua. exact LEua. }
  apply (EqVal_fuel_any (k := RBf) (k' := RB));
    [ unfold RBf; lia | unfold RBf; lia | lia | lia | ].
  asimpl in Efun.
  match goal with
  | |- EqVal _ _ _ _ ?T _ => replace T with (B[⇑ σ][M[σ] .: var])
  end;
    [ exact (@EqVal_app_transport _ Δ _ _ _ u v_sel a (app f u_sel)
               (wt_Selection_abs WTbig Sel) WT hUc Caaf LEu_vsel RBf VTc Efun)
    | solve [ apply subst1_subst_comm | symmetry; apply subst1_subst_comm ] ].
Qed.

(** Application congruence in the argument position (Agda [adequacyE2-App-arg]):
    [N : tpi A B] and [M ≡ M' : A] give [app N M ≡ app N M' : B[M..]]. *)
Lemma sc_app2 A B N M M' :
  typing Γ A Core.tuniv ->
  typing (Γ ++ A) B Core.tuniv ->
  typing Γ N (Core.tpi A B) ->
  conv Γ M M' A ->
  semantic_typing Γ A Core.tuniv ->
  semantic_typing (Γ ++ A) B Core.tuniv ->
  semantic_typing Γ N (Core.tpi A B) ->
  semantic_conv2 Γ M M' A ->
(* ------------------------- *)
  semantic_conv2 Γ (Core.app N M) (Core.app N M') B[M..].
Proof.
  move=> TA TB TN CMM' STA STB STN SCmm.
  have [TM _] := conv_typing CMM'.
  move=> ρ m Δ σ TS FR VS CD u a WT Eapp EBM.
  have Vρ : valid_env ρ := fits_valid_env FR.
  move=> RB Hrank.
  destruct (is_bot u) eqn:Hu.
  { have Eu : u = bot by (apply is_bot_eq; rewrite Hu). subst u. apply EqVal_Bot. }
  cbn in Eapp. rewrite Hu in Eapp. move: Eapp => [w [evN_sing evMw]].
  have IT : InvTyped Γ N (Core.tpi A B) ρ by (apply typing_EvalRel; [ exact TN | exact FR ]).
  have [vbig [abig [WTbig [LEbig [evMbig evTpi]]]]] := IT (w ↦ u) evN_sing.
  unfold singleton in LEbig. rewrite Hu in LEbig.
  have [g [Evbig LEfun]] := le_abs_inv LEbig. subst vbig.
  destruct abig as [ | | | | | b f | ]; try solve [ exfalso; clear -WTbig; inversion WTbig ].
  have evTpiC := evTpi. cbn in evTpiC. move: evTpiC => [Vb [Vf [evA_b _]]].
  have Vg : valid_fun g := proj1 (andb_prop _ _ (wt_valid_tm WTbig)).
  have Vw : valid w := EvalRel_valid evMw.
  have [u_sel [v_sel [Sel [Le_usel Eq_vsel]]]] := selectionBelow Vg Vw.
  have [WTu_sel WTv_sel] : wt u_sel b /\ wt v_sel (app f u_sel).
  { eapply wt_Selection_cod;
      [ exact (wt_abs_ty WTbig) | exact (wt_abs_inv1 WTbig)
      | move=> ui vi Hin; exact (wt_abs_inv2 WTbig Hin erefl) | exact Vg | exact Sel ]. }
  have Vusel : valid u_sel := wt_valid_tm WTu_sel.
  have evM_usel : EvalRel M ρ u_sel
    by (eapply EvalRel_down; [ exact Vρ | exact Vusel | exact evMw | exact Le_usel ]).
  pose RBf := S (max (max (rk (abs g)) (rk (tpi b f))) (max (rk u) (rk a))).
  have RKusel : rk u_sel <= rk_fun g := rk_Selection_key Sel.
  have RKb : rk b < rk (tpi b f) by (cbn; lia).
  have RKfg : rk_fun g < rk (abs g) by (cbn; lia).
  have HfM : max (rk (abs g)) (rk (tpi b f)) < S RBf by (unfold RBf; lia).
  have HfN : max (rk u_sel) (rk b) < RBf by (unfold RBf; lia).
  have eqvalM := SCmm ρ m Δ σ TS FR VS CD u_sel b WTu_sel evM_usel evA_b.
  have [valNbig _] :=
    STN ρ m Δ σ σ TS TS (ConvSub_refl TS) FR VS VS (ValSub_EqValSub VS) CD
        (abs g) (tpi b f) WTbig evMbig evTpi.
  have convMM' : conv Δ M[σ] M'[σ] A[σ]
    by (eapply substitution_conv; [ exact CMM' | exact TS | exact CD ]).
  (* expose the function's [PiAppEq] (argument variation) *)
  have VN := valNbig (S RBf) HfM. rewrite Val_abs in VN.
  move: VN => [_ VPi]. move: VPi => [A0 [B0 [HRpi [CTpi [_ pae]]]]].
  asimpl in HRpi. have [EA0 EB0] := HeadRed_tpi_eq HRpi. subst A0 B0.
  have Earg := pae u_sel v_sel Sel WTu_sel M[σ] M'[σ] convMM' (eqvalM RBf HfN).
  have VNarg : forall v c0 (h : wt v c0), EvalRel M ρ v -> EvalRel A ρ c0 ->
      forall RB0, max (rk v) (rk c0) < RB0 -> Val RB0 Δ M[σ] A[σ] h
    by (move=> v c0 h ev ea RB0 Hr0;
        eapply EqVal_Val1; exact (SCmm ρ m Δ σ TS FR VS CD v c0 h ev ea RB0 Hr0)).
  (* the edge codomain [app f u_sel] also evaluates [B[M..]] *)
  have evB_af : EvalRel B[M..] ρ (app f u_sel).
  { destruct (is_bot (app f u_sel)) eqn:Hbaf.
    - have -> : app f u_sel = bot by apply is_bot_eq; rewrite Hbaf. apply EvalRel_bot.
    - have NB : ~ is_bot (app f u_sel) by rewrite Hbaf.
      eapply EvalRel_Pi_app_type;
        [ exact evTpi | exact Vρ | exact Vusel | reflexivity | exact NB | exact evM_usel ]. }
  have Caaf : compatible a (app f u_sel)
    by (eapply EvalRel_compatible; [ exact Vρ | exact EBM | exact evB_af ]).
  have ELub : EvalRel B[M..] ρ (lub a (app f u_sel))
    by (exact (proj2 (EvalRel_compatible_lub Vρ EBM evB_af) _ erefl)).
  have Waf : wt (app f u_sel) tuniv := wt_ty_tuniv (wt_Selection_abs WTbig Sel).
  have hUc : wt (lub a (app f u_sel)) tuniv := wt_lub (wt_ty_tuniv WT) Caaf Waf.
  have HrC : max (rk (lub a (app f u_sel))) (rk tuniv) < RBf.
  { have L1 := rk_lub a (app f u_sel). have L2 := rk_app f u_sel.
    have Hf : rk_fun f < rk (tpi b f) by (cbn; lia).
    have Htu : rk tuniv <= rk (tpi b f) by (cbn; lia).
    unfold RBf; lia. }
  have VTc : Val RBf Δ (B[⇑ σ][M[σ] .: var]) Core.tuniv hUc
    by (eapply codomain_type_ValTy;
          [ exact TA | exact TM | exact STA | exact STB | exact FR | exact TS
          | exact VS | exact CD | exact VNarg | exact ELub | exact HrC ]).
  have LEu_vsel : le u v_sel.
  { rewrite le_fun_cons in LEfun.
    have LEua := proj1 (andb_prop _ _ LEfun). rewrite Eq_vsel in LEua. exact LEua. }
  apply (EqVal_fuel_any (k := RBf) (k' := RB));
    [ unfold RBf; lia | unfold RBf; lia | lia | lia | ].
  asimpl in Earg.
  match goal with
  | |- EqVal _ _ _ _ ?T _ => replace T with (B[⇑ σ][M[σ] .: var])
  end;
    [ exact (@EqVal_app_transport _ Δ _ _ _ u v_sel a (app f u_sel)
               (wt_Selection_abs WTbig Sel) WT hUc Caaf LEu_vsel RBf VTc Earg)
    | solve [ apply subst1_subst_comm | symmetry; apply subst1_subst_comm ] ].
Qed.

(** Beta rule (Agda [adequacyE2-beta]): the redex [app (abs A N) M] is
    semantically convertible to its contractum [N[M..]] at [B[M..]]. *)
Lemma sc_beta A B M N :
  typing Γ A Core.tuniv ->
  typing (Γ ++ A) B Core.tuniv ->
  typing (Γ ++ A) N B ->
  typing Γ M A ->
  semantic_typing Γ A Core.tuniv ->
  semantic_typing (Γ ++ A) B Core.tuniv ->
  semantic_typing (Γ ++ A) N B ->
  semantic_typing Γ M A ->
(* ------------------------- *)
  semantic_conv2 Γ (Core.app (Core.abs A N) M) N[M..] B[M..].
Proof.
  move=> TA TB TN TM STA STB STN STM.
  (* the redex [app (abs A N) M] is semantically well-typed at [B[M..]]
     (st_abs then st_app); we use its reflexive [EqVal] and contract the
     second side along the beta head-reduction to [N[M..]]. *)
  have Tabs : typing Γ (Core.abs A N) (Core.tpi A B)
    by (eapply t_abs; [ exact TA | exact TB | exact TN ]).
  have STabs : semantic_typing Γ (Core.abs A N) (Core.tpi A B)
    by (eapply st_abs; [ exact TA | exact TB | exact TN | exact STA | exact STB | exact STN ]).
  have ST_app : semantic_typing Γ (Core.app (Core.abs A N) M) B[M..]
    by (eapply st_app;
        [ exact TA | exact TB | exact Tabs | exact TM
        | exact STA | exact STB | exact STabs | exact STM ]).
  (* the syntactic β conversion, which is the [Red3] step conversion for the
     head contraction below *)
  have Cbeta : conv Γ (Core.app (Core.abs A N) M) N[M..] B[M..]
    by (eapply c_beta; [ exact TA | exact TB | exact TN | exact TM ]).
  have Tapp : typing Γ (Core.app (Core.abs A N) M) B[M..]
    by (eapply t_app; [ exact TA | exact TB | exact Tabs | exact TM ]).
  move=> ρ m Δ σ TS FR VS CD u a WT evApp evB RB Hrank.
  have eqApp :=
    proj2 (ST_app ρ m Δ σ σ TS TS (ConvSub_refl TS) FR VS VS (ValSub_EqValSub VS)
             CD u a WT evApp evB).
  have CbetaS : conv Δ (Core.app (Core.abs A N) M)[σ] (N[M..])[σ] (B[M..])[σ]
    by (eapply substitution_conv; [ exact Cbeta | exact TS | exact CD ]).
  have CreflS : conv Δ (Core.app (Core.abs A N) M)[σ]
                       (Core.app (Core.abs A N) M)[σ] (B[M..])[σ]
    by (apply c_refl; eapply substitution_tm; [ exact Tapp | exact TS | exact CD ]).
  eapply EqVal_headred_contract.
  - apply ms_refl.
  - rewrite subst1_subst_comm.
    eapply ms_trans; [ apply hr_beta | apply ms_refl ].
  - exact CreflS.
  - apply c_sym; exact CbetaS.
  - exact (eqApp RB Hrank).
Qed.

(** Function extensionality / eta (Agda [adequacyE2-funext]): two functions
    that act equally on a fresh argument are semantically convertible at the
    Π-type. *)
Lemma sc_eta A B (N N' : Tm n) :
  typing Γ A Core.tuniv ->
  typing Γ N (Core.tpi A B) ->
  typing Γ N' (Core.tpi A B) ->
  conv (Γ ++ A) (Core.app N⟨↑⟩ (var var_zero))
                (Core.app N'⟨↑⟩ (var var_zero)) B ->
  semantic_typing Γ A Core.tuniv ->
  semantic_typing Γ N (Core.tpi A B) ->
  semantic_typing Γ N' (Core.tpi A B) ->
  semantic_conv2 (Γ ++ A) (Core.app N⟨↑⟩ (var var_zero))
                          (Core.app N'⟨↑⟩ (var var_zero)) B ->
(* ------------------------- *)
  semantic_conv2 Γ N N' (Core.tpi A B).
Proof.
  move=> TA TN TN' CBody STA STN STN' SC_body.
  have CNN' : conv Γ N N' (Core.tpi A B)
    by (eapply c_eta; [ exact TA | exact TN | exact TN' | exact CBody ]).
  move=> ρ m Δ σ TS FR VS CD u a WT evN evTpi.
  have Vρ : valid_env ρ := fits_valid_env FR.
  have evU : EvalRel Core.tuniv ρ tuniv by (cbn; apply le_refl).
  (* [N'] reaches the same value [u] by conversion soundness *)
  move: (conv_EvalRel CNN' FR) => [_ [_ [fwd _]]].
  have evN' : EvalRel N' ρ u := fwd u evN.
  have evTpi0 := evTpi. cbn in evTpi.
  move=> RB Hrank. destruct RB; [ exact I | ].
  destruct a as [ | | | | | b f_ty | ];
    try solve [ exfalso; clear -evTpi; cbn in evTpi; done ].
  - (* a = bot: the type value is [bot], so [u = bot] *)
    have Eu := wt_bot_inv WT. subst u. apply EqVal_Bot.
  - (* a = tpi b f_ty *)
    move: evTpi => [Vb [Vf_ty [ERA_b [a'_T [ERA_aT EFunB]]]]].
    destruct u as [ | | | | | | g_val ];
      try solve [ exfalso; clear -WT; inversion WT ].
    + (* u = bot *) apply EqVal_Bot.
    + (* u = abs g_val *)
      (* the two [ValPi]s from [STN]/[STN'] at the shared value [abs g_val] *)
      have VM : Val (S RB) Δ N[σ] (Core.tpi A B)[σ] WT.
      { have [vM _] :=
          STN ρ m Δ σ σ TS TS (ConvSub_refl TS) FR VS VS (ValSub_EqValSub VS)
              CD (abs g_val) (tpi b f_ty) WT evN evTpi0.
        exact (vM (S RB) Hrank). }
      have VN' : Val (S RB) Δ N'[σ] (Core.tpi A B)[σ] WT.
      { have [vN _] :=
          STN' ρ m Δ σ σ TS TS (ConvSub_refl TS) FR VS VS (ValSub_EqValSub VS)
               CD (abs g_val) (tpi b f_ty) WT evN' evTpi0.
        exact (vN (S RB) Hrank). }
      rewrite Val_abs in VM. rewrite Val_abs in VN'.
      move: VM => [VTd VPiM]. move: VN' => [_ VPiN'].
      rewrite EqVal_abs.
      split; [ exact VTd | ]. split; [ exact VPiM | ]. split; [ exact VPiN' | ].
      (* codomain-type evaluation edge (mirrors [st_abs]) *)
      have bodyB : forall u0, valid u0 -> EvalRel B (u0 .: ρ) (app f_ty u0).
      { move=> u0 Vu0.
        destruct (EFunB u0 (app f_ty u0) Vu0 erefl) as [y [WTy [Ley EBy]]].
        have Vy : valid y := wt_valid_tm WTy.
        eapply EvalRel_mono_env;
          [ exact EBy | apply valid_cons; [ exact Vy | exact Vρ ]
          | apply valid_cons; [ exact Vu0 | exact Vρ ]
          | apply le_env_cons; [ exact Ley | apply le_env_refl; exact Vρ ] ]. }
      have Vg : valid_fun g_val := proj1 (andb_prop _ _ (wt_valid_tm WT)).
      (* the Π-code conversion: read it off the [ValPi] we already have (the
         type term is already a Π-normal form, so [HeadRed_tpi_eq] identifies
         the reduct) *)
      have CPiσ : conv Δ (Core.tpi A B)[σ] (Core.tpi A[σ] B[⇑ σ]) Core.tuniv.
      { move: VPiM => [A0 [B0 [HRpi [CT _]]]].
        asimpl in HRpi. have [E1 E2] := HeadRed_tpi_eq HRpi. subst A0 B0. exact CT. }
      (* the [EqValPi] edge: each related result equals via the body conversion *)
      exists A[σ], B[⇑ σ]. split; [ apply ms_refl | ]. split; [ exact CPiσ | ].
      cbn [Rec.PiAppEqVal]. move=> u0 v0 Sel WTu0 P TP VP.
      have Vu0 : valid u0 := wt_valid_tm WTu0.
      have RKu0 : rk u0 <= rk_fun g_val := rk_Selection_key Sel.
      have RKv0 : rk v0 <= rk_fun g_val := rk_Selection_val Sel.
      have RKapp : rk (app f_ty u0) <= rk_fun f_ty := rk_app f_ty u0.
      set WTcod := (wt_Selection_abs WT Sel).
      destruct (is_bot v0) eqn:Bv0.
      { have Ev0 : v0 = bot by (apply is_bot_eq; rewrite Bv0). subst v0. apply EqVal_Bot. }
      have Vv0 : valid v0 := wt_valid_tm WTcod.
      have NBv0 : ~~ le v0 bot.
      { apply /negP => H. move/le_bot_inv: H => H. rewrite H /= in Bv0. discriminate Bv0. }
      (* the eta-application evaluates: [app N⟨↑⟩ var0] at [(u0.:ρ)] reaches [v0] *)
      have LEsing : le (u0 ↦ v0) (abs g_val).
      { rewrite /singleton Bv0 le_abs le_fun_cons le_fun_nil andbT.
        eapply Selection_le_app;
          [ exact Vg | exact Vg | apply le_fun_refl; exact Vg | exact Vu0 | exact Sel ]. }
      have Vsing : valid (u0 ↦ v0).
      { rewrite /singleton Bv0 /= /_valid_fun /= !Bool.andb_true_r.
        apply /andP; split.
        2: by rewrite Vu0 Vv0.
        apply /andP; split.
        2: exact NBv0.
        apply /implyP => _. by apply compatible_refl. }
      have evNsing : EvalRel N ρ (u0 ↦ v0)
        by (eapply EvalRel_down; [ exact Vρ | exact Vsing | exact evN | exact LEsing ]).
      have evApp0 : EvalRel (Core.app N⟨↑⟩ (var var_zero)) (u0 .: ρ) v0.
      { have -> : EvalRel (Core.app N⟨↑⟩ (var var_zero)) (u0 .: ρ) v0
                = (exists w, EvalRel (N⟨↑⟩) (u0 .: ρ) (w ↦ v0)
                          /\ EvalRel (var var_zero) (u0 .: ρ) w)
          by (cbn [EvalRel]; rewrite Bv0; reflexivity).
        exists u0. split.
        - apply EvalRel_wk; exact evNsing.
        - cbn. split; [ exact Vu0 | apply le_refl; exact Vu0 ]. }
      (* extend the substitution to [(P .: σ)] over [Γ ++ A] *)
      have VPall : forall RB0, max (rk u0) (rk b) < RB0 -> Val RB0 Δ P A[σ] WTu0.
      { move=> RB0 Hr0. eapply (Val_fuel_any (k := RB));
          [ cbn in Hrank; lia | cbn in Hrank; lia | lia | lia | exact VP ]. }
      have HYP1 := dom_transport (A := A) STA FR TS VS CD (ρ := ρ) (Δ := Δ) (σ := σ) (N := P)
                     (b := b) (u' := u0) (WTu' := WTu0) ERA_b VPall.
      have VS1 : ValSub Δ (Γ ++ A) (P .: σ) (u0 .: ρ)
        by (eapply ValSub_cons; [ exact HYP1 | exact VS ]).
      have TS1 : typing_subst Δ (P .: σ) (Γ ++ A)
        by (eapply typing_subst_cons; [ exact TP | exact TS ]).
      have Fits : fits (Γ ++ A) (u0 .: ρ)
        by (eapply fits_cons; [ exact TA | exact ERA_b | eapply wt_ty_tuniv; exact WTu0 | exact WTu0 | exact FR ]).
      have eqBody := SC_body (u0 .: ρ) m Δ (P .: σ) TS1 Fits VS1 CD
                       v0 (app f_ty u0) WTcod evApp0 (bodyB u0 Vu0).
      have HrB : max (rk v0) (rk (app f_ty u0)) < RB by (cbn in Hrank; lia).
      move: (eqBody RB HrB) => HvB.
      have E1 : (Core.app N⟨↑⟩ (var var_zero))[P .: σ] = Core.app N[σ] P by asimpl.
      have E2 : (Core.app N'⟨↑⟩ (var var_zero))[P .: σ] = Core.app N'[σ] P by asimpl.
      rewrite E1 E2 (subst_cons_eq B P σ) in HvB.
      exact HvB.
Qed.

(*
(* c_nrec_Z: app (nrec T M0 M1) zero ≡ M0 : T[zero..] *)
Lemma sc_nrec_Z M0 M1 (T : Tm (S n)) :
  typing (Γ ++ Core.tnat) T Core.tuniv ->
  typing Γ M0 (T[Core.zero..]) ->
  typing Γ M1 (Core.tpi Core.tnat (Core.tpi T T[rho]⟨↑⟩)) ->
  semantic_typing (Γ ++ Core.tnat) T Core.tuniv ->
  semantic_typing Γ M0 (T[Core.zero..]) ->
  semantic_typing Γ M1 (Core.tpi Core.tnat (Core.tpi T T[rho]⟨↑⟩)) ->
(* ------------------------- *)
  semantic_conv2 Γ (Core.app (Core.nrec T M0 M1) Core.zero) M0 T[Core.zero..].


(* c_nrec_S: app (nrec T M0 M1) (succ n) ≡ app (app M1 n) (app (nrec ...) n) : T[(succ n)..] *)
Lemma sc_nrec_S (T : Tm (S n)) M0 M1 (e : Tm n) :
  typing (Γ ++ Core.tnat) T Core.tuniv ->
  typing Γ M0 (T[Core.zero..]) ->
  typing Γ M1 (Core.tpi Core.tnat (Core.tpi T T[rho]⟨↑⟩)) ->
  semantic_typing (Γ ++ Core.tnat) T Core.tuniv ->
  semantic_typing Γ M0 (T[Core.zero..]) ->
  semantic_typing Γ M1 (Core.tpi Core.tnat (Core.tpi T T[rho]⟨↑⟩)) ->
(* ------------------------- *)
  semantic_conv2 Γ (Core.app (Core.nrec T M0 M1) (Core.succ e))
                   (Core.app (Core.app M1 e) (Core.app (Core.nrec T M0 M1) e))
                   T[(Core.succ e)..].
*)

Lemma sc_succ M N  :
  conv Γ M N Core.tnat ->
  semantic_conv2 Γ M N Core.tnat ->
(* ------------------------- *)
  semantic_conv2 Γ (Core.succ M) (Core.succ N) Core.tnat.
Proof.
  move=> CMN SC1.
  have [TMc TNc] := conv_typing CMN.
  move=> ρ m Δ σ TS FR VS CD u a WT EM EA.
  have Vρ : valid_env ρ := fits_valid_env FR.
  (* [Red3] leaf conversions: both sides already *are* successors *)
  have TsM : typing Δ (Core.succ M[σ]) Core.tnat.
  { move: (substitution_tm _ (Core.succ M) Core.tnat _ σ
             ltac:(apply t_succ; exact TMc) TS CD) => hh. asimpl in hh. exact hh. }
  have TsN : typing Δ (Core.succ N[σ]) Core.tnat.
  { move: (substitution_tm _ (Core.succ N) Core.tnat _ σ
             ltac:(apply t_succ; exact TNc) TS CD) => hh. asimpl in hh. exact hh. }
  have cvPred : conv Δ M[σ] N[σ] Core.tnat.
  { move: (substitution_conv _ M N Core.tnat _ σ CMN TS CD) => hh.
    asimpl in hh. exact hh. }
  move=> RB Hrank. destruct RB; [ exact I | ].
  (* [u = bot] is trivial *)
  destruct (is_bot u) eqn:Bu.
  { have Eu : u = bot by (apply is_bot_eq; rewrite Bu). subst u. apply EqVal_Bot. }
  (* [u <> bot]: from [EvalRel (succ M) ρ u], [u <= succ v] and [EvalRel M ρ v] *)
  move: EM. cbn. rewrite Bu. move=> [Vu [v [LEuv EMv]]].
  destruct u as [ | | | | w | b f | g ];
    try discriminate; try (exfalso; move: LEuv; done).
  (* only [u = succ w] survives *)
  have Ea : a = tnat by (inversion WT; reflexivity). subst a.
  move: LEuv. rewrite le_succ. move=> Lwv.
  have Vw : valid w by (eapply wt_valid_tm; eapply wt_succ_inv; exact WT).
  have EMw : EvalRel M ρ w by (eapply EvalRel_down; [ exact Vρ | exact Vw | exact EMv | exact Lwv ]).
  refine (ex_intro _ M[σ]
            (conj _ (conj _ (ex_intro _ N[σ] (conj _ (conj _ (conj _ _)))))));
    [ apply ms_refl | apply c_refl; exact TsM
    | apply ms_refl | apply c_refl; exact TsN
    | exact cvPred | ].
  (* inner [EqVal M[σ] N[σ] : tnat] at the predecessor value [w] *)
  destruct (is_bot w) eqn:Bw.
  { have Ew : w = bot by (apply is_bot_eq; rewrite Bw).
    move: (wt_succ_inv WT). rewrite Ew. move=> wb. apply EqVal_Bot. }
  have RPw : 1 <= rk w := rk_pos Bw.
  have evN : EvalRel Core.tnat ρ tnat by (cbn; apply le_refl).
  apply (SC1 ρ m Δ σ TS FR VS CD w tnat (wt_succ_inv WT) EMw evN RB).
  cbn in Hrank |- *. lia.
Qed.

(* Cross-codomain PiEdgeEqTy: like [tpi_PiEdgeEqTy] but the two codomains are
   genuinely different terms [B0], [B1] (single substitution [σ]).  The codomain
   equality comes from [SCB : semantic_conv2 (Γ.A) B0 B1] applied at the extended
   substitution [P.:σ]; the domain transport [dom_transport] still uses [STA]. *)
Lemma tpi_PiEdgeEqTy_cross (A : Tm n) (B0 B1 : Tm (S n))
  (TA : typing Γ A Core.tuniv)
  (STA : semantic_typing Γ A Core.tuniv)
  (SCB : semantic_conv2 (Γ ++ A) B0 B1 Core.tuniv)
  ρ m (Δ : Ctx m) (σ : Sub n m)
  (TS : typing_subst Δ σ Γ) (Fρ : fits Γ ρ) (VS : ValSub Δ Γ σ ρ) (CΔ : ctx Δ)
  b f (WT : wt (tpi b f) tuniv)
  (evAN : EvalRel (Core.tpi A B0) ρ (tpi b f)) RB
  (Hguard : max (rk (tpi b f)) (rk tuniv) < S RB) :
  PiEdgeEqTy RB Δ A[σ] B0[⇑ σ] B1[⇑ σ] WT.
Proof.
  have Vρ : valid_env ρ := fits_valid_env Fρ.
  cbn in Hguard.
  cbn [Rec.PiEdgeEqTy].
  move=> u v Sel WTu P TP VP.
  move: (evAN) => Hpi. cbn in Hpi.
  move: Hpi => [Vb [Vf [evAdom [a' [evAdom' EFun]]]]].
  have Vu : valid u := wt_valid_tm WTu.
  destruct (is_bot v) eqn:Bv.
  { have Ev : v = bot by (apply is_bot_eq; rewrite Bv). subst v. apply EqVal_Bot. }
  have RPv : 1 <= rk v := rk_pos Bv.
  have RKu : rk u <= rk_fun f := rk_Selection_key Sel.
  have RKv : rk v <= rk_fun f := rk_Selection_val Sel.
  set WT_ := (wt_Selection_codU WT Sel).
  have Vv : valid v := wt_valid_tm WT_.
  have VPall : forall RB0, max (rk u) (rk b) < RB0 -> Val RB0 Δ P A[σ] WTu.
  { move=> RB0 Hr0. eapply (Val_fuel_any (k := RB)); [ lia | lia | lia | lia | exact VP ]. }
  have HYP1 := dom_transport (A := A) STA Fρ TS VS CΔ (ρ := ρ) (Δ := Δ) (σ := σ) (N := P)
                 (b := b) (u' := u) (WTu' := WTu) evAdom VPall.
  have VS1 : ValSub Δ (Γ ++ A) (P .: σ) (u .: ρ)
    by (eapply ValSub_cons; [ exact HYP1 | exact VS ]).
  have leV : le v (app f u)
    by (eapply Selection_le_app; [ exact Vf | exact Vf | apply le_fun_refl; exact Vf | exact Vu | exact Sel ]).
  destruct (EFun u (app f u) Vu erefl) as [x [WTx [Lexu EBxa]]].
  have Vx : valid x := wt_valid_tm WTx.
  have EBxv : EvalRel B0 (x .: ρ) v.
  { eapply EvalRel_down;
      [ apply valid_cons; [ exact Vx | exact Vρ ] | exact Vv | exact EBxa | exact leV ]. }
  have EBuv : EvalRel B0 (u .: ρ) v.
  { eapply EvalRel_mono_env;
      [ exact EBxv
      | apply valid_cons; [ exact Vx | exact Vρ ]
      | apply valid_cons; [ exact Vu | exact Vρ ]
      | apply le_env_cons; [ exact Lexu | apply le_env_refl; exact Vρ ] ]. }
  have evU' : EvalRel Core.tuniv (u .: ρ) tuniv by (cbn; apply le_refl).
  have TS1 : typing_subst Δ (P .: σ) (Γ ++ A)
    by (eapply typing_subst_cons; [ exact TP | exact TS ]).
  have Fits : fits (Γ ++ A) (u .: ρ)
    by (eapply fits_cons; [ exact TA | exact evAdom | eapply wt_ty_tuniv; exact WTu | exact WTu | exact Fρ ]).
  have eqvalB := SCB (u .: ρ) m Δ (P .: σ) TS1 Fits VS1 CΔ v tuniv WT_ EBuv evU'.
  have HrV : max (rk v) (rk tuniv) < RB by (cbn; lia).
  move: (eqvalB RB HrV) => HvB.
  rewrite (subst_cons_eq B0 P σ) (subst_cons_eq B1 P σ) in HvB.
  exact HvB.
Qed.

(** Π congruence (Agda [adequacyE2-Pi]): [A0 ≡ A1] and [B0 ≡ B1] give
    [tpi A0 B0 ≡ tpi A1 B1 : tuniv].  Needs full [semantic_typing] of the four
    components because Coq's [EqValTy] bundles [ValTy] of both sides; the shared
    value for the right side comes from [conv_EvalRel]'s forward transport. *)
Lemma sc_tpi A0 A1 (B0 B1 : Tm (S n)) :
  typing Γ A0 Core.tuniv ->
  typing Γ A1 Core.tuniv ->
  typing (Γ ++ A0) B0 Core.tuniv ->
  typing (Γ ++ A1) B1 Core.tuniv ->
  conv Γ A0 A1 Core.tuniv ->
  conv (Γ ++ A0) B0 B1 Core.tuniv ->
  semantic_typing Γ A0 Core.tuniv ->
  semantic_typing Γ A1 Core.tuniv ->
  semantic_typing (Γ ++ A0) B0 Core.tuniv ->
  semantic_typing (Γ ++ A1) B1 Core.tuniv ->
  semantic_conv2 Γ A0 A1 Core.tuniv ->
  semantic_conv2 (Γ ++ A0) B0 B1 Core.tuniv ->
(* ------------------------- *)
  semantic_conv2 Γ (Core.tpi A0 B0) (Core.tpi A1 B1) Core.tuniv.
Proof.
  move=> TA0 TA1 TB0 TB1 CA CB STA0 STA1 STB0 STB1 SCA SCB.
  move=> ρ m Δ σ TS FR VS CD u a WT evM evA.
  have Vρ : valid_env ρ := fits_valid_env FR.
  have evU : EvalRel Core.tuniv ρ tuniv by (cbn; apply le_refl).
  have CPI : conv Γ (Core.tpi A0 B0) (Core.tpi A1 B1) Core.tuniv
    by (eapply c_tpi; [ exact TA0 | exact TA1 | exact TB0 | exact TB1 | exact CA | exact CB ]).
  move: (conv_EvalRel CPI FR) => [_ [_ [fwd _]]].
  have evN : EvalRel (Core.tpi A1 B1) ρ u := fwd u evM.
  have CAσ : typing Δ A0[σ] Core.tuniv
    by (eapply substitution_tm with (A := Core.tuniv); eauto).
  have CE : ctx (Δ ++ A0[σ]) by (eapply c_cons; [ exact CD | exact CAσ ]).
  have TSlift : typing_subst (Δ ++ A0[σ]) (⇑ σ) (Γ ++ A0)
    by (eapply typing_subst_lift; [ exact CE | exact TS ]).
  have convA0A1 : conv Δ A0[σ] A1[σ] Core.tuniv
    := substitution_conv Γ A0 A1 Core.tuniv Δ σ CA TS CD.
  have convB0B1 : conv (Δ ++ A0[σ]) B0[⇑ σ] B1[⇑ σ] Core.tuniv
    := substitution_conv (Γ ++ A0) B0 B1 Core.tuniv (Δ ++ A0[σ]) (⇑ σ) CB TSlift CE.
  move=> RB Hrank. destruct RB; [ exact I | ].
  have evM0 := evM. cbn in evM.
  destruct u as [ | | | | | b f | ]; try done.
  - (* u = bot *) apply EqVal_Bot.
  - (* u = tpi b f *)
    move: evM => [Vb [Vf [evAdom [a' [evAdom' EFun]]]]].
    have Eatu : a = tuniv by (inversion WT; auto). subst a.
    have VMv : Val (S RB) Δ (Core.tpi A0 B0)[σ] Core.tuniv[σ] WT.
    { eapply st_tpi_Val_edge with (σ' := σ); try eassumption.
      - exact (ConvSub_refl TS).
      - exact (ValSub_EqValSub VS). }
    have VNv : Val (S RB) Δ (Core.tpi A1 B1)[σ] Core.tuniv[σ] WT.
    { eapply st_tpi_Val_edge with (σ' := σ); try eassumption.
      - exact (ConvSub_refl TS).
      - exact (ValSub_EqValSub VS). }
    rewrite Val_tuniv in VMv. rewrite Val_tuniv in VNv.
    have eqA := SCA ρ m Δ σ TS FR VS CD b tuniv (wt_tpi_dom WT) evAdom evU.
    have eqDom : EqVal RB Δ A0[σ] A1[σ] Core.tuniv (wt_tpi_dom WT).
    { destruct (le_lt_dec 2 RB) as [HRB|HRB].
      - eapply EqVal_irr; eapply eqA; cbn in Hrank |- *; lia.
      - have Eb : b = bot by (apply rk_bot_inv; cbn in Hrank; lia).
        move: (wt_tpi_dom WT). rewrite Eb. move=> w. apply EqVal_Bot. }
    rewrite EqVal_tuniv.
    split; [ exact VMv | ]. split; [ exact VNv | ].
    cbn [Rec.EqValTy].
    split; [ exact VMv | ]. split; [ exact VNv | ].
    exists A0[σ], B0[⇑ σ]. split; [ apply ms_refl | ].
    exists A1[σ], B1[⇑ σ]. split; [ apply ms_refl | ].
    split; [ exact convA0A1 | ].
    split; [ exact convB0B1 | ].
    split; [ exact (wt_valid_tm WT) | ].
    split; [ exact eqDom | ].
    eapply tpi_PiEdgeEqTy_cross; (try eassumption); exact Hrank.
Qed.

(** Lambda congruence: [A ≡ A'] and [M ≡ M'] give [abs A M ≡ abs A' M' : tpi A B].
    (No Agda counterpart: the MIN conversion judgment derives a Lam congruence
    from [funext] rather than taking it as a rule.)  Needs full
    [semantic_typing] of the components since Coq's [EqVal]-at-Π bundles both
    [ValPi]s; the right lambda is valued at the off-diagonal type [tpi A B],
    handled by the [Alam]-generalised [st_abs_Val_edge]. *)
Lemma sc_abs (A A' : Tm n) (B M M' : Tm (S n)) :
  typing Γ A Core.tuniv ->
  typing Γ A' Core.tuniv ->
  typing (Γ ++ A) B Core.tuniv ->
  typing (Γ ++ A) M B ->
  typing (Γ ++ A) M' B ->
  conv Γ A A' Core.tuniv ->
  conv (Γ ++ A) M M' B ->
  semantic_typing Γ A Core.tuniv ->
  semantic_typing (Γ ++ A) B Core.tuniv ->
  semantic_typing (Γ ++ A) M B ->
  semantic_typing (Γ ++ A) M' B ->
  semantic_conv2 (Γ ++ A) M M' B ->
(* ------------------------- *)
  semantic_conv2 Γ (Core.abs A M) (Core.abs A' M') (Core.tpi A B).
Proof.
  move=> TA TA' TB TM TM' CA CM STA STB STM STM' SCM.
  have CAA : conv Γ A A Core.tuniv by (apply c_refl; exact TA).
  move=> ρ m Δ σ TS FR VS CD u a WT evM evA.
  have Vρ : valid_env ρ := fits_valid_env FR.
  have evU : EvalRel Core.tuniv ρ tuniv by (cbn; apply le_refl).
  (* the Π-code conversion stored by [EqValPi]: the type term already *is* the
     Π-normal form *)
  have CPiσ : conv Δ (Core.tpi A[σ] B[⇑ σ]) (Core.tpi A[σ] B[⇑ σ]) Core.tuniv.
  { apply c_refl.
    move: (substitution_tm _ (Core.tpi A B) Core.tuniv _ σ
             ltac:(apply t_tpi; [ exact TA | exact TB ]) TS CD) => hh.
    asimpl in hh. exact hh. }
  have CABS : conv Γ (Core.abs A M) (Core.abs A' M') (Core.tpi A B)
    by (eapply c_abs;
        [ exact TA | exact TA' | exact TB | exact TM | exact TM' | exact CA | exact CM ]).
  move: (conv_EvalRel CABS FR) => [_ [_ [fwd _]]].
  have evN : EvalRel (Core.abs A' M') ρ u := fwd u evM.
  move=> RB Hrank. destruct RB; [ exact I | ].
  have evM0 := evM. have evA0 := evA.
  cbn in evM. cbn in evA.
  destruct u as [ | | | | | | g_val ]; try done.
  - (* u = bot *) apply EqVal_Bot.
  - (* u = abs g_val *)
    destruct a as [ | | | | | b f_ty | ];
      try solve [ cbn in evA; done | exfalso; clear -WT; inversion WT ].
    move: evM => [Vg [NBg [a_d [WTad [ERA_ad EFunM]]]]].
    move: evA => [Vb [Vf_ty [ERA_b [a'_T [ERA_aT EFunB]]]]].
    have bodyM : forall u0 v0, Selection g_val u0 v0 -> valid u0 -> EvalRel M (u0 .: ρ) v0.
    { move=> u0 v0 Sel Vu0.
      have Vv0 : valid v0 := wt_valid_tm (wt_Selection_abs WT Sel).
      have leV : le v0 (app g_val u0)
        by (eapply Selection_le_app; [ exact Vg | exact Vg | apply le_fun_refl; exact Vg | exact Vu0 | exact Sel ]).
      destruct (EFunM u0 (app g_val u0) Vu0 erefl) as [x [WTx [Lex EBx]]].
      have Vx : valid x := wt_valid_tm WTx.
      have EBxv : EvalRel M (x .: ρ) v0
        by (eapply EvalRel_down; [ apply valid_cons; [ exact Vx | exact Vρ ] | exact Vv0 | exact EBx | exact leV ]).
      eapply EvalRel_mono_env;
        [ exact EBxv | apply valid_cons; [ exact Vx | exact Vρ ]
        | apply valid_cons; [ exact Vu0 | exact Vρ ]
        | apply le_env_cons; [ exact Lex | apply le_env_refl; exact Vρ ] ]. }
    have bodyB : forall u0, valid u0 -> EvalRel B (u0 .: ρ) (app f_ty u0).
    { move=> u0 Vu0.
      destruct (EFunB u0 (app f_ty u0) Vu0 erefl) as [y [WTy [Ley EBy]]].
      have Vy : valid y := wt_valid_tm WTy.
      eapply EvalRel_mono_env;
        [ exact EBy | apply valid_cons; [ exact Vy | exact Vρ ]
        | apply valid_cons; [ exact Vu0 | exact Vρ ]
        | apply le_env_cons; [ exact Ley | apply le_env_refl; exact Vρ ] ]. }
    (* the two [ValPi]s, from the (Alam-generalised) Lam value edge *)
    have VM : Val (S RB) Δ (Core.abs A M)[σ] (Core.tpi A B)[σ] WT.
    { eapply st_abs_Val_edge with (σ' := σ); try eassumption.
      - exact (ConvSub_refl TS).
      - exact (ValSub_EqValSub VS). }
    have VN : Val (S RB) Δ (Core.abs A' M')[σ] (Core.tpi A B)[σ] WT.
    { eapply st_abs_Val_edge with (σ' := σ); try eassumption.
      - exact (ConvSub_refl TS).
      - exact (ValSub_EqValSub VS). }
    rewrite Val_abs in VM. rewrite Val_abs in VN.
    move: VM => [VTd VPiM]. move: VN => [_ VPiN].
    rewrite EqVal_abs.
    split; [ exact VTd | ]. split; [ exact VPiM | ]. split; [ exact VPiN | ].
    (* the cross [EqValPi] edge: related results from related bodies via [SCM] *)
    exists A[σ], B[⇑ σ]. split; [ apply ms_refl | ]. split; [ exact CPiσ | ].
    cbn [Rec.PiAppEqVal]. move=> u0 v0 Sel WTu0 P TP VP.
    have Vu0 : valid u0 := wt_valid_tm WTu0.
    have RKu0 : rk u0 <= rk_fun g_val := rk_Selection_key Sel.
    have RKv0 : rk v0 <= rk_fun g_val := rk_Selection_val Sel.
    have RKapp : rk (app f_ty u0) <= rk_fun f_ty := rk_app f_ty u0.
    have VPall : forall RB0, max (rk u0) (rk b) < RB0 -> Val RB0 Δ P A[σ] WTu0.
    { move=> RB0 Hr0. eapply (Val_fuel_any (k := RB)); [ cbn in Hrank; lia | cbn in Hrank; lia | lia | lia | exact VP ]. }
    have EVall : forall RB0, max (rk u0) (rk b) < RB0 -> EqVal RB0 Δ P P A[σ] WTu0.
    { move=> RB0 Hr0. eapply Val_EqVal; exact (VPall RB0 Hr0). }
    have HYP1 := dom_transport (A := A) STA FR TS VS CD (ρ := ρ) (Δ := Δ) (σ := σ) (N := P)
                   (b := b) (u' := u0) (WTu' := WTu0) ERA_b VPall.
    have HYPE := dom_transport_eq (A := A) STA FR TS VS CD (ρ := ρ) (Δ := Δ) (σ := σ) (N1 := P) (N2 := P)
                   (b := b) (u' := u0) (WTu' := WTu0) ERA_b EVall.
    have VS1 : ValSub Δ (Γ ++ A) (P .: σ) (u0 .: ρ)
      by (eapply ValSub_cons; [ exact HYP1 | exact VS ]).
    have EVS1 : EqValSub Δ (Γ ++ A) (P .: σ) (P .: σ) (u0 .: ρ)
      by (eapply EqValSub_cons; [ exact HYPE | exact (ValSub_EqValSub VS) ]).
    have TS1 : typing_subst Δ (P .: σ) (Γ ++ A)
      by (eapply typing_subst_cons; [ exact TP | exact TS ]).
    have Fits : fits (Γ ++ A) (u0 .: ρ)
      by (eapply fits_cons; [ exact TA | exact ERA_b | eapply wt_ty_tuniv; exact WTu0 | exact WTu0 | exact FR ]).
    have eqvalBody :=
      SCM (u0 .: ρ) m Δ (P .: σ) TS1 Fits VS1 CD v0 (app f_ty u0)
          (wt_Selection_abs WT Sel) (bodyM u0 v0 Sel Vu0) (bodyB u0 Vu0).
    have HrB : max (rk v0) (rk (app f_ty u0)) < RB by (cbn in Hrank; lia).
    move: (eqvalBody RB HrB) => HvB.
    rewrite (subst_cons_eq M P σ) (subst_cons_eq M' P σ) (subst_cons_eq B P σ) in HvB.
    eapply EqVal_headred_expand;
      [ eapply ms_trans; [ apply hr_beta | apply ms_refl ]
      | eapply ms_trans; [ apply hr_beta | apply ms_refl ]
      | eapply beta_step_conv;
          [ exact TA | exact TA | exact CAA | exact TB | exact TM
          | exact TS | exact CD | exact TP ]
      | (* the right lambda is annotated with [A'], only *convertible* to the
           Π-domain [A] — exactly what [beta_step_conv] is generalised over *)
        eapply beta_step_conv;
          [ exact TA' | exact TA | exact CA | exact TB | exact TM'
          | exact TS | exact CD | exact TP ]
      | exact HvB ].
Qed.


End SemanticTyping.


(*
------------------------------------------------------------------------
-- Main mutual block — adequacySub / adequacyEqSub
------------------------------------------------------------------------
*)


(* well-typed terms are semantically typed.  *)
Fixpoint adequacySub {g} (Γ : Ctx g) (M A : Tm g) :
  typing Γ M A -> semantic_typing Γ M A
with adequacyEqSub {g} (Γ : Ctx g) (M N A : Tm g) :
  conv Γ M N A -> semantic_conv2 Γ M N A.
Proof. 
  - move=> h. dependent destruction h.
    + eapply st_var; eauto.
    + eapply st_conv; eauto.
    + eapply st_abs; eauto.
    + eapply st_app; eauto.
    + eapply st_nat; eauto.
    + eapply st_zero; eauto.
    + eapply st_succ; eauto.
    + (* st_case: adequacy for ncase — TODO *) admit.
    + eapply st_tpi; eauto.
    + eapply st_univ; eauto.
  - move=> h. dependent destruction h.
    + eapply sc_conv; eauto.
    + eapply sc_refl; eauto. 
    + eapply sc_sym; eauto.
    + eapply sc_trans; eauto.
    + eapply sc_app1; eauto.
    + eapply sc_app2; eauto.
    + eapply sc_beta; eauto.
    + eapply sc_eta; eauto.
    + (* sc_ncase_Z — TODO *) admit.
    + (* sc_ncase_S — TODO *) admit.
    + (* sc_ncase — TODO *) admit.
    + eapply sc_succ; eauto.
    + eapply sc_abs; eauto.
    + eapply sc_tpi; eauto.
Admitted.

Definition empty {n} : fin 0 -> Tm n := 
  fun f => match f with end. 


(* ===========================================================
   Translation of PiInjectivity.agda

   Corollary 6 (paper p.661): Pi injectivity.

   If conv Γ A₀ (tpi B₁ F₁) (tuniv i), then there exist B₀, F₀ with
     (1) HeadRed A₀ (tpi B₀ F₀)
     (2) conv Γ B₀ B₁ (tuniv i)
     (3) conv (Γ ++ B₀) F₀ F₁ (tuniv i)

   As a corollary (piInjectivity):
   conv Γ (tpi A₀ B₀) (tpi A₁ B₁) (tuniv i) implies
     conv Γ A₀ A₁ (tuniv i)  and  conv (Γ ++ A₀) B₀ B₁ (tuniv i).

   The full proof in Agda goes through adequacyEqSub2 applied at
   bot_env with idSub. The Coq Val/EqVal relations defined in
   raw_validity2.v live in ctx_empty (after closing substitution),
   so the analogous adequacy is not directly available; piConv
   below is therefore stated and admitted.
   =========================================================== *)

From Stdlib Require Import FunctionalExtensionality.

(* bot_env_lookup: bot_env always returns bot *)
Lemma bot_env_lookup {n} (i : fin n) : (@bot_env n) i = bot.
Proof. unfold bot_env. reflexivity. Qed.

(* bot_env at S n agrees with bot .: bot_env *)
Lemma bot_env_cons {n} : @bot_env (S n) = bot .: bot_env.
Proof. apply functional_extensionality. by case. Qed.

(* bot_env at 0 agrees with null *)
Lemma bot_env_null : @bot_env 0 = null.
Proof. apply functional_extensionality. by case. Qed.

(* fits Γ bot_env: trivially satisfied with a = bot, u = bot at every
   variable. Mirrors botEnv-fits in PiInjectivity.agda. *)
Lemma fits_bot_env {n} (Γ : Ctx n) : ctx Γ -> fits Γ bot_env.
Proof.
  induction 1.
  - rewrite bot_env_null. exact fits_empty.
  - rewrite bot_env_cons.
    eapply (@fits_cons _ _ _ _ bot bot); eauto.
    + apply EvalRel_bot.
    + eapply wt_bot. eapply wt_tuniv.
    + eapply wt_bot. eapply wt_bot. eapply wt_tuniv. 
Qed.

(** The identity substitution is semantically well-typed against the everywhere
    -[bot] environment ([botEnv-validSub2]); used to instantiate adequacy at the
    trivial environment for Π-injectivity. *)
Lemma ValSub_id n (Γ:Ctx n) :
  ValSub Γ Γ var bot_env.
Proof.
  unfold ValSub.
  move=> i u Vu LE a ER h RB Hrank.
  unfold bot_env in LE.
  apply le_bot_inv in LE. subst.
  apply Val_Bot.
Qed.


Lemma EqValSub_id n (Γ:Ctx n) :
  EqValSub Γ Γ var var bot_env.
Proof.
  unfold EqValSub.
  move=> i u Vu LE a ER h RB Hrank.
  unfold bot_env in LE.
  apply le_bot_inv in LE. subst.
  apply EqVal_Bot.
Qed.

(** Every Π-type evaluates to the trivial Π-code [tpi bot nil] (Agda:
    [evalRel-Pi-trivial]).  This is the seed that exposes a Π-code at the
    bottom environment, where the type edges can be read off. *)
Lemma evalRel_Pi_trivial {n} (A : Tm n) (B : Tm (S n)) (ρ : Env n) :
  EvalRel (Core.tpi A B) ρ (tpi bot nil).
Proof.
  (* Mirrors evalRel-Pi-trivial: the Pi type relates at the trivial code
     [tpi bot nil] — domain/codomain both [bot], empty graph. *)
  cbn.
  split; [ done | ]. split; [ done | ].
  split; [ apply EvalRel_bot | ].
  exists bot. split; [ apply EvalRel_bot | ].
  move=> u v Vu APP. subst v.
  exists bot, (wt_bot (wt_bot wt_tuniv)).
  split; [ apply le_bot' | apply EvalRel_bot ].
Qed.

(** [piConv] (Agda: [piConv] / [convPi2]): from a conversion
    [A0 ≡ tpi B1 F1 : tuniv], recover that [A0] head-reduces to some Π-type
    [tpi B0 F0] whose domain and codomain are convertible to [B1], [F1].  The
    engine: evaluate at the bottom environment, transport the trivial Π code via
    conversion soundness, then run adequacy ([semantic_conv2]) and read the
    components off the resulting [EqValTy]. *)
Lemma piConv {n} (Γ : Ctx n) (A0 : Tm n) (B1 : Tm n) (F1 : Tm (S n)) :
  conv Γ A0 (Core.tpi B1 F1) Core.tuniv ->
  exists B0 F0,
    HeadRed A0 (Core.tpi B0 F0)
    /\ conv Γ B0 B1 Core.tuniv
    /\ conv (Γ ++ B0) F0 F1 Core.tuniv.
Proof.
  (* Mirrors PiInjectivity.agda [piConv]: evaluate at [bot_env]/[var],
     transfer the trivial Pi evaluation [tpi bot nil] from [tpi B1 F1] to
     [A0] via conversion soundness, then run [adequacyEqSub] (semantic_conv2)
     to obtain [EqVal], whose [EqValTy] component at [tpi bot nil] exposes
     [HeadRed A0 (tpi B0 F0)] and the domain/codomain conversions. *)
  move=> d.
  have cΓ : ctx Γ by eapply conv_ctx; exact d.
  (* well-typedness of the trivial Pi code [tpi bot nil] *)
  have WT : wt (tpi bot nil) tuniv.
  { apply: wt_tpi.
    - apply wt_bot. apply wt_tuniv.
    - move=> ui vi [].
    - move=> ui vi [].
    - done. }
  (* trivial Pi evaluation, transferred to A0 along the conversion *)
  have evPi : EvalRel (Core.tpi B1 F1) bot_env (tpi bot nil)
    by apply evalRel_Pi_trivial.
  have IC : InvConv Γ A0 (Core.tpi B1 F1) Core.tuniv bot_env.
  { eapply conv_EvalRel. exact d. exact (@fits_bot_env n Γ cΓ). }
  move: IC => [_ [_ [_ bwd]]].
  have evA0 : EvalRel A0 bot_env (tpi bot nil) by apply bwd; exact evPi.
  have evU : EvalRel Core.tuniv (@bot_env n) tuniv by [].
  (* reify the conversion adequacy as a [semantic_conv2] hypothesis, then
     instantiate it at [σ := var], [ρ := bot_env] via [eapply], discharging
     the substitution/validity premises with their identity lemmas. *)
  have SCA : semantic_conv2 Γ A0 (Core.tpi B1 F1) Core.tuniv.
  { apply adequacyEqSub; exact d. }
  (* fuel 2: above the rank of the trivial code [tpi bot nil] (rk 1) and of
     [tuniv] (rk 1), as the canonical-fuel [semantic_conv2] now requires. *)
  have EVfun : EqVal 2 Γ A0[var] (Core.tpi B1 F1)[var] Core.tuniv[var] WT.
  { eapply SCA.
    - apply typing_subst_id. exact cΓ.
    - apply fits_bot_env. exact cΓ.
    - apply ValSub_id.
    - exact cΓ.
    - exact evA0.
    - exact evU.
    - cbn; lia. }
  have EV1 := EVfun.
  unfold subst1, Subst_Tm in EV1.
  rewrite (instId'_Tm A0) (instId'_Tm (Core.tpi B1 F1)) (instId'_Tm Core.tuniv) in EV1.
  have EVT := EqVal_EqValTy EV1.
  clear EV1 EVfun.
  (* expose [WT]'s constructor form so the [{struct h}] [EqValTy] fixpoint
     iota-reduces *)
  dependent destruction WT.
  cbn [Rec.EqValTy] in EVT.
  move: EVT => [_ [_ [B0 [F0 [HRA0 [A' [B' [HRPi [cD [cC _]]]]]]]]]].
  have [EA EB] := HeadRed_tpi_eq HRPi. subst A' B'.
  exists B0, F0. split; [ exact HRA0 | split; [ exact cD | exact cC ] ].
Qed.

(** Π-injectivity (Agda: [piInjectivity]) — the headline corollary of adequacy:
    a conversion between two Π-types entails convertibility of their domains and
    codomains.  Obtained from [piConv] plus determinacy of head reduction on the
    Π head-normal form. *)
Lemma piInjectivity {n} (Γ : Ctx n)
  (A0 A1 : Tm n) (B0 B1 : Tm (S n)) :
  conv Γ (Core.tpi A0 B0) (Core.tpi A1 B1) Core.tuniv ->
  conv Γ A0 A1 Core.tuniv /\
  conv (Γ ++ A0) B0 B1 Core.tuniv.
Proof.
  move=> H.
  destruct (piConv H) as [B0' [F0' [HR [convD convC]]]].
  (* HR : HeadRed (tpi A0 B0) (tpi B0' F0').
     Pi is a head-normal form, so by determinacy of HeadRed on Pi
     we have B0' = A0 and F0' = B0. *)
  have [EQA EQB]: B0' = A0 /\ F0' = B0.
  { eapply HeadRed_tpi_det. exact HR. apply ms_refl. }
  subst B0' F0'.
  split; auto.
Qed.

(** * Subject reduction (Agda: [SubjectReduction.agda])

    Port of the Agda [subject-red1]: typing is preserved by single-step head
    reduction.  The β-case inverts the [abs] typing through conversion
    ([typing_abs_inv]) and uses Π-injectivity ([piInjectivity]) to align the
    domain/codomain, exactly as the Agda [ty-Lam-body] helper does, then
    substitutes ([substitution_tm]). *)

(* Inversion of a head reduction whose redex is an application. *)
Lemma HeadRed1_app_inv {n} (F a N' : Tm n) :
  HeadRed1 (Core.app F a) N' ->
  (exists A0 M', F = Core.abs A0 M' /\ N' = M'[a..]) \/
  (exists F2, HeadRed1 F F2 /\ N' = Core.app F2 a).
Proof.
  move=> h. inversion h; subst.
  - left. do 2 eexists. split; reflexivity.
  - right. eexists. split; [ eassumption | reflexivity ].
Qed.

(* Inversion of a head reduction whose redex is a case analysis. *)
Lemma HeadRed1_ncase_inv {n} (M M0 : Tm n) (M1 : Tm (S n)) (N' : Tm n) :
  HeadRed1 (Core.ncase M M0 M1) N' ->
  (M = Core.zero /\ N' = M0)
  \/ (exists P, M = Core.succ P /\ N' = M1[P..])
  \/ (exists M', HeadRed1 M M' /\ N' = Core.ncase M' M0 M1).
Proof.
  move=> h. inversion h; subst.
  - left. split; reflexivity.
  - right; left. eexists. split; reflexivity.
  - right; right. eexists. split; [ eassumption | reflexivity ].
Qed.

(** Head reduction is contained in conversion, for well-typed terms.  Each
    contraction is exactly one of the computation rules ([c_beta],
    [c_ncase_Z], [c_ncase_S]) and each congruence step is [c_app1]/[c_ncase].
    The β-case needs the abstraction's own domain, so it goes through
    [typing_abs_inv] + [piInjectivity] — which is why this lemma has to come
    *after* adequacy rather than in the syntactic layer. *)
Lemma red1_conv {n} (Γ : Ctx n) (M A : Tm n) :
  typing Γ M A -> forall N, HeadRed1 M N -> conv Γ M N A.
Proof.
  induction 1 as
    [ n Γ x cΓ
    | n Γ M A B tM IHM cAB
    | n Γ A B P tA IHA tB IHB tP IHP
    | n Γ A B F a tA IHA tB IHB tF IHF ta IHa
    | n Γ cΓ
    | n Γ cΓ
    | n Γ P tP IHP
    | n Γ T Mc Mc0 Mc1 tT IHT tMc IHMc tMc0 IHMc0 tMc1 IHMc1
    | n Γ A B tA IHA tB IHB
    | n Γ cΓ ]; intros N' hr.
  all: try solve [ inversion hr ].
  - (* t_conv: peel the conversion, recurse, re-wrap. *)
    eapply c_conv; [ eapply IHM; exact hr | exact cAB ].
  - (* t_app on [app F a] : B[a..] *)
    apply HeadRed1_app_inv in hr.
    destruct hr as [ [A0 [M' [-> ->]]] | [F2 [hrF ->]] ].
    + (* β: the redex is [app (abs A0 M') a].  [c_beta] wants everything at the
         abstraction's *own* domain [A0], so move [a] and [B] across [cA]. *)
      destruct (typing_abs_inv _ _ _ _ _ tF) as [B2 [tM' cPi]].
      destruct (piInjectivity cPi) as [cA cB].
      have tA0 : typing Γ A0 Core.tuniv by (exact (proj1 (conv_typing cA))).
      have tBA0 : typing (Γ ++ A0) B Core.tuniv
        by (eapply ctx_conv_typing; [ apply c_sym; exact cA | exact tB ]).
      have tM'B : typing (Γ ++ A0) M' B by (eapply t_conv; [ exact tM' | exact cB ]).
      have taA0 : typing Γ a A0 by (eapply t_conv; [ exact ta | apply c_sym; exact cA ]).
      eapply c_beta; [ exact tA0 | exact tBA0 | exact tM'B | exact taA0 ].
    + (* congruence: the function reduces. *)
      eapply c_app1; [ exact tA | exact tB | eapply IHF; exact hrF | exact ta ].
  - (* t_case on [ncase Mc Mc0 Mc1] : T[Mc..] *)
    apply HeadRed1_ncase_inv in hr.
    destruct hr as [ [-> ->] | [ [P [-> ->]] | [Mc' [hrM ->]] ] ].
    + eapply c_ncase_Z; [ exact tT | exact tMc0 | exact tMc1 ].
    + eapply c_ncase_S;
        [ exact tT | exact (typing_succ_arg_inv tMc) | exact tMc0 | exact tMc1 ].
    + eapply c_ncase;
        [ exact tT | eapply IHMc; exact hrM
        | apply c_refl; exact tMc0 | apply c_refl; exact tMc1 ].
Qed.

(* Agda: subject-red1 : HasType G M A -> HeadRed1 M N -> HasType G N A *)
Lemma subject_red1 {n} (Γ : Ctx n) (M A : Tm n) :
  typing Γ M A -> forall N, HeadRed1 M N -> typing Γ N A.
Proof.
  induction 1 as
    [ n Γ x cΓ
    | n Γ M A B tM IHM cAB
    | n Γ A B P tA IHA tB IHB tP IHP
    | n Γ A B F a tA IHA tB IHB tF IHF ta IHa
    | n Γ cΓ
    | n Γ cΓ
    | n Γ P tP IHP
    | n Γ T Mc Mc0 Mc1 tT IHT tMc IHMc tMc0 IHMc0 tMc1 IHMc1
    | n Γ A B tA IHA tB IHB
    | n Γ cΓ ]; intros N' hr.
  all: try solve [ inversion hr ].
  - (* t_conv: peel the conversion, recurse, re-wrap. *)
    eapply t_conv; [ eapply IHM; exact hr | exact cAB ].
  - (* t_app on [app F a] : B[a..] *)
    apply HeadRed1_app_inv in hr.
    destruct hr as [ [A0 [M' [-> ->]]] | [F2 [hrF ->]] ].
    + (* β: F = abs A0 M'.  Invert the Lam typing, align via Π-injectivity. *)
      destruct (typing_abs_inv _ _ _ _ _ tF) as [B2 [tM' cPi]].
      destruct (piInjectivity cPi) as [cA cB].
      have tM'A : typing (Γ ++ A) M' B2
        by (eapply ctx_conv_typing; [ exact cA | exact tM' ]).
      have cBA : conv (Γ ++ A) B2 B Core.tuniv
        by (eapply ctx_conv_conv; [ exact cA | exact cB ]).
      have tM'B : typing (Γ ++ A) M' B
        by (eapply t_conv; [ exact tM'A | exact cBA ]).
      eapply substitution_tm.
      * exact tM'B.
      * eapply typing_subst_cons.
        -- asimpl. exact ta.
        -- apply typing_subst_id. eapply typing_ctx; exact ta.
      * eapply typing_ctx; exact ta.
    + (* congruence: the function reduces. *)
      eapply t_app; [ exact tA | exact tB | eapply IHF; exact hrF | exact ta ].
  - (* t_case on [ncase Mc Mc0 Mc1] : T[Mc..] *)
    apply HeadRed1_ncase_inv in hr.
    destruct hr as [ [-> ->] | [ [P [-> ->]] | [Mc' [hrM ->]] ] ].
    + (* hr_zero: the result is the zero branch, already at [T[zero..]]. *)
      exact tMc0.
    + (* hr_succ: the result is the successor branch instantiated at the
         predecessor; [T[rho][P..]] is [T[(succ P)..]] by [asimpl]. *)
      have tP : typing Γ P Core.tnat by (exact (typing_succ_arg_inv tMc)).
      have cΓ : ctx Γ by (eapply typing_ctx; exact tMc).
      have TS : typing_subst Γ (P..) (Γ ++ Core.tnat)
        by (eapply typing_subst_cons;
            [ asimpl; exact tP | apply typing_subst_id; exact cΓ ]).
      move: (substitution_tm _ Mc1 T[rho] _ (P..) tMc1 TS cΓ) => h.
      unfold rho in h. asimpl in h. exact h.
    + (* hr_case: the scrutinee reduces, so the motive must be transported
         along [conv Mc' Mc] — which is where [red1_conv] is needed. *)
      have tMc' : typing Γ Mc' Core.tnat by (eapply IHMc; exact hrM).
      have cΓ : ctx Γ by (eapply typing_ctx; exact tMc).
      eapply t_conv.
      * eapply t_case; [ exact tT | exact tMc' | exact tMc0 | exact tMc1 ].
      * eapply conv_subst_arg;
          [ apply t_nat; exact cΓ | exact tT | exact tMc' | exact tMc
          | apply c_sym; eapply red1_conv; [ exact tMc | exact hrM ] ].
Qed.

(* Subject reduction for multi-step head reduction. *)
Lemma subject_red {n} (Γ : Ctx n) (M N A : Tm n) :
  typing Γ M A -> HeadRed M N -> typing Γ N A.
Proof.
  move=> H hr. move: A H. induction hr as [ e | e1 e2 e3 s _ IH ]; intros A H.
  - exact H.
  - apply IH. eapply subject_red1; eassumption.
Qed.

(** * Consistency: distinct type formers are not convertible.

    [tnat] and [tpi A B] cannot be convertible at the universe.  If they were,
    [piConv] would head-reduce [tnat] to a Π-code, but [tnat] is a head-normal
    form (no [HeadRed1] step applies to it), so the only reduction sequence out
    of it is the empty one — contradicting [tnat = tpi B0 F0]. *)
Lemma tnat_not_tpi {n} (Γ : Ctx n) (A : Tm n) (B : Tm (S n)) :
  ~ conv Γ Core.tnat (Core.tpi A B) Core.tuniv.
Proof.
  move=> H.
  destruct (piConv H) as [B0 [F0 [HR _]]].
  (* HR : HeadRed Core.tnat (Core.tpi B0 F0) *)
  inversion HR; subst; try discriminate.
  match goal with [ S : HeadRed1 Core.tnat _ |- _ ] => inversion S end.
Qed.

(* Symmetric form. *)
Lemma tpi_not_tnat {n} (Γ : Ctx n) (A : Tm n) (B : Tm (S n)) :
  ~ conv Γ (Core.tpi A B) Core.tnat Core.tuniv.
Proof.
  move=> H. apply tnat_not_tpi with (Γ := Γ) (A := A) (B := B).
  apply c_sym. exact H.
Qed.

(* [tuniv] is also head-normal, so it is not convertible to a Π type. *)
Lemma tuniv_not_tpi {n} (Γ : Ctx n) (A : Tm n) (B : Tm (S n)) :
  ~ conv Γ Core.tuniv (Core.tpi A B) Core.tuniv.
Proof.
  move=> H.
  destruct (piConv H) as [B0 [F0 [HR _]]].
  inversion HR; subst; try discriminate.
  match goal with [ S : HeadRed1 Core.tuniv _ |- _ ] => inversion S end.
Qed.

(* [tuniv] and [tnat] are distinct head-normal forms, hence not convertible.
   Proved semantically: conversion soundness ([conv_EvalRel]) at the bottom
   environment would force [le tuniv tnat], which is false. *)
Lemma tuniv_not_tnat {n} (Γ : Ctx n) :
  ~ conv Γ Core.tuniv Core.tnat Core.tuniv.
Proof.
  move=> d.
  have cΓ : ctx Γ by eapply conv_ctx; exact d.
  have IC : InvConv Γ Core.tuniv Core.tnat Core.tuniv bot_env
    by (eapply conv_EvalRel; [ exact d | exact (@fits_bot_env n Γ cΓ) ]).
  move: IC => [_ [_ [fwd _]]].
  have evU : EvalRel Core.tuniv (@bot_env n) tuniv by [].
  have evN : EvalRel Core.tnat (@bot_env n) tuniv := fwd _ evU.
  cbn in evN. done.
Qed.

(** * Progress for closed terms

    A closed, well-typed term is either a value (weak-head-normal form) or it
    takes a head-reduction step.  The content is in the application case: a
    closed value of Π type must be a λ (canonical forms), proved from the
    per-former type inversions ([typing_univ_inv], [typing_nat_inv],
    [typing_tpi_inv], [typing_zero_inv], [typing_succ_inv], at the end of
    [syntax/typing.v]) together with the [tnat]/[tuniv] vs Π non-confusion
    facts. *)

(* Values (weak-head-normal forms) and neutral (variable-headed) terms. *)
Inductive value {n} : Tm n -> Prop :=
| v_univ : value Core.tuniv
| v_nat  : value Core.tnat
| v_tpi  : forall A B, value (Core.tpi A B)
| v_zero : value Core.zero
| v_succ : forall M, value (Core.succ M)
| v_abs  : forall A M, value (Core.abs A M).

Inductive neutral {n} : Tm n -> Prop :=
| ne_var : forall x, neutral (Core.var x)
| ne_app : forall M N, neutral M -> neutral (Core.app M N)
| ne_ncase : forall M M0 M1, neutral M -> neutral (Core.ncase M M0 M1).

(* Canonical forms at Π type (any context): a value of Π type is a λ. *)
Lemma canonical_pi {n} (Γ : Ctx n) (M : Tm n) (A : Tm n) (B : Tm (S n)) :
  value M -> typing Γ M (Core.tpi A B) -> exists A' N, M = Core.abs A' N.
Proof.
  move=> v; destruct v; move=> HT.
  - exfalso; exact (tuniv_not_tpi (typing_univ_inv HT)).
  - exfalso; exact (tuniv_not_tpi (typing_nat_inv HT)).
  - exfalso; exact (tuniv_not_tpi (typing_tpi_inv HT)).
  - exfalso; exact (tnat_not_tpi (typing_zero_inv HT)).
  - exfalso; exact (tnat_not_tpi (typing_succ_inv HT)).
  - eexists; eexists; reflexivity.
Qed.

(* Canonical forms at [tnat]: a value of type [tnat] is [zero] or a successor. *)
Lemma canonical_nat {n} (Γ : Ctx n) (M : Tm n) :
  value M -> typing Γ M Core.tnat -> M = Core.zero \/ exists N, M = Core.succ N.
Proof.
  move=> v; destruct v; move=> HT.
  - exfalso; exact (tuniv_not_tnat (typing_univ_inv HT)).
  - exfalso; exact (tuniv_not_tnat (typing_nat_inv HT)).
  - exfalso; exact (tuniv_not_tnat (typing_tpi_inv HT)).
  - left; reflexivity.
  - right; eexists; reflexivity.
  - exfalso. destruct (typing_abs_inv _ _ _ _ _ HT) as [B2 [_ cPi]].
    exact (tpi_not_tnat cPi).
Qed.

(* Progress, general form: every well-typed term is a value, a neutral
   (variable-headed) term, or head-reduces. *)
Lemma progress_gen {n} (Γ : Ctx n) M A :
  typing Γ M A -> value M \/ neutral M \/ exists N, HeadRed1 M N.
Proof.
  induction 1 as
    [ n Γ x cΓ
    | n Γ M A B tM IHM cAB
    | n Γ A B P tA IHA tB IHB tP IHP
    | n Γ A B F a tA IHA tB IHB tF IHF ta IHa
    | n Γ cΓ
    | n Γ cΓ
    | n Γ P tP IHP
    | n Γ T Mc Mc0 Mc1 tT IHT tMc IHMc tMc0 IHMc0 tMc1 IHMc1
    | n Γ A B tA IHA tB IHB
    | n Γ cΓ ].
  - right; left; constructor.
  - exact IHM.
  - left; constructor.
  - destruct IHF as [ vF | [ neF | [F' stF] ] ].
    + destruct (canonical_pi vF tF) as [A' [N0 ->]].
      right; right; eexists; apply hr_beta.
    + right; left; apply ne_app; exact neF.
    + right; right; eexists; apply hr_app; exact stF.
  - left; constructor.
  - left; constructor.
  - left; constructor.
  - (* t_case: a value scrutinee at [tnat] is zero/succ and the case steps
       (hr_zero/hr_succ); a neutral scrutinee makes the case neutral; a stepping
       scrutinee steps by hr_case. *)
    destruct IHMc as [ vMc | [ neMc | [Mc' stMc] ] ].
    + destruct (canonical_nat vMc tMc) as [ -> | [N0 ->] ].
      * right; right; eexists; apply hr_zero.
      * right; right; eexists; apply hr_succ.
    + right; left; apply ne_ncase; exact neMc.
    + right; right; eexists; apply hr_case; exact stMc.
  - left; constructor.
  - left; constructor.
Qed.

(* A closed term has no neutral (variable-headed) subterm. *)
Lemma neutral_not_closed (M : Tm 0) : neutral M -> False.
Proof. induction 1 as [ x | M N ne IH | M M0 M1 ne IH ]. - destruct x. - exact IH. - exact IH. Qed.

(* Progress for closed terms. *)
Lemma progress (M A : Tm 0) :
  typing ctx_empty M A -> value M \/ exists N, HeadRed1 M N.
Proof.
  move=> H. destruct (progress_gen H) as [ v | [ ne | st ] ].
  - left; exact v.
  - exfalso; exact (neutral_not_closed ne).
  - right; exact st.
Qed.
