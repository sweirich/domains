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
    | n0 Γ0 Ay gy hAy hgy                 (* t_fix *)
    | n0 Γ0 Ai ai bi hAi hai hbi          (* t_tid *)
    | n0 Γ0 Ar ar hAr har                 (* t_rfl *)
    | n0 Γ0 Aj aj bj Cj dj pj hAj haj hbj hCj hdj hpj (* t_jcase *)
    | n0 Γ0 A0 B0 hA hB                   (* t_tpi *)
    | n0 Γ0 cv                            (* t_univ *)
    | n0 Γ0 As Bs hAs hBs                 (* t_tsig *)
    | n0 Γ0 Ap Bp Mp Np hAp hBp hMp hNp   (* t_mkpair *)
    | n0 Γ0 Af Bf Mf hAf hBf hMf          (* t_pfst *)
    | n0 Γ0 Ag Bg Mg hAg hBg hMg          (* t_psnd *)
    | n0 Γ0 cvp                           (* t_prop *)
    | n0 Γ0 Apu hApu                      (* t_prop_u *)
    | n0 Γ0 Apr Bpr hApr hBpr ];          (* t_tpi_prop *)
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
    eapply c_ncase; [ exact TT | | exact convMc | | ].
    + (* the right successor branch's typing: read it off [convMc1] *)
      have EQ1 : (T0[⇑ σ])[rho] = (T0[rho])[⇑ σ].
      { unfold rho. asimpl. setoid_rewrite rinstInst'_Tm_pointwise. reflexivity. }
      rewrite EQ1; exact (proj2 (conv_typing convMc1)).
    + have EQ0 : (T0[⇑ σ])[Core.zero..] = (T0[Core.zero..])[σ] by asimpl.
      rewrite EQ0; exact convMc0.
    + have EQ1 : (T0[⇑ σ])[rho] = (T0[rho])[⇑ σ].
      { unfold rho. asimpl. setoid_rewrite rinstInst'_Tm_pointwise. reflexivity. }
      rewrite EQ1; exact convMc1.
  - (* t_fix: [fix_] congruence.  Both step-function typings come from
       [conv_typing] of the cross conversion, so they are already stated at the
       σ-type. *)
    have CG : conv Δ (gy[σ]) (gy[σ']) (Core.tpi (Ay[σ]) (⟨↑⟩ (Ay[σ]))).
    { move: (subst_conv_cross _ _ _ _ hgy m Δ σ σ' CΔ TS TS' CS).
      asimpl. done. }
    have TAσ : typing Δ Ay[σ] Core.tuniv.
    { move: (substitution_tm _ Ay Core.tuniv _ σ hAy TS CΔ) => hh.
      asimpl in hh. exact hh. }
    have [Tg Tg'] := conv_typing CG.
    cbn. eapply c_fix_cong; [ exact TAσ | exact Tg | exact Tg' | exact CG ].
  - (* t_tid: componentwise congruence *)
    cbn. eapply c_tid;
      [ eapply (substitution_tm _ Ai Core.tuniv _ σ); eauto
      | eapply (substitution_tm _ ai Ai _ σ); eauto
      | eapply (substitution_tm _ bi Ai _ σ); eauto
      | exact (subst_conv_cross _ _ _ _ hAi m Δ σ σ' CΔ TS TS' CS)
      | exact (subst_conv_cross _ _ _ _ hai m Δ σ σ' CΔ TS TS' CS)
      | exact (subst_conv_cross _ _ _ _ hbi m Δ σ σ' CΔ TS TS' CS) ].
  - (* t_rfl *)
    cbn. eapply c_rfl;
      [ eapply (substitution_tm _ Ar Core.tuniv _ σ); eauto
      | eapply (substitution_tm _ ar Ar _ σ); eauto
      | exact (subst_conv_cross _ _ _ _ har m Δ σ σ' CΔ TS TS' CS) ].
  - (* t_jcase: the derived motive/base types commute with the substitution *)
    cbn. eapply (@c_jcase _ Δ (Aj[σ]) (aj[σ]) (bj[σ]) (Cj[σ]) (Cj[σ'])
                          (dj[σ]) (dj[σ']) (pj[σ]) (pj[σ'])).
    1: eapply (substitution_tm _ Aj Core.tuniv _ σ); eauto.
    1: eapply (substitution_tm _ aj Aj _ σ); eauto.
    1: eapply (substitution_tm _ bj Aj _ σ); eauto.
    1: (rewrite -subst_motive_ty;
        eapply (substitution_tm _ Cj (motive_ty Aj) _ σ); eauto).
    1: (rewrite -subst_base_ty;
        eapply (substitution_tm _ dj (base_ty Aj Cj) _ σ); eauto).
    1: eapply (substitution_tm _ pj (Core.tid Aj aj bj) _ σ); eauto.
    1: (rewrite -subst_motive_ty;
        exact (subst_conv_cross _ _ _ _ hCj m Δ σ σ' CΔ TS TS' CS)).
    1: (rewrite -subst_base_ty;
        exact (subst_conv_cross _ _ _ _ hdj m Δ σ σ' CΔ TS TS' CS)).
    1: exact (subst_conv_cross _ _ _ _ hpj m Δ σ σ' CΔ TS TS' CS).
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
  - (* t_tsig: the [t_tpi] case with [c_tsig] *)
    have CAσ : typing Δ As[σ] Core.tuniv
      by (eapply substitution_tm with (A := Core.tuniv); eauto).
    have ECA : ctx (Δ ++ As[σ]) by (eapply c_cons; [ exact CΔ | exact CAσ ]).
    have convA : conv Δ As[σ] As[σ'] Core.tuniv
      := subst_conv_cross _ _ _ _ hAs m Δ σ σ' CΔ TS TS' CS.
    have TSl : typing_subst (Δ ++ As[σ]) (⇑ σ) (Γ0 ++ As)
      by (eapply typing_subst_lift; eauto).
    have TSl' : typing_subst (Δ ++ As[σ]) (⇑ σ') (Γ0 ++ As)
      by (eapply typing_subst_lift_conv; eauto).
    have CSl : ConvSub (Δ ++ As[σ]) (Γ0 ++ As) (⇑ σ) (⇑ σ')
      by (eapply ConvSub_lift; eauto).
    have convB : conv (Δ ++ As[σ]) Bs[⇑ σ] Bs[⇑ σ'] Core.tuniv
      := subst_conv_cross _ _ _ _ hBs _ (Δ ++ As[σ]) (⇑ σ) (⇑ σ') ECA TSl TSl' CSl.
    have TBσ : typing (Δ ++ As[σ]) Bs[⇑ σ] Core.tuniv
      by (eapply substitution_tm with (A := Core.tuniv); eauto).
    have CAσ' : typing Δ As[σ'] Core.tuniv
      by (eapply substitution_tm with (A := Core.tuniv); eauto).
    have ECAσ' : ctx (Δ ++ As[σ']) by (eapply c_cons; [ exact CΔ | exact CAσ' ]).
    have TSlσ' : typing_subst (Δ ++ As[σ']) (⇑ σ') (Γ0 ++ As)
      by (eapply typing_subst_lift; [ exact ECAσ' | exact TS' ]).
    have TBσ' : typing (Δ ++ As[σ']) Bs[⇑ σ'] Core.tuniv
      by (eapply substitution_tm with (A := Core.tuniv); eauto).
    cbn. eapply c_tsig;
      [ exact CAσ | exact CAσ' | exact TBσ | exact TBσ' | exact convA | exact convB ].
  - (* t_mkpair: vary the first component, then the second.  The second's type
       moves from [Bp[Mp[σ]..]] to [Bp[Mp[σ']..]] along the first's
       conversion, which is [conv_subst_arg]. *)
    have CAσ : typing Δ Ap[σ] Core.tuniv
      by (eapply substitution_tm with (A := Core.tuniv); eauto).
    have ECA : ctx (Δ ++ Ap[σ]) by (eapply c_cons; [ exact CΔ | exact CAσ ]).
    have convA : conv Δ Ap[σ] Ap[σ'] Core.tuniv
      := subst_conv_cross _ _ _ _ hAp m Δ σ σ' CΔ TS TS' CS.
    have TSl : typing_subst (Δ ++ Ap[σ]) (⇑ σ) (Γ0 ++ Ap)
      by (eapply typing_subst_lift; eauto).
    have TBσ : typing (Δ ++ Ap[σ]) Bp[⇑ σ] Core.tuniv
      by (eapply substitution_tm with (A := Core.tuniv); eauto).
    have TMσ : typing Δ Mp[σ] Ap[σ]
      by (eapply substitution_tm with (A := Ap); eauto).
    have convM : conv Δ Mp[σ] Mp[σ'] Ap[σ]
      := subst_conv_cross _ _ _ _ hMp m Δ σ σ' CΔ TS TS' CS.
    have TMσ' : typing Δ Mp[σ'] Ap[σ]
      by (eapply t_conv; [ eapply substitution_tm with (A := Ap); eauto
                         | eapply c_sym; exact convA ]).
    have TNσ : typing Δ Np[σ] (Bp[⇑ σ][Mp[σ]..]).
    { rewrite -subst1_subst_comm.
      eapply substitution_tm with (A := Bp[Mp..]); eauto. }
    have convN : conv Δ Np[σ] Np[σ'] (Bp[⇑ σ][Mp[σ]..]).
    { rewrite -subst1_subst_comm.
      exact (subst_conv_cross _ _ _ _ hNp m Δ σ σ' CΔ TS TS' CS). }
    have convBM : conv Δ (Bp[⇑ σ][Mp[σ]..]) (Bp[⇑ σ][Mp[σ']..]) Core.tuniv
      := @conv_subst_arg _ Δ (Ap[σ]) (Bp[⇑ σ]) (Mp[σ]) (Mp[σ'])
           CAσ TBσ TMσ TMσ' convM.
    cbn.
    eapply c_trans with (N := Core.mkpair Mp[σ'] Np[σ]).
    + eapply c_mkpair1; [ exact CAσ | exact TBσ | exact convM | exact TNσ ].
    + eapply c_mkpair2;
        [ exact CAσ | exact TBσ | exact TMσ'
        | eapply c_conv; [ exact convN | exact convBM ] ].
  - (* t_pfst *)
    have convM : conv Δ Mf[σ] Mf[σ'] ((Core.tsig Af Bf)[σ])
      := subst_conv_cross _ _ _ _ hMf m Δ σ σ' CΔ TS TS' CS.
    cbn in convM.
    have CAσ : typing Δ Af[σ] Core.tuniv
      by (eapply substitution_tm with (A := Core.tuniv); eauto).
    have ECA : ctx (Δ ++ Af[σ]) by (eapply c_cons; [ exact CΔ | exact CAσ ]).
    have TSl : typing_subst (Δ ++ Af[σ]) (⇑ σ) (Γ0 ++ Af)
      by (eapply typing_subst_lift; eauto).
    have TBσ : typing (Δ ++ Af[σ]) Bf[⇑ σ] Core.tuniv
      by (eapply substitution_tm with (A := Core.tuniv); eauto).
    cbn. eapply c_pfst; [ exact CAσ | exact TBσ | exact convM ].
  - (* t_psnd: the type is [Bg] at the first projection, so it is given to
       [c_psnd'] in the shape the substitution leaves it in *)
    have convM : conv Δ Mg[σ] Mg[σ'] ((Core.tsig Ag Bg)[σ])
      := subst_conv_cross _ _ _ _ hMg m Δ σ σ' CΔ TS TS' CS.
    cbn in convM.
    have CAσ : typing Δ Ag[σ] Core.tuniv
      by (eapply substitution_tm with (A := Core.tuniv); eauto).
    have ECA : ctx (Δ ++ Ag[σ]) by (eapply c_cons; [ exact CΔ | exact CAσ ]).
    have TSl : typing_subst (Δ ++ Ag[σ]) (⇑ σ) (Γ0 ++ Ag)
      by (eapply typing_subst_lift; eauto).
    have TBσ : typing (Δ ++ Ag[σ]) Bg[⇑ σ] Core.tuniv
      by (eapply substitution_tm with (A := Core.tuniv); eauto).
    eapply (@c_psnd' _ Δ (Ag[σ]) (Bg[⇑ σ]) (Mg[σ]) (Mg[σ'])
                       ((Bg[(Core.pfst Mg)..])[σ]));
      [ exact CAσ | exact TBσ | exact convM
      | first [ asimpl; reflexivity | symmetry; apply subst1_subst_comm ] ].
  - (* t_prop: [tprop] is closed, so both substitutions leave it alone *)
    cbn. eapply c_refl. eapply t_prop. exact CΔ.
  - (* t_prop_u: lift the [tprop] conversion along Prop-to-U subtyping *)
    cbn. eapply c_prop_u.
    exact (subst_conv_cross _ _ _ _ hApu m Δ σ σ' CΔ TS TS' CS).
  - (* t_tpi_prop: the [t_tpi] case with the codomain at the second sort *)
    have CAσ : typing Δ Apr[σ] Core.tuniv
      by (eapply substitution_tm with (A := Core.tuniv); eauto).
    have ECA : ctx (Δ ++ Apr[σ]) by (eapply c_cons; [ exact CΔ | exact CAσ ]).
    have convA : conv Δ Apr[σ] Apr[σ'] Core.tuniv
      := subst_conv_cross _ _ _ _ hApr m Δ σ σ' CΔ TS TS' CS.
    have TSl : typing_subst (Δ ++ Apr[σ]) (⇑ σ) (Γ0 ++ Apr)
      by (eapply typing_subst_lift; eauto).
    have TSl' : typing_subst (Δ ++ Apr[σ]) (⇑ σ') (Γ0 ++ Apr)
      by (eapply typing_subst_lift_conv; eauto).
    have CSl : ConvSub (Δ ++ Apr[σ]) (Γ0 ++ Apr) (⇑ σ) (⇑ σ')
      by (eapply ConvSub_lift; eauto).
    have convB : conv (Δ ++ Apr[σ]) Bpr[⇑ σ] Bpr[⇑ σ'] Core.tprop
      := subst_conv_cross _ _ _ _ hBpr _ (Δ ++ Apr[σ]) (⇑ σ) (⇑ σ') ECA TSl TSl' CSl.
    have TBσ : typing (Δ ++ Apr[σ]) Bpr[⇑ σ] Core.tprop
      by (eapply substitution_tm with (A := Core.tprop); eauto).
    have CAσ' : typing Δ Apr[σ'] Core.tuniv
      by (eapply substitution_tm with (A := Core.tuniv); eauto).
    have ECAσ' : ctx (Δ ++ Apr[σ']) by (eapply c_cons; [ exact CΔ | exact CAσ' ]).
    have TSlσ' : typing_subst (Δ ++ Apr[σ']) (⇑ σ') (Γ0 ++ Apr)
      by (eapply typing_subst_lift; [ exact ECAσ' | exact TS' ]).
    have TBσ' : typing (Δ ++ Apr[σ']) Bpr[⇑ σ'] Core.tprop
      by (eapply substitution_tm with (A := Core.tprop); eauto).
    cbn. eapply c_tpi_prop;
      [ exact CAσ | exact CAσ' | exact TBσ | exact TBσ' | exact convA | exact convB ].
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
  destruct v as [ | | | | v' | | | | | | | ]; try (autorewrite with le; done).
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
      destruct abig as [ | | | | | b f | | | | | | ];
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
      destruct abig as [ | | | | | b f | | | | | | ];
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
      have Hafsel : rk (app f u_sel) < RBf.
      { have L := rk_app f u_sel. have Hf : rk_fun f < rk (tpi b f) by (cbn; lia).
        unfold RBf; lia. }
      have Ecomb := EqVal_trans Hvsel Hafsel Efun Earg.
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
  destruct u as [ | | | | w | b f | g | | | | | ];
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
    destruct u0 as [ | | | | w0 | b0 f0 | g0 | | | | | ];
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
    destruct u0 as [ | | | | w0 | b0 f0 | g0 | | | | | ];
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
        [ exact TTσ | exact TM1σ | exact cvM
        | apply c_refl; exact TM0σ | apply c_refl; exact TM1σ ].
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
    destruct a0 as [ | | | | z0 | b0 f0 | g0 | | | | | ];
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
        [ exact TTσ | exact TM1σ | exact cvM
        | apply c_refl; exact TM0σ | apply c_refl; exact TM1σ ].
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
    destruct a0 as [ | | | | z0 | b0 f0 | g0 | | | | | ];
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
        [ exact TTσ | exact TM1σ | exact cvM
        | apply c_refl; exact TM0σ | apply c_refl; exact TM1σ ].
    - eapply c_conv;
        [ eapply c_ncase_S; [ exact TTσ | exact TP | exact TM0σ | exact TM1σ ]
        | exact cvTs ]. }
  have cvStep' : conv Δ (Core.ncase M M0 M1)[σ'] (M1[⇑ σ'][P'..]) (T[⇑ σ][M[σ]..]).
  { eapply c_conv; [ | exact cvTx ]. cbn. eapply c_trans.
    - eapply c_ncase;
        [ exact TTσ' | exact TM1σ' | exact cvM'
        | apply c_refl; exact TM0σ' | apply c_refl; exact TM1σ' ].
    - eapply c_conv;
        [ eapply c_ncase_S; [ exact TTσ' | exact TP' | exact TM0σ' | exact TM1σ' ]
        | exact cvTs' ]. }
  have EQg : (T[M..])[σ] = T[⇑ σ][M[σ]..] by (asimpl; reflexivity).
  rewrite EQg.
  eapply EqVal_headred_expand;
    [ exact HRstep | exact HRstep' | exact cvStep | exact cvStep' | exact EBrM ].
Qed.

(** The zero branch of [st_case]'s cross ([EqVal]) conjunct.  Both sides
    head-reduce to the zero branch under their own substitution, so the only
    ingredient beyond [st_case_Val_zero] is the σ'-side step conversion,
    retyped to the *shared* motive [T[⇑σ][M[σ]..]] by the cross-substitution
    conversion [cvTx]. *)
Lemma st_case_EqVal_zero (T : Tm (S n)) M M0 M1
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
    EqVal RB Δ (Core.ncase M M0 M1)[σ] (Core.ncase M M0 M1)[σ'] (T[M..])[σ] WT.
Proof.
  have Vρ : valid_env ρ := fits_valid_env Fρ.
  have cΓ : ctx Γ by (eapply typing_ctx; exact TM).
  have evTn : EvalRel Core.tnat ρ tnat by (cbn; apply le_refl).
  (* ---- 1. the scrutinee's cross [EqVal] at the code [zero] ---- *)
  have [_ eqSc] :=
    SM ρ m Δ σ σ' TS TS' CS Fρ VS VS' EVS CΔ zero tnat wt_zero evMz evTn.
  have ESc := eqSc (S (max (rk zero) (rk tnat))) ltac:(lia).
  rewrite EqVal_zero in ESc. move: ESc => [HRz [cvM [HRz' cvM']]].
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
  (* ---- 3. the zero branch's cross [EqVal], at the *zero* motive ---- *)
  have [_ eqBr] :=
    SM0 ρ m Δ σ σ' TS TS' CS Fρ VS VS' EVS CΔ u a WT evM0 evTz.
  (* ---- 4. the motive transport (identical to the [Val] branch) ---- *)
  have Tzero : typing Δ Core.zero Core.tnat by (apply t_zero; exact CΔ).
  have TMσ : typing Δ M[σ] Core.tnat.
  { move: (substitution_tm _ M Core.tnat _ σ TM TS CΔ) => hh. asimpl in hh. exact hh. }
  have TMσ' : typing Δ M[σ'] Core.tnat.
  { move: (substitution_tm _ M Core.tnat _ σ' TM TS' CΔ) => hh. asimpl in hh. exact hh. }
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
    destruct u0 as [ | | | | w0 | b0 f0 | g0 | | | | | ];
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
    destruct u0 as [ | | | | w0 | b0 f0 | g0 | | | | | ];
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
  (* the σ'-side motive conversion, and the cross-substitution one *)
  have TS1z' : typing_subst Δ (Core.zero .: σ') (Γ ++ Core.tnat)
    by (eapply typing_subst_cons; [ asimpl; exact Tzero | exact TS' ]).
  have TS1m' : typing_subst Δ (M[σ'] .: σ') (Γ ++ Core.tnat)
    by (eapply typing_subst_cons; [ asimpl; exact TMσ' | exact TS' ]).
  have CS1' : ConvSub Δ (Γ ++ Core.tnat) (Core.zero .: σ') (M[σ'] .: σ')
    by (eapply ConvSub_cons;
        [ asimpl; apply c_sym; exact cvM' | exact (ConvSub_refl TS') ]).
  have cvTT' : conv Δ T[Core.zero .: σ'] T[M[σ'] .: σ'] Core.tuniv
    := subst_conv_cross TT CΔ TS1z' TS1m' CS1'.
  have cvMx : conv Δ M[σ] M[σ'] Core.tnat.
  { move: (subst_conv_cross TM CΔ TS TS' CS) => hh. asimpl in hh. exact hh. }
  have CSx : ConvSub Δ (Γ ++ Core.tnat) (M[σ] .: σ) (M[σ'] .: σ')
    by (eapply ConvSub_cons; [ asimpl; exact cvMx | exact CS ]).
  have cvTcross : conv Δ T[M[σ] .: σ] T[M[σ'] .: σ'] Core.tuniv
    := subst_conv_cross TT CΔ TS0' TS1m' CSx.
  (* ---- 5. syntactic pieces at σ and σ' ---- *)
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
  (* ---- 6. assemble ---- *)
  move=> RB Hrank.
  have cvTs : conv Δ (T[⇑ σ][Core.zero..]) (T[⇑ σ][M[σ]..]) Core.tuniv.
  { rewrite -(subst_cons_eq T Core.zero σ) -(subst_cons_eq T M[σ] σ). exact cvTT. }
  have cvTs' : conv Δ (T[⇑ σ'][Core.zero..]) (T[⇑ σ'][M[σ']..]) Core.tuniv.
  { rewrite -(subst_cons_eq T Core.zero σ') -(subst_cons_eq T M[σ'] σ'). exact cvTT'. }
  have cvTx : conv Δ (T[⇑ σ'][M[σ']..]) (T[⇑ σ][M[σ]..]) Core.tuniv.
  { rewrite -(subst_cons_eq T M[σ'] σ') -(subst_cons_eq T M[σ] σ).
    apply c_sym. exact cvTcross. }
  have EBrM : EqVal RB Δ M0[σ] M0[σ'] (T[⇑ σ][M[σ]..]) WT.
  { eapply EqVal_EqVal_fwd;
      [ cbn in Hrank; lia | cbn in Hrank; lia | exact cvTs
      | move: (eqBr RB Hrank); rewrite subst1_subst_comm; done
      | rewrite -(subst_cons_eq T Core.zero σ) -(subst_cons_eq T M[σ] σ);
        eapply EqVal_EqValTy;
        exact (eqT (S RB) ltac:(cbn in Hrank |- *; lia)) ]. }
  have HRstep : HeadRed (Core.ncase M M0 M1)[σ] M0[σ].
  { cbn. eapply relations.ms_app;
      [ eapply HeadRed_ncase; exact HRz
      | eapply ms_trans; [ apply hr_zero | apply ms_refl ] ]. }
  have HRstep' : HeadRed (Core.ncase M M0 M1)[σ'] M0[σ'].
  { cbn. eapply relations.ms_app;
      [ eapply HeadRed_ncase; exact HRz'
      | eapply ms_trans; [ apply hr_zero | apply ms_refl ] ]. }
  have cvStep : conv Δ (Core.ncase M M0 M1)[σ] M0[σ] (T[⇑ σ][M[σ]..]).
  { cbn. eapply c_trans.
    - eapply c_ncase;
        [ exact TTσ | exact TM1σ | exact cvM
        | apply c_refl; exact TM0σ | apply c_refl; exact TM1σ ].
    - eapply c_conv;
        [ eapply c_ncase_Z; [ exact TTσ | exact TM0σ | exact TM1σ ] | exact cvTs ]. }
  have cvStep' : conv Δ (Core.ncase M M0 M1)[σ'] M0[σ'] (T[⇑ σ][M[σ]..]).
  { eapply c_conv; [ | exact cvTx ]. cbn. eapply c_trans.
    - eapply c_ncase;
        [ exact TTσ' | exact TM1σ' | exact cvM'
        | apply c_refl; exact TM0σ' | apply c_refl; exact TM1σ' ].
    - eapply c_conv;
        [ eapply c_ncase_Z; [ exact TTσ' | exact TM0σ' | exact TM1σ' ] | exact cvTs' ]. }
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
  destruct w as [ | | | | vp | b0 f0 | g0 | | | | | ]; cbn in Hbr; try done.
  - (* scrutinee is [bot]: so is the result *)
    move: Hbr => [Vu Leu].
    have Eu : u = bot by (apply le_bot_inv; exact Leu).
    move=> RB Hrank. subst u. apply Val_Bot.
  - (* scrutinee is [zero] *)
    eapply st_case_Val_zero; eassumption.
  - (* scrutinee is a successor *)
    eapply st_case_Val_succ; eassumption.
Qed.

(** The cross ([EqVal]) conjunct of [st_case], assembled. *)
Lemma st_case_EqVal (T : Tm (S n)) M M0 M1
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
    EqVal RB Δ (Core.ncase M M0 M1)[σ] (Core.ncase M M0 M1)[σ'] (T[M..])[σ] WT.
Proof.
  cbn in evNcase. move: evNcase => [w [evMw Hbr]].
  destruct w as [ | | | | vp | b0 f0 | g0 | | | | | ]; cbn in Hbr; try done.
  - (* scrutinee is [bot]: so is the result *)
    move: Hbr => [Vu Leu].
    have Eu : u = bot by (apply le_bot_inv; exact Leu).
    move=> RB Hrank. subst u. apply EqVal_Bot.
  - (* scrutinee is [zero] *)
    eapply st_case_EqVal_zero; eassumption.
  - (* scrutinee is a successor *)
    eapply st_case_EqVal_succ; eassumption.
Qed.

(** Dependent case analysis (Agda [adequacyV-ty-Case-dep]): [ncase M M0 M1] is
    semantically typed at the motive instantiated at the scrutinee, [T[M..]].

    This is the rule the whole [Red3] refactor was for.  The dependent motive
    has to be transported from the branch's type ([T[zero..]] or
    [T[(succ P)..]]) to [T[M..]], which needs the *syntactic* conversion
    [conv M[σ] ≡ numeral] at [tnat] — exactly the conversion that [Val]'s
    numeral leaves now carry. *)
Lemma st_case (T : Tm (S n)) M M0 M1 :
  typing (Γ ++ Core.tnat) T Core.tuniv ->
  typing Γ M Core.tnat ->
  typing Γ M0 (T[Core.zero..]) ->
  typing (Γ ++ Core.tnat) M1 T[rho] ->
  semantic_typing (Γ ++ Core.tnat) T Core.tuniv ->
  semantic_typing Γ M Core.tnat ->
  semantic_typing Γ M0 (T[Core.zero..]) ->
  semantic_typing (Γ ++ Core.tnat) M1 T[rho] ->
(* ------------------------- *)
  semantic_typing Γ (Core.ncase M M0 M1) T[M..].
Proof.
  move=> TT TM TM0 TM1 STT SM SM0 SM1.
  move=> ρ m Δ σ σ' TS TS' CS Fρ VS VS' EVS CΔ u a WT evNcase evT.
  split.
  - eapply st_case_Val; eassumption.
  - eapply st_case_EqVal; eassumption.
Qed.

(** ι-rule for the zero scrutinee (Agda [adequacyE-ty-Case-zero]): the case
    redex is semantically convertible to its zero branch.  Same shape as
    [sc_beta]: take the redex's *reflexive* [EqVal] (via [st_case]) and contract
    the second side along the [hr_zero] head reduction, with the [c_ncase_Z]
    step conversion. *)
Lemma sc_ncase_Z (T : Tm (S n)) M0 M1 :
  typing (Γ ++ Core.tnat) T Core.tuniv ->
  typing Γ M0 (T[Core.zero..]) ->
  typing (Γ ++ Core.tnat) M1 T[rho] ->
  semantic_typing (Γ ++ Core.tnat) T Core.tuniv ->
  semantic_typing Γ M0 (T[Core.zero..]) ->
  semantic_typing (Γ ++ Core.tnat) M1 T[rho] ->
(* ------------------------- *)
  semantic_conv2 Γ (Core.ncase Core.zero M0 M1) M0 (T[Core.zero..]).
Proof.
  move=> TT TM0 TM1 STT STM0 STM1.
  have cΓ : ctx Γ by (eapply typing_ctx; exact TM0).
  have Tz : typing Γ Core.zero Core.tnat by (apply t_zero; exact cΓ).
  have STz : semantic_typing Γ Core.zero Core.tnat by (apply st_zero; exact cΓ).
  have STcase : semantic_typing Γ (Core.ncase Core.zero M0 M1) (T[Core.zero..])
    by (eapply st_case;
        [ exact TT | exact Tz | exact TM0 | exact TM1
        | exact STT | exact STz | exact STM0 | exact STM1 ]).
  have Tcase : typing Γ (Core.ncase Core.zero M0 M1) (T[Core.zero..])
    by (eapply t_case; [ exact TT | exact Tz | exact TM0 | exact TM1 ]).
  have Ccase : conv Γ (Core.ncase Core.zero M0 M1) M0 (T[Core.zero..])
    by (eapply c_ncase_Z; [ exact TT | exact TM0 | exact TM1 ]).
  move=> ρ m Δ σ TS FR VS CD u a WT evCase evT RB Hrank.
  have eqCase :=
    proj2 (STcase ρ m Δ σ σ TS TS (ConvSub_refl TS) FR VS VS (ValSub_EqValSub VS)
             CD u a WT evCase evT).
  have CcaseS : conv Δ (Core.ncase Core.zero M0 M1)[σ] (M0[σ]) ((T[Core.zero..])[σ])
    by (eapply substitution_conv; [ exact Ccase | exact TS | exact CD ]).
  have CreflS : conv Δ (Core.ncase Core.zero M0 M1)[σ]
                       (Core.ncase Core.zero M0 M1)[σ] ((T[Core.zero..])[σ])
    by (apply c_refl; eapply substitution_tm; [ exact Tcase | exact TS | exact CD ]).
  eapply EqVal_headred_contract.
  - apply ms_refl.
  - eapply ms_trans; [ apply hr_zero | apply ms_refl ].
  - exact CreflS.
  - apply c_sym; exact CcaseS.
  - exact (eqCase RB Hrank).
Qed.

(** ι-rule for a successor scrutinee (Agda [adequacyE-ty-Case-succ]). *)
Lemma sc_ncase_S (T : Tm (S n)) M0 M1 N :
  typing (Γ ++ Core.tnat) T Core.tuniv ->
  typing Γ N Core.tnat ->
  typing Γ M0 (T[Core.zero..]) ->
  typing (Γ ++ Core.tnat) M1 T[rho] ->
  semantic_typing (Γ ++ Core.tnat) T Core.tuniv ->
  semantic_typing Γ N Core.tnat ->
  semantic_typing Γ M0 (T[Core.zero..]) ->
  semantic_typing (Γ ++ Core.tnat) M1 T[rho] ->
(* ------------------------- *)
  semantic_conv2 Γ (Core.ncase (Core.succ N) M0 M1) M1[N..] (T[(Core.succ N)..]).
Proof.
  move=> TT TN TM0 TM1 STT STN STM0 STM1.
  have Ts : typing Γ (Core.succ N) Core.tnat by (apply t_succ; exact TN).
  have STs : semantic_typing Γ (Core.succ N) Core.tnat
    by (eapply st_succ; [ exact TN | exact STN ]).
  have STcase : semantic_typing Γ (Core.ncase (Core.succ N) M0 M1)
                  (T[(Core.succ N)..])
    by (eapply st_case;
        [ exact TT | exact Ts | exact TM0 | exact TM1
        | exact STT | exact STs | exact STM0 | exact STM1 ]).
  have Tcase : typing Γ (Core.ncase (Core.succ N) M0 M1) (T[(Core.succ N)..])
    by (eapply t_case; [ exact TT | exact Ts | exact TM0 | exact TM1 ]).
  have Ccase : conv Γ (Core.ncase (Core.succ N) M0 M1) M1[N..] (T[(Core.succ N)..])
    by (eapply c_ncase_S; [ exact TT | exact TN | exact TM0 | exact TM1 ]).
  move=> ρ m Δ σ TS FR VS CD u a WT evCase evT RB Hrank.
  have eqCase :=
    proj2 (STcase ρ m Δ σ σ TS TS (ConvSub_refl TS) FR VS VS (ValSub_EqValSub VS)
             CD u a WT evCase evT).
  have CcaseS : conv Δ (Core.ncase (Core.succ N) M0 M1)[σ] ((M1[N..])[σ])
                       ((T[(Core.succ N)..])[σ])
    by (eapply substitution_conv; [ exact Ccase | exact TS | exact CD ]).
  have CreflS : conv Δ (Core.ncase (Core.succ N) M0 M1)[σ]
                       (Core.ncase (Core.succ N) M0 M1)[σ]
                       ((T[(Core.succ N)..])[σ])
    by (apply c_refl; eapply substitution_tm; [ exact Tcase | exact TS | exact CD ]).
  eapply EqVal_headred_contract.
  - apply ms_refl.
  - rewrite subst1_subst_comm.
    eapply ms_trans; [ apply hr_succ | apply ms_refl ].
  - exact CreflS.
  - apply c_sym; exact CcaseS.
  - exact (eqCase RB Hrank).
Qed.

(** The zero case of the [ncase] congruence.  Unlike [st_case_EqVal_zero]
    there is only one substitution, so the σ'-bookkeeping disappears; what
    replaces it is the *right* step conversion, obtained from the whole
    congruence conversion [Ccong] rather than rebuilt from scratch:
    [ncase M' M0' M1' ≡ ncase M M0 M1 ≡ M0 ≡ M0']. *)
Lemma sc_ncase_zero (T : Tm (S n)) M M0 M1 M' M0' M1'
  (TT : typing (Γ ++ Core.tnat) T Core.tuniv)
  (TM1' : typing (Γ ++ Core.tnat) M1' T[rho])
  (CMM' : conv Γ M M' Core.tnat)
  (CM0 : conv Γ M0 M0' (T[Core.zero..]))
  (CM1 : conv (Γ ++ Core.tnat) M1 M1' T[rho])
  (STT : semantic_typing (Γ ++ Core.tnat) T Core.tuniv)
  (SCM : semantic_conv2 Γ M M' Core.tnat)
  (SCM0 : semantic_conv2 Γ M0 M0' (T[Core.zero..]))
  ρ m (Δ : Ctx m) (σ : Sub n m)
  (TS : typing_subst Δ σ Γ) (Fρ : fits Γ ρ) (VS : ValSub Δ Γ σ ρ) (CΔ : ctx Δ)
  u a (WT : wt u a)
  (evMz : EvalRel M ρ zero) (evM0 : EvalRel M0 ρ u)
  (evT : EvalRel T[M..] ρ a) :
  forall RB, max (rk u) (rk a) < RB ->
    EqVal RB Δ (Core.ncase M M0 M1)[σ] (Core.ncase M' M0' M1')[σ] (T[M..])[σ] WT.
Proof.
  have Vρ : valid_env ρ := fits_valid_env Fρ.
  have cΓ : ctx Γ := fits_ctx Fρ.
  have evTn : EvalRel Core.tnat ρ tnat by (cbn; apply le_refl).
  have Ccong : conv Γ (Core.ncase M M0 M1) (Core.ncase M' M0' M1') (T[M..])
    by (eapply c_ncase; [ exact TT | exact TM1' | exact CMM' | exact CM0 | exact CM1 ]).
  have [TM1 _] := conv_typing CM1.
  (* ---- 1. the scrutinee's conversion [EqVal] at the code [zero] ---- *)
  have ESc := SCM ρ m Δ σ TS Fρ VS CΔ zero tnat wt_zero evMz evTn
                (S (max (rk zero) (rk tnat))) ltac:(lia).
  rewrite EqVal_zero in ESc. move: ESc => [HRz [cvM [HRz' cvM']]].
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
  (* ---- 3. the branch conversion [EqVal] ---- *)
  have eqBr := SCM0 ρ m Δ σ TS Fρ VS CΔ u a WT evM0 evTz.
  (* ---- 4. the motive transport, from the motive's own semantic typing ---- *)
  have Tzero : typing Δ Core.zero Core.tnat by (apply t_zero; exact CΔ).
  have [TMσ _] := conv_typing cvM.
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
    destruct u0 as [ | | | | w0 | b0 f0 | g0 | | | | | ];
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
    eapply EqVal_Val1.
    exact (SCM ρ m Δ σ TS Fρ VS CΔ u0 a0 h0 evMu0 Ea0 RB0 Hr0). }
  have HEhead : forall u0, valid u0 -> le u0 zero -> forall a0 (h0 : wt u0 a0),
      EvalRel Core.tnat ρ a0 -> forall RB0, max (rk u0) (rk a0) < RB0 ->
      EqVal RB0 Δ Core.zero M[σ] Core.tnat[σ] h0.
  { move=> u0 Vu0 Le0 a0 h0 Ea0 RB0 Hr0.
    destruct u0 as [ | | | | w0 | b0 f0 | g0 | | | | | ];
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
  (* ---- 5. syntactic pieces ---- *)
  have TTσ : typing (Δ ++ Core.tnat) T[⇑ σ] Core.tuniv.
  { exact (@subst_cod_typing n Γ Core.tnat T m Δ σ
             ltac:(apply t_nat; exact cΓ) TT TS CΔ). }
  have TM0σ : typing Δ M0[σ] (T[⇑ σ][Core.zero..]).
  { move: (substitution_tm _ M0 (T[Core.zero..]) _ σ
             ltac:(exact (proj1 (conv_typing CM0))) TS CΔ) => hh.
    asimpl in hh. asimpl. exact hh. }
  have CΔn : ctx (Δ ++ Core.tnat)
    by (eapply c_cons; [ exact CΔ | apply t_nat; exact CΔ ]).
  have TSl : typing_subst (Δ ++ Core.tnat) (⇑ σ) (Γ ++ Core.tnat).
  { exact (@typing_subst_lift m Δ n σ Γ Core.tnat CΔn TS). }
  have TM1σ : typing (Δ ++ Core.tnat) M1[⇑ σ] (T[⇑ σ])[rho].
  { rewrite rho_subst_comm.
    exact (substitution_tm _ M1 (T[rho]) _ (⇑ σ) TM1 TSl CΔn). }
  (* ---- 6. assemble ---- *)
  move=> RB Hrank.
  have cvTs : conv Δ (T[⇑ σ][Core.zero..]) (T[⇑ σ][M[σ]..]) Core.tuniv.
  { rewrite -(subst_cons_eq T Core.zero σ) -(subst_cons_eq T M[σ] σ). exact cvTT. }
  have EBrM : EqVal RB Δ M0[σ] M0'[σ] (T[⇑ σ][M[σ]..]) WT.
  { eapply EqVal_EqVal_fwd;
      [ cbn in Hrank; lia | cbn in Hrank; lia | exact cvTs
      | move: (eqBr RB Hrank);
        rewrite (@subst1_subst_comm _ _ T Core.zero σ); done
      | rewrite -(subst_cons_eq T Core.zero σ) -(subst_cons_eq T M[σ] σ);
        eapply EqVal_EqValTy;
        exact (eqT (S RB) ltac:(cbn in Hrank |- *; lia)) ]. }
  have HRstep : HeadRed (Core.ncase M M0 M1)[σ] M0[σ].
  { cbn. eapply relations.ms_app;
      [ eapply HeadRed_ncase; exact HRz
      | eapply ms_trans; [ apply hr_zero | apply ms_refl ] ]. }
  have HRstep' : HeadRed (Core.ncase M' M0' M1')[σ] M0'[σ].
  { cbn. eapply relations.ms_app;
      [ eapply HeadRed_ncase; exact HRz'
      | eapply ms_trans; [ apply hr_zero | apply ms_refl ] ]. }
  have cvStep : conv Δ (Core.ncase M M0 M1)[σ] M0[σ] (T[⇑ σ][M[σ]..]).
  { cbn. eapply c_trans.
    - eapply c_ncase;
        [ exact TTσ | exact TM1σ | exact cvM
        | apply c_refl; exact TM0σ | apply c_refl; exact TM1σ ].
    - eapply c_conv;
        [ eapply c_ncase_Z; [ exact TTσ | exact TM0σ | exact TM1σ ] | exact cvTs ]. }
  have CcongS : conv Δ (Core.ncase M M0 M1)[σ] (Core.ncase M' M0' M1')[σ]
                       (T[⇑ σ][M[σ]..]).
  { move: (substitution_conv _ (Core.ncase M M0 M1) (Core.ncase M' M0' M1')
             (T[M..]) _ σ Ccong TS CΔ) => hh.
    rewrite (@subst1_subst_comm _ _ T M σ) in hh. exact hh. }
  have cvBranch : conv Δ M0[σ] M0'[σ] (T[⇑ σ][M[σ]..]).
  { eapply c_conv; [ | exact cvTs ].
    move: (substitution_conv _ M0 M0' (T[Core.zero..]) _ σ CM0 TS CΔ) => hh.
    rewrite (@subst1_subst_comm _ _ T Core.zero σ) in hh. exact hh. }
  have cvStep' : conv Δ (Core.ncase M' M0' M1')[σ] M0'[σ] (T[⇑ σ][M[σ]..]).
  { eapply c_trans; [ apply c_sym; exact CcongS | ].
    eapply c_trans; [ exact cvStep | exact cvBranch ]. }
  have EQg : (T[M..])[σ] = T[⇑ σ][M[σ]..] by (asimpl; reflexivity).
  rewrite EQg.
  eapply EqVal_headred_expand;
    [ exact HRstep | exact HRstep' | exact cvStep | exact cvStep' | exact EBrM ].
Qed.

(** The successor case of the [ncase] congruence.  The two sides reduce to the
    successor branch at *different* predecessor terms, [P] (from [M[σ]]) and
    [P'] (from [M'[σ]]), so the branch relation is composed in two steps
    through [M1'[P .: σ]]:

      [M1[P .: σ] ≈ M1'[P .: σ]]   from the branch conversion at [P .: σ],
      [M1'[P .: σ] ≈ M1'[P' .: σ]] from the *semantic typing* of [M1'] at the
                                   two substitutions, related by [conv P P']
                                   (the predecessor conversion stored in
                                   [EqVal]'s successor leaf).

    The second step is why [c_ncase] carries [typing (Γ++tnat) M1' T[rho]]: a
    conversion premise alone yields only the single-substitution
    [semantic_conv2], which cannot relate one term under two substitutions. *)
Lemma sc_ncase_succ (T : Tm (S n)) M M0 M1 M' M0' M1'
  (TT : typing (Γ ++ Core.tnat) T Core.tuniv)
  (TM1' : typing (Γ ++ Core.tnat) M1' T[rho])
  (CMM' : conv Γ M M' Core.tnat)
  (CM0 : conv Γ M0 M0' (T[Core.zero..]))
  (CM1 : conv (Γ ++ Core.tnat) M1 M1' T[rho])
  (STT : semantic_typing (Γ ++ Core.tnat) T Core.tuniv)
  (STM1' : semantic_typing (Γ ++ Core.tnat) M1' T[rho])
  (SCM : semantic_conv2 Γ M M' Core.tnat)
  (SCM1 : semantic_conv2 (Γ ++ Core.tnat) M1 M1' T[rho])
  ρ m (Δ : Ctx m) (σ : Sub n m)
  (TS : typing_subst Δ σ Γ) (Fρ : fits Γ ρ) (VS : ValSub Δ Γ σ ρ) (CΔ : ctx Δ)
  u a (WT : wt u a)
  vp (evMs : EvalRel M ρ (succ vp)) (evM1 : EvalRel M1 (vp .: ρ) u)
  (evT : EvalRel T[M..] ρ a) :
  forall RB, max (rk u) (rk a) < RB ->
    EqVal RB Δ (Core.ncase M M0 M1)[σ] (Core.ncase M' M0' M1')[σ] (T[M..])[σ] WT.
Proof.
  have Vρ : valid_env ρ := fits_valid_env Fρ.
  have cΓ : ctx Γ := fits_ctx Fρ.
  have evTn : EvalRel Core.tnat ρ tnat by (cbn; apply le_refl).
  have Ccong : conv Γ (Core.ncase M M0 M1) (Core.ncase M' M0' M1') (T[M..])
    by (eapply c_ncase; [ exact TT | exact TM1' | exact CMM' | exact CM0 | exact CM1 ]).
  have [TM1 _] := conv_typing CM1.
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
  have IT : InvTyped Γ M Core.tnat ρ
    by (apply typing_EvalRel; [ exact (proj1 (conv_typing CMM')) | exact Fρ ]).
  have [vv [aa [hwt [Lsv [_ Etn]]]]] := IT (succ vpp) evMc.
  cbn in Etn.
  have wtvv : wt vv tnat := wt_le hwt Etn (wt_ty_tuniv hwt) wt_tnat.
  have wtsvpp : wt (succ vpp) tnat := wt_tnat_down wtvv Lsv.
  set wtvpp := wt_succ_inv wtsvpp.
  (* ---- 3. the scrutinee's conversion [EqVal] at the code [succ vpp] ---- *)
  have ESc := SCM ρ m Δ σ TS Fρ VS CΔ (succ vpp) tnat wtsvpp evMc evTn
                (S (S (max (rk (succ vpp)) (rk tnat)))) ltac:(lia).
  rewrite EqVal_succ in ESc.
  move: ESc => [P [HRs [cvM [P' [HRs' [cvM' [cvPP EP]]]]]]].
  have [TMσ TsP] := conv_typing cvM.
  have [TMσ' TsP'] := conv_typing cvM'.
  have TP : typing Δ P Core.tnat := typing_succ_arg_inv TsP.
  have TP' : typing Δ P' Core.tnat := typing_succ_arg_inv TsP'.
  (* ---- 4. the [Sub] heads at the value [succ vpp] ---- *)
  have HEMhead : forall u0, valid u0 -> le u0 (succ vpp) -> forall a0 (h0 : wt u0 a0),
      EvalRel Core.tnat ρ a0 -> forall RB0, max (rk u0) (rk a0) < RB0 ->
      EqVal RB0 Δ M[σ] M'[σ] Core.tnat[σ] h0.
  { move=> u0 Vu0 Le0 a0 h0 Ea0 RB0 Hr0.
    have evMu0 : EvalRel M ρ u0
      by (eapply EvalRel_down; [ exact Vρ | exact Vu0 | exact evMc | exact Le0 ]).
    exact (SCM ρ m Δ σ TS Fρ VS CΔ u0 a0 h0 evMu0 Ea0 RB0 Hr0). }
  have HMhead : forall u0, valid u0 -> le u0 (succ vpp) -> forall a0 (h0 : wt u0 a0),
      EvalRel Core.tnat ρ a0 -> forall RB0, max (rk u0) (rk a0) < RB0 ->
      Val RB0 Δ M[σ] Core.tnat[σ] h0.
  { move=> u0 Vu0 Le0 a0 h0 Ea0 RB0 Hr0.
    eapply EqVal_Val1; exact (HEMhead u0 Vu0 Le0 a0 h0 Ea0 RB0 Hr0). }
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
  (* ---- 5. the [Sub] heads for the two predecessor terms ---- *)
  have HPPhead : forall u0, valid u0 -> le u0 vpp -> forall a0 (h0 : wt u0 a0),
      EvalRel Core.tnat ρ a0 -> forall RB0, max (rk u0) (rk a0) < RB0 ->
      EqVal RB0 Δ P P' Core.tnat[σ] h0.
  { move=> u0 Vu0 Le0 a0 h0 Ea0 RB0 Hr0. cbn in Ea0.
    destruct a0 as [ | | | | z0 | b0 f0 | g0 | | | | | ];
      try solve [ autorewrite with le in Ea0; done ].
    - apply EqVal_Bot_ty.
    - have Vsu0 : valid (succ u0) by (cbn; exact Vu0).
      have Lesu0 : le (succ u0) (succ vpp) by (rewrite le_succ; exact Le0).
      have evMsu0 : EvalRel M ρ (succ u0)
        by (eapply EvalRel_down; [ exact Vρ | exact Vsu0 | exact evMc | exact Lesu0 ]).
      have EM0 := SCM ρ m Δ σ TS Fρ VS CΔ (succ u0) tnat (wt_succ h0) evMsu0 evTn
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
      Val RB0 Δ P' Core.tnat[σ] h0.
  { move=> u0 Vu0 Le0 a0 h0 Ea0 RB0 Hr0.
    eapply EqVal_Val2; exact (HPPhead u0 Vu0 Le0 a0 h0 Ea0 RB0 Hr0). }
  (* ---- 6. the branch relation, composed through [M1'[P .: σ]] ---- *)
  have evM1v : EvalRel M1 (vpp .: ρ) u.
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
  have evM1'v : EvalRel M1' (vpp .: ρ) u.
  { move: (conv_EvalRel CM1 Fits1) => [_ [_ [fwd _]]]. exact (fwd u evM1v). }
  have TS1 : typing_subst Δ (P .: σ) (Γ ++ Core.tnat)
    by (eapply typing_subst_cons; [ asimpl; exact TP | exact TS ]).
  have TS1' : typing_subst Δ (P' .: σ) (Γ ++ Core.tnat)
    by (eapply typing_subst_cons; [ asimpl; exact TP' | exact TS ]).
  have CS1 : ConvSub Δ (Γ ++ Core.tnat) (P .: σ) (P' .: σ)
    by (eapply ConvSub_cons; [ asimpl; exact cvPP | exact (ConvSub_refl TS) ]).
  have VS1 : ValSub Δ (Γ ++ Core.tnat) (P .: σ) (vpp .: ρ)
    by (eapply ValSub_cons; [ exact HPvhead | exact VS ]).
  have VS1' : ValSub Δ (Γ ++ Core.tnat) (P' .: σ) (vpp .: ρ)
    by (eapply ValSub_cons; [ exact HPv'head | exact VS ]).
  have EVS1 : EqValSub Δ (Γ ++ Core.tnat) (P .: σ) (P' .: σ) (vpp .: ρ)
    by (eapply EqValSub_cons; [ exact HPPhead | exact (ValSub_EqValSub VS) ]).
  have eqBr1 := SCM1 (vpp .: ρ) m Δ (P .: σ) TS1 Fits1 VS1 CΔ u a WT evM1v evTrho.
  have [_ eqBr2] :=
    STM1' (vpp .: ρ) m Δ (P .: σ) (P' .: σ) TS1 TS1' CS1 Fits1
          VS1 VS1' EVS1 CΔ u a WT evM1'v evTrho.
  (* ---- 7. the motive transport ---- *)
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
  (* ---- 8. syntactic pieces ---- *)
  have TTσ : typing (Δ ++ Core.tnat) T[⇑ σ] Core.tuniv.
  { exact (@subst_cod_typing n Γ Core.tnat T m Δ σ
             ltac:(apply t_nat; exact cΓ) TT TS CΔ). }
  have TM0σ : typing Δ M0[σ] (T[⇑ σ][Core.zero..]).
  { move: (substitution_tm _ M0 (T[Core.zero..]) _ σ
             ltac:(exact (proj1 (conv_typing CM0))) TS CΔ) => hh.
    asimpl in hh. asimpl. exact hh. }
  have CΔn : ctx (Δ ++ Core.tnat)
    by (eapply c_cons; [ exact CΔ | apply t_nat; exact CΔ ]).
  have TSl : typing_subst (Δ ++ Core.tnat) (⇑ σ) (Γ ++ Core.tnat).
  { exact (@typing_subst_lift m Δ n σ Γ Core.tnat CΔn TS). }
  have TM1σ : typing (Δ ++ Core.tnat) M1[⇑ σ] (T[⇑ σ])[rho].
  { rewrite rho_subst_comm.
    exact (substitution_tm _ M1 (T[rho]) _ (⇑ σ) TM1 TSl CΔn). }
  (* ---- 9. assemble ---- *)
  move=> RB Hrank.
  have cvTs : conv Δ (T[⇑ σ][(Core.succ P)..]) (T[⇑ σ][M[σ]..]) Core.tuniv.
  { rewrite -(subst_cons_eq T (Core.succ P) σ) -(subst_cons_eq T M[σ] σ).
    exact cvTT. }
  have Hru : rk u < RB by (cbn in Hrank; lia).
  (* compose the two branch relations through [M1'[P .: σ]] *)
  have EBr0 : EqVal RB Δ M1[P .: σ] M1'[P' .: σ] ((T[rho])[P .: σ]) WT.
  { eapply EqVal_trans;
      [ exact Hru | cbn in Hrank; lia
      | exact (eqBr1 RB Hrank) | exact (eqBr2 RB Hrank) ]. }
  have EBr : EqVal RB Δ (M1[⇑ σ][P..]) (M1'[⇑ σ][P'..]) (T[⇑ σ][M[σ]..]) WT.
  { eapply EqVal_EqVal_fwd;
      [ cbn in Hrank; lia | cbn in Hrank; lia | exact cvTs
      | move: EBr0;
        rewrite rho_subst_cons (subst_cons_eq M1 P σ) (subst_cons_eq M1' P' σ)
                (subst_cons_eq T (Core.succ P) σ); done
      | rewrite -(subst_cons_eq T (Core.succ P) σ) -(subst_cons_eq T M[σ] σ);
        eapply EqVal_EqValTy;
        exact (eqT (S RB) ltac:(cbn in Hrank |- *; lia)) ]. }
  have HRstep : HeadRed (Core.ncase M M0 M1)[σ] (M1[⇑ σ][P..]).
  { cbn. eapply relations.ms_app;
      [ eapply HeadRed_ncase; exact HRs
      | eapply ms_trans; [ apply hr_succ | apply ms_refl ] ]. }
  have HRstep' : HeadRed (Core.ncase M' M0' M1')[σ] (M1'[⇑ σ][P'..]).
  { cbn. eapply relations.ms_app;
      [ eapply HeadRed_ncase; exact HRs'
      | eapply ms_trans; [ apply hr_succ | apply ms_refl ] ]. }
  have cvStep : conv Δ (Core.ncase M M0 M1)[σ] (M1[⇑ σ][P..]) (T[⇑ σ][M[σ]..]).
  { cbn. eapply c_trans.
    - eapply c_ncase;
        [ exact TTσ | exact TM1σ | exact cvM
        | apply c_refl; exact TM0σ | apply c_refl; exact TM1σ ].
    - eapply c_conv;
        [ eapply c_ncase_S; [ exact TTσ | exact TP | exact TM0σ | exact TM1σ ]
        | exact cvTs ]. }
  have CcongS : conv Δ (Core.ncase M M0 M1)[σ] (Core.ncase M' M0' M1')[σ]
                       (T[⇑ σ][M[σ]..]).
  { move: (substitution_conv _ (Core.ncase M M0 M1) (Core.ncase M' M0' M1')
             (T[M..]) _ σ Ccong TS CΔ) => hh.
    rewrite (@subst1_subst_comm _ _ T M σ) in hh. exact hh. }
  have cvBranch : conv Δ (M1[⇑ σ][P..]) (M1'[⇑ σ][P'..]) (T[⇑ σ][M[σ]..]).
  { eapply c_conv; [ | exact cvTs ].
    have cb1 : conv Δ M1[P .: σ] M1'[P .: σ] ((T[rho])[P .: σ])
      := substitution_conv _ M1 M1' (T[rho]) _ (P .: σ) CM1 TS1 CΔ.
    have cb2 : conv Δ M1'[P .: σ] M1'[P' .: σ] ((T[rho])[P .: σ])
      := subst_conv_cross TM1' CΔ TS1 TS1' CS1.
    have cbt : conv Δ M1[P .: σ] M1'[P' .: σ] ((T[rho])[P .: σ])
      by (eapply c_trans; [ exact cb1 | exact cb2 ]).
    move: cbt.
    rewrite rho_subst_cons (subst_cons_eq M1 P σ) (subst_cons_eq M1' P' σ)
            (subst_cons_eq T (Core.succ P) σ); done. }
  have cvStep' : conv Δ (Core.ncase M' M0' M1')[σ] (M1'[⇑ σ][P'..])
                        (T[⇑ σ][M[σ]..]).
  { eapply c_trans; [ apply c_sym; exact CcongS | ].
    eapply c_trans; [ exact cvStep | exact cvBranch ]. }
  have EQg : (T[M..])[σ] = T[⇑ σ][M[σ]..] by (asimpl; reflexivity).
  rewrite EQg.
  eapply EqVal_headred_expand;
    [ exact HRstep | exact HRstep' | exact cvStep | exact cvStep' | exact EBr ].
Qed.

(** Congruence for dependent case analysis, assembled. *)
Lemma sc_ncase (T : Tm (S n)) M M0 M1 M' M0' M1' :
  typing (Γ ++ Core.tnat) T Core.tuniv ->
  typing (Γ ++ Core.tnat) M1' T[rho] ->
  conv Γ M M' Core.tnat ->
  conv Γ M0 M0' (T[Core.zero..]) ->
  conv (Γ ++ Core.tnat) M1 M1' T[rho] ->
  semantic_typing (Γ ++ Core.tnat) T Core.tuniv ->
  semantic_typing (Γ ++ Core.tnat) M1' T[rho] ->
  semantic_conv2 Γ M M' Core.tnat ->
  semantic_conv2 Γ M0 M0' (T[Core.zero..]) ->
  semantic_conv2 (Γ ++ Core.tnat) M1 M1' T[rho] ->
(* ------------------------- *)
  semantic_conv2 Γ (Core.ncase M M0 M1) (Core.ncase M' M0' M1') (T[M..]).
Proof.
  move=> TT TM1' CMM' CM0 CM1 STT STM1' SCM SCM0 SCM1.
  move=> ρ m Δ σ TS Fρ VS CΔ u a WT evNcase evT.
  cbn in evNcase. move: evNcase => [w [evMw Hbr]].
  destruct w as [ | | | | vp | b0 f0 | g0 | | | | | ]; cbn in Hbr; try done.
  - (* scrutinee is [bot]: so is the result *)
    move: Hbr => [Vu Leu].
    have Eu : u = bot by (apply le_bot_inv; exact Leu).
    move=> RB Hrank. subst u. apply EqVal_Bot.
  - (* scrutinee is [zero] *)
    eapply sc_ncase_zero; eassumption.
  - (* scrutinee is a successor *)
    eapply sc_ncase_succ; eassumption.
Qed.

(** The application core for [Y] (Agda [adequacyV-Y-App-core] /
    [adequacyE-Y-App-core] in [NAT/Adequacy/YCore.agda] and
    [NAT/Adequacy/YCross.agda]): validity of the *contractum*
    [app g (fix_ g) : A] at a value [u] recorded by an edge [v0 ↦ u] of the
    step function [g], whose key [v0] is a stage-[j] Kleene approximant.

    This mirrors [st_app] at [M := g], [N := fix_ g], [B := A⟨↑⟩], with two
    changes:

      * the argument's validity (Agda's "Site 1", at the canonical selection
        key [u_sel] below [v0]) comes from the stage-[j] recursor [IHy] rather
        than from a [semantic_typing] hypothesis on the argument — that is the
        whole reason [Y] needs its own core.  The key step is that [u_sel] is
        again a stage-[j] approximant: [Approx_EvalRel_down] is
        index-preserving; and
      * the codomain-type block *collapses*.  Since [B = A⟨↑⟩] is
        non-dependent, [A⟨↑⟩[⇑σ][(fix_ g)[σ]..] = A[σ]], so [ValTy] at the
        join comes straight from [STA] and [codomain_type_ValTy] — with its
        [VNarg] argument-validity requirement — is not needed at all. *)
Lemma st_fix_app_core (A g : Tm n) :
  typing Γ A Core.tuniv ->
  typing Γ g (Core.tpi A (⟨↑⟩ A)) ->
  semantic_typing Γ A Core.tuniv ->
  semantic_typing Γ g (Core.tpi A (⟨↑⟩ A)) ->
  forall (j : nat) ρ m (Δ : Ctx m) (σ σ': Sub n m)
    (TS : typing_subst Δ σ Γ) (TS' : typing_subst Δ σ' Γ)
    (CS : ConvSub Δ Γ σ σ') (Fρ : fits Γ ρ)
    (VS : ValSub Δ Γ σ ρ) (VS' : ValSub Δ Γ σ' ρ)
    (EVS : EqValSub Δ Γ σ σ' ρ) (CΔ : ctx Δ),
  (* the stage-[j] argument recursor *)
  (forall u' a' (WT' : wt u' a'),
      Approx (fun p w => EvalRel g ρ (p ↦ w)) j u' -> EvalRel A ρ a' ->
      (forall RB, max (rk u') (rk a') < RB -> Val RB Δ (Core.fix_ (g[σ])) A[σ] WT') /\
      (forall RB, max (rk u') (rk a') < RB ->
          EqVal RB Δ (Core.fix_ (g[σ])) (Core.fix_ (g[σ'])) A[σ] WT')) ->
  forall u a (WT : wt u a) v0,
    is_bot u = false ->
    Approx (fun p w => EvalRel g ρ (p ↦ w)) j v0 ->
    EvalRel g ρ (v0 ↦ u) ->
    EvalRel A ρ a ->
    (forall RB, max (rk u) (rk a) < RB ->
        Val RB Δ (Core.app (g[σ]) (Core.fix_ (g[σ]))) A[σ] WT) /\
    (forall RB, max (rk u) (rk a) < RB ->
        EqVal RB Δ (Core.app (g[σ]) (Core.fix_ (g[σ])))
                   (Core.app (g[σ']) (Core.fix_ (g[σ']))) A[σ] WT).
Proof.
  move=> TA Tg STA STg.
  move=> j ρ m Δ σ σ' TS TS' CS Fρ VS VS' EVS CΔ IHy u a WT v0 Hu HAj evEdge evA_a.
  have Vρ : valid_env ρ := fits_valid_env Fρ.
  have TY : typing Γ (Core.fix_ g) A by (eapply t_fix; [ exact TA | exact Tg ]).
  have evN : EvalRel (Core.fix_ g) ρ v0 by (exists j; exact HAj).
  (* enlarge the edge to a well-typed function value (as in [st_app]) *)
  have IT : InvTyped Γ g (Core.tpi A (⟨↑⟩ A)) ρ.
  { apply typing_EvalRel. exact Tg. exact Fρ. }
  have [vbig [abig [WTbig [LEbig [evMbig evTpi]]]]] := IT (v0 ↦ u) evEdge.
  unfold singleton in LEbig. rewrite Hu in LEbig.
  have [gt [Evbig LEfun]] := le_abs_inv LEbig. subst vbig.
  destruct abig as [ | | | | | b f | | | | | | ];
    try solve [ exfalso; clear -WTbig; inversion WTbig ].
  have evTpiC := evTpi. cbn in evTpiC. move: evTpiC => [Vb [Vf [evA_b _]]].
  have Vg : valid_fun gt := proj1 (andb_prop _ _ (wt_valid_tm WTbig)).
  have Vv0 : valid v0 := EvalRel_valid evN.
  have [u_sel [v_sel [Sel [Le_usel Eq_vsel]]]] := selectionBelow Vg Vv0.
  have [WTu_sel WTv_sel] : wt u_sel b /\ wt v_sel (app f u_sel).
  { eapply wt_Selection_cod;
      [ exact (wt_abs_ty WTbig) | exact (wt_abs_inv1 WTbig)
      | move=> ui vi Hin; exact (wt_abs_inv2 WTbig Hin erefl)
      | exact Vg | exact Sel ]. }
  have Vusel : valid u_sel := wt_valid_tm WTu_sel.
  have evN_usel : EvalRel (Core.fix_ g) ρ u_sel
    by (eapply EvalRel_down; [ exact Vρ | exact Vusel | exact evN | exact Le_usel ]).
  (* Site 1: the argument's validity, from the stage-[j] recursor run on the
     index-preserving down-closure of [HAj] *)
  have HAsel : Approx (fun p w => EvalRel g ρ (p ↦ w)) j u_sel
    := Approx_EvalRel_down Vρ HAj Vusel Le_usel.
  have [valY eqvalY] := IHy u_sel b WTu_sel HAsel evA_b.
  have TNσ0 : typing Δ ((Core.fix_ g)[σ]) A[σ]
    by (eapply substitution_tm; [ exact TY | exact TS | exact CΔ ]).
  have TNσ : typing Δ (Core.fix_ (g[σ])) A[σ] := TNσ0.
  (* the edge codomain also evaluates the (non-dependent!) codomain type *)
  have evB_af : EvalRel A ρ (app f u_sel).
  { destruct (is_bot (app f u_sel)) eqn:Hbaf.
    - have -> : app f u_sel = bot by apply is_bot_eq; rewrite Hbaf. apply EvalRel_bot.
    - have NB : ~ is_bot (app f u_sel) by rewrite Hbaf.
      move: (@EvalRel_Pi_app_type _ A (⟨↑⟩ A) ρ b f evTpi Vρ u_sel
               (app f u_sel) Vusel erefl NB (Core.fix_ g) evN_usel).
      rewrite subst1_shift. done. }
  have Caaf : compatible a (app f u_sel)
    by (eapply EvalRel_compatible; [ exact Vρ | exact evA_a | exact evB_af ]).
  have ELub : EvalRel A ρ (lub a (app f u_sel))
    by (exact (proj2 (EvalRel_compatible_lub Vρ evA_a evB_af) _ erefl)).
  have Waf : wt (app f u_sel) tuniv := wt_ty_tuniv (wt_Selection_abs WTbig Sel).
  have hUc : wt (lub a (app f u_sel)) tuniv := wt_lub (wt_ty_tuniv WT) Caaf Waf.
  have evU : EvalRel Core.tuniv ρ tuniv by (cbn; apply le_refl).
  have LEu_vsel : le u v_sel.
  { rewrite le_fun_cons in LEfun.
    have LEua := proj1 (andb_prop _ _ LEfun).
    rewrite Eq_vsel in LEua. exact LEua. }
  (* work at a fuel above the FUNCTION's rank, then drop to the result fuel *)
  pose RBf := S (max (max (rk (abs gt)) (rk (tpi b f))) (max (rk u) (rk a))).
  have RKusel : rk u_sel <= rk_fun gt := rk_Selection_key Sel.
  have RKb : rk b < rk (tpi b f) by (cbn; lia).
  have RKfg : rk_fun gt < rk (abs gt) by (cbn; lia).
  have HfM : max (rk (abs gt)) (rk (tpi b f)) < S RBf by (unfold RBf; lia).
  have HfN : max (rk u_sel) (rk b) < RBf by (unfold RBf; lia).
  have HrC : max (rk (lub a (app f u_sel))) (rk tuniv) < RBf.
  { have L1 := rk_lub a (app f u_sel). have L2 := rk_app f u_sel.
    have Hf : rk_fun f < rk (tpi b f) by (cbn; lia).
    have Htu : rk tuniv <= rk (tpi b f) by (cbn; lia).
    unfold RBf; lia. }
  have Hvsel : rk v_sel < RBf.
  { have L := rk_Selection_val Sel. have Hf : rk_fun f < rk (tpi b f) by (cbn; lia).
    unfold RBf; lia. }
  have Hafsel : rk (app f u_sel) < RBf.
  { have L := rk_app f u_sel. have Hf : rk_fun f < rk (tpi b f) by (cbn; lia).
    unfold RBf; lia. }
  (* the codomain-type block, COLLAPSED: the type is the fixed [A[σ]] *)
  have [VTA _] := STA ρ m Δ σ σ' TS TS' CS Fρ VS VS' EVS CΔ
                    (lub a (app f u_sel)) tuniv hUc ELub evU.
  have VTc : Val RBf Δ A[σ] Core.tuniv hUc := VTA RBf HrC.
  (* the codomain of the Π-edge collapses: [B = A⟨↑⟩] is non-dependent *)
  have Ecod : forall (X : Tm m), A[σ >> ren_Tm ↑][X .: var] = A[σ]
    by (move=> X; asimpl; reflexivity).
  split; move=> RB Hrank.
  - (* Val conjunct (Agda [adequacyV-Y-App-core]) *)
    have [valMbig _] :=
      STg ρ m Δ σ σ' TS TS' CS Fρ VS VS' EVS CΔ (abs gt) (tpi b f) WTbig evMbig evTpi.
    have VM := valMbig (S RBf) HfM. rewrite Val_abs in VM. move: VM => [_ VPi].
    move: VPi => [A0 [B0 [HRpi [CTpi [pav _]]]]].
    asimpl in HRpi.
    have [EA0 EB0] := HeadRed_tpi_eq HRpi. subst A0 B0.
    have Vapp := pav u_sel v_sel Sel WTu_sel (Core.fix_ (g[σ])) TNσ (valY RBf HfN).
    apply (Val_fuel_any (k := RBf) (k' := RB));
      [ unfold RBf; lia | unfold RBf; lia | lia | lia | ].
    asimpl in Vapp. rewrite Ecod in Vapp.
    exact (@Val_app_transport _ Δ _ _ u v_sel a (app f u_sel)
             (wt_Selection_abs WTbig Sel) WT hUc Caaf LEu_vsel RBf VTc Vapp).
  - (* EqVal cross conjunct (Agda [YCross]) *)
    have convNN'0 : conv Δ ((Core.fix_ g)[σ]) ((Core.fix_ g)[σ']) A[σ].
    { eapply subst_conv_cross;
        [ exact TY | exact CΔ | exact TS | exact TS' | exact CS ]. }
    have convNN' : conv Δ (Core.fix_ (g[σ])) (Core.fix_ (g[σ'])) A[σ] := convNN'0.
    have [_ eqvalMbig] :=
      STg ρ m Δ σ σ' TS TS' CS Fρ VS VS' EVS CΔ (abs gt) (tpi b f) WTbig evMbig evTpi.
    have EM := eqvalMbig (S RBf) HfM. rewrite EqVal_abs in EM.
    move: EM => [_ [_ [VPiM' EPi]]].
    move: EPi => [A0 [B0 [HRpi [CTpi paev]]]].
    move: VPiM' => [A0' [B0' [HRpi' [CTpi' [_ pae']]]]].
    asimpl in HRpi. asimpl in HRpi'.
    have [EA0 EB0] := HeadRed_tpi_eq HRpi. subst A0 B0.
    have [EA0' EB0'] := HeadRed_tpi_eq HRpi'. subst A0' B0'.
    have Efun := paev u_sel v_sel Sel WTu_sel (Core.fix_ (g[σ])) TNσ (valY RBf HfN).
    have Earg := pae' u_sel v_sel Sel WTu_sel (Core.fix_ (g[σ])) (Core.fix_ (g[σ']))
                   convNN' (eqvalY RBf HfN).
    have Ecomb := EqVal_trans Hvsel Hafsel Efun Earg.
    apply (EqVal_fuel_any (k := RBf) (k' := RB));
      [ unfold RBf; lia | unfold RBf; lia | lia | lia | ].
    asimpl in Ecomb. rewrite Ecod in Ecomb.
    exact (@EqVal_app_transport _ Δ _ _ _ u v_sel a (app f u_sel)
             (wt_Selection_abs WTbig Sel) WT hUc Caaf LEu_vsel RBf VTc Ecomb).
Qed.

(** Adequacy for [Y], stage by stage (Agda [adequacyV-Y-approx]): structural
    recursion on the Kleene index.  Stage [0] contributes only [bot]
    ([Val_Bot]/[EqVal_Bot]); stage [S j] head-expands along [hr_fix] (justified
    by [c_fix]) and hands the resulting contractum to [st_fix_app_core], with
    the stage-[j] instance of *this* lemma as the argument recursor. *)
Lemma st_fix_approx (A g : Tm n) :
  typing Γ A Core.tuniv ->
  typing Γ g (Core.tpi A (⟨↑⟩ A)) ->
  semantic_typing Γ A Core.tuniv ->
  semantic_typing Γ g (Core.tpi A (⟨↑⟩ A)) ->
  forall k ρ m (Δ : Ctx m) (σ σ': Sub n m)
    (TS : typing_subst Δ σ Γ) (TS' : typing_subst Δ σ' Γ)
    (CS : ConvSub Δ Γ σ σ') (Fρ : fits Γ ρ)
    (VS : ValSub Δ Γ σ ρ) (VS' : ValSub Δ Γ σ' ρ)
    (EVS : EqValSub Δ Γ σ σ' ρ) (CΔ : ctx Δ),
  forall u a (WT : wt u a),
    Approx (fun p w => EvalRel g ρ (p ↦ w)) k u ->
    EvalRel A ρ a ->
    (forall RB, max (rk u) (rk a) < RB -> Val RB Δ (Core.fix_ (g[σ])) A[σ] WT) /\
    (forall RB, max (rk u) (rk a) < RB ->
        EqVal RB Δ (Core.fix_ (g[σ])) (Core.fix_ (g[σ'])) A[σ] WT).
Proof.
  move=> TA Tg STA STg k.
  induction k as [ | j IH ];
    move=> ρ m Δ σ σ' TS TS' CS Fρ VS VS' EVS CΔ u a WT HA evA_a.
  - (* stage 0: the only approximant is [bot] *)
    move: HA => [Vu Lu].
    have Eu : u = bot by (apply le_bot_inv; exact Lu). subst u.
    split; move=> RB Hrank; [ apply Val_Bot | apply EqVal_Bot ].
  - (* stage [S j] *)
    destruct (is_bot u) eqn:Hu.
    { have Eu : u = bot by (apply is_bot_eq; rewrite Hu). subst u.
      split; move=> RB Hrank; [ apply Val_Bot | apply EqVal_Bot ]. }
    move: HA => [v0 [HAj evEdge]].
    have [Vcore Ecore] :
      (forall RB, max (rk u) (rk a) < RB ->
          Val RB Δ (Core.app (g[σ]) (Core.fix_ (g[σ]))) A[σ] WT) /\
      (forall RB, max (rk u) (rk a) < RB ->
          EqVal RB Δ (Core.app (g[σ]) (Core.fix_ (g[σ])))
                     (Core.app (g[σ']) (Core.fix_ (g[σ']))) A[σ] WT).
    { eapply st_fix_app_core;
        [ exact TA | exact Tg | exact STA | exact STg
        | exact TS | exact TS' | exact CS | exact Fρ | exact VS | exact VS'
        | exact EVS | exact CΔ
        | exact (IH ρ m Δ σ σ' TS TS' CS Fρ VS VS' EVS CΔ)
        | exact Hu | exact HAj | exact evEdge | exact evA_a ]. }
    (* head-expand both sides along [hr_fix] *)
    have Cfix : conv Γ (Core.fix_ g) (Core.app g (Core.fix_ g)) A
      by (eapply c_fix; [ exact TA | exact Tg ]).
    have CfixS00 : conv Δ ((Core.fix_ g)[σ]) ((Core.app g (Core.fix_ g))[σ]) A[σ]
      by (eapply substitution_conv; [ exact Cfix | exact TS | exact CΔ ]).
    have CfixS : conv Δ (Core.fix_ (g[σ])) (Core.app (g[σ]) (Core.fix_ (g[σ]))) A[σ]
      := CfixS00.
    have CfixS'00 : conv Δ ((Core.fix_ g)[σ']) ((Core.app g (Core.fix_ g))[σ']) A[σ']
      by (eapply substitution_conv; [ exact Cfix | exact TS' | exact CΔ ]).
    have CfixS'0 : conv Δ (Core.fix_ (g[σ'])) (Core.app (g[σ']) (Core.fix_ (g[σ']))) A[σ']
      := CfixS'00.
    have convA0 : conv Δ A[σ] A[σ'] Core.tuniv[σ].
    { eapply subst_conv_cross;
        [ exact TA | exact CΔ | exact TS | exact TS' | exact CS ]. }
    have convA : conv Δ A[σ] A[σ'] Core.tuniv := convA0.
    have CfixS' : conv Δ (Core.fix_ (g[σ'])) (Core.app (g[σ']) (Core.fix_ (g[σ']))) A[σ]
      by (eapply c_conv; [ exact CfixS'0 | apply c_sym; exact convA ]).
    have HRfix : forall (h : Tm m),
        HeadRed (Core.fix_ h) (Core.app h (Core.fix_ h))
      by (move=> h; eapply ms_trans; [ apply hr_fix | apply ms_refl ]).
    split; move=> RB Hrank.
    + eapply Val_beta_expand;
        [ exact (HRfix (g[σ])) | exact CfixS | exact (Vcore RB Hrank) ].
    + eapply EqVal_headred_expand;
        [ exact (HRfix (g[σ])) | exact (HRfix (g[σ'])) | exact CfixS | exact CfixS'
        | exact (Ecore RB Hrank) ].
Qed.

(** Adequacy for [Y] (Agda [ty-Y] / [NAT/Adequacy/YCore.agda]): every Kleene
    approximant of [fix_ g] is valid at [A].  All the work is in
    [st_fix_approx]; here we merely open the existential Kleene index carried
    by [EvalRel (fix_ g) ρ u]. *)
Lemma st_fix (A g : Tm n) :
  typing Γ A Core.tuniv ->
  typing Γ g (Core.tpi A (⟨↑⟩ A)) ->
  semantic_typing Γ A Core.tuniv ->
  semantic_typing Γ g (Core.tpi A (⟨↑⟩ A)) ->
(* ------------------------- *)
  semantic_typing Γ (Core.fix_ g) A.
Proof.
  move=> TA Tg STA STg.
  move=> ρ m Δ σ σ' TS TS' CS Fρ VS VS' EVS CΔ u a WT evY evA.
  move: evY => [k HA].
  eapply st_fix_approx;
    [ exact TA | exact Tg | exact STA | exact STg
    | exact TS | exact TS' | exact CS | exact Fρ | exact VS | exact VS'
    | exact EVS | exact CΔ | exact HA | exact evA ].
Qed.

(** The Y-unfolding conversion (Agda [conv-Y]).  Proved from [st_fix] exactly as
    [sc_beta] is proved from [st_abs]/[st_app]: take the redex's reflexive
    [EqVal] and contract the second side along [hr_fix], with [c_fix] as the
    step conversion. *)
Lemma sc_fix (A g : Tm n) :
  typing Γ A Core.tuniv ->
  typing Γ g (Core.tpi A (⟨↑⟩ A)) ->
  semantic_typing Γ A Core.tuniv ->
  semantic_typing Γ g (Core.tpi A (⟨↑⟩ A)) ->
(* ------------------------- *)
  semantic_conv2 Γ (Core.fix_ g) (Core.app g (Core.fix_ g)) A.
Proof.
  move=> TA Tg STA STg.
  have STY : semantic_typing Γ (Core.fix_ g) A
    by (eapply st_fix; [ exact TA | exact Tg | exact STA | exact STg ]).
  have TY : typing Γ (Core.fix_ g) A by (eapply t_fix; [ exact TA | exact Tg ]).
  have Cfix : conv Γ (Core.fix_ g) (Core.app g (Core.fix_ g)) A
    by (eapply c_fix; [ exact TA | exact Tg ]).
  move=> ρ m Δ σ TS FR VS CD u a WT evY evA RB Hrank.
  have eqY :=
    proj2 (STY ρ m Δ σ σ TS TS (ConvSub_refl TS) FR VS VS (ValSub_EqValSub VS)
             CD u a WT evY evA).
  have CfixS : conv Δ (Core.fix_ g)[σ] ((Core.app g (Core.fix_ g))[σ]) (A[σ])
    by (eapply substitution_conv; [ exact Cfix | exact TS | exact CD ]).
  have CreflS : conv Δ (Core.fix_ g)[σ] (Core.fix_ g)[σ] (A[σ])
    by (apply c_refl; eapply substitution_tm; [ exact TY | exact TS | exact CD ]).
  eapply EqVal_headred_contract.
  - apply ms_refl.
  - eapply ms_trans; [ apply hr_fix | apply ms_refl ].
  - exact CreflS.
  - apply c_sym; exact CfixS.
  - exact (eqY RB Hrank).
Qed.

(** Congruence for [Y] (Agda [conv-Y-cong] / [NAT/Adequacy/YCross.agda]),
    stage by stage.  Structural recursion on the Kleene index of the *first*
    chain: the two fixpoints' approximant chains are related step by step
    through the step functions' [semantic_conv2].

    The [S j] step is the [EqVal] half of [st_fix_app_core] with the two
    variations retargeted: the function varies [g[σ] → g'[σ]] (from [SCg]
    rather than from a cross-substitution) and the argument varies
    [fix_ (g[σ]) → fix_ (g'[σ])] (from the stage-[j] recursor).  Because a
    single substitution is used throughout, no [c_conv] retyping is needed on
    the second side. *)
Lemma sc_fix_approx (A g g' : Tm n) :
  typing Γ A Core.tuniv ->
  typing Γ g (Core.tpi A (⟨↑⟩ A)) ->
  typing Γ g' (Core.tpi A (⟨↑⟩ A)) ->
  conv Γ g g' (Core.tpi A (⟨↑⟩ A)) ->
  semantic_typing Γ A Core.tuniv ->
  semantic_typing Γ g (Core.tpi A (⟨↑⟩ A)) ->
  semantic_conv2 Γ g g' (Core.tpi A (⟨↑⟩ A)) ->
  forall k ρ m (Δ : Ctx m) (σ : Sub n m) (TS : typing_subst Δ σ Γ)
    (Fρ : fits Γ ρ) (VS : ValSub Δ Γ σ ρ) (CΔ : ctx Δ),
  forall u a (WT : wt u a),
    Approx (fun p w => EvalRel g ρ (p ↦ w)) k u ->
    EvalRel A ρ a ->
    forall RB, max (rk u) (rk a) < RB ->
      EqVal RB Δ (Core.fix_ (g[σ])) (Core.fix_ (g'[σ])) A[σ] WT.
Proof.
  move=> TA Tg Tg' Cgg' STA STg SCg k.
  induction k as [ | j IH ];
    move=> ρ m Δ σ TS Fρ VS CΔ u a WT HA evA_a.
  - (* stage 0: the only approximant is [bot] *)
    move: HA => [Vu Lu].
    have Eu : u = bot by (apply le_bot_inv; exact Lu). subst u.
    move=> RB Hrank. apply EqVal_Bot.
  - (* stage [S j] *)
    destruct (is_bot u) eqn:Hu.
    { have Eu : u = bot by (apply is_bot_eq; rewrite Hu). subst u.
      move=> RB Hrank. apply EqVal_Bot. }
    move: HA => [v0 [HAj evEdge]].
    have Vρ : valid_env ρ := fits_valid_env Fρ.
    have TY : typing Γ (Core.fix_ g) A by (eapply t_fix; [ exact TA | exact Tg ]).
    have TY' : typing Γ (Core.fix_ g') A by (eapply t_fix; [ exact TA | exact Tg' ]).
    have evN : EvalRel (Core.fix_ g) ρ v0 by (exists j; exact HAj).
    (* --- the App-cross core, mirroring [st_fix_app_core] --- *)
    have Ecore : forall RB, max (rk u) (rk a) < RB ->
        EqVal RB Δ (Core.app (g[σ]) (Core.fix_ (g[σ])))
                   (Core.app (g'[σ]) (Core.fix_ (g'[σ]))) A[σ] WT.
    { have IT : InvTyped Γ g (Core.tpi A (⟨↑⟩ A)) ρ.
      { apply typing_EvalRel. exact Tg. exact Fρ. }
      have [vbig [abig [WTbig [LEbig [evMbig evTpi]]]]] := IT (v0 ↦ u) evEdge.
      unfold singleton in LEbig. rewrite Hu in LEbig.
      have [gt [Evbig LEfun]] := le_abs_inv LEbig. subst vbig.
      destruct abig as [ | | | | | b f | | | | | | ];
        try solve [ exfalso; clear -WTbig; inversion WTbig ].
      have evTpiC := evTpi. cbn in evTpiC. move: evTpiC => [Vb [Vf [evA_b _]]].
      have Vg : valid_fun gt := proj1 (andb_prop _ _ (wt_valid_tm WTbig)).
      have Vv0 : valid v0 := EvalRel_valid evN.
      have [u_sel [v_sel [Sel [Le_usel Eq_vsel]]]] := selectionBelow Vg Vv0.
      have [WTu_sel WTv_sel] : wt u_sel b /\ wt v_sel (app f u_sel).
      { eapply wt_Selection_cod;
          [ exact (wt_abs_ty WTbig) | exact (wt_abs_inv1 WTbig)
          | move=> ui vi Hin; exact (wt_abs_inv2 WTbig Hin erefl)
          | exact Vg | exact Sel ]. }
      have Vusel : valid u_sel := wt_valid_tm WTu_sel.
      have evN_usel : EvalRel (Core.fix_ g) ρ u_sel
        by (eapply EvalRel_down; [ exact Vρ | exact Vusel | exact evN | exact Le_usel ]).
      have HAsel : Approx (fun p w => EvalRel g ρ (p ↦ w)) j u_sel
        := Approx_EvalRel_down Vρ HAj Vusel Le_usel.
      (* argument, first side: [Val] of [fix_ g] from [st_fix] *)
      have STY : semantic_typing Γ (Core.fix_ g) A
        by (eapply st_fix; [ exact TA | exact Tg | exact STA | exact STg ]).
      have [valArg _] :=
        STY ρ m Δ σ σ TS TS (ConvSub_refl TS) Fρ VS VS
          (ValSub_EqValSub VS) CΔ u_sel b WTu_sel evN_usel evA_b.
      (* argument variation: the stage-[j] recursor *)
      have eqArg := IH ρ m Δ σ TS Fρ VS CΔ u_sel b WTu_sel HAsel evA_b.
      have TNσ0 : typing Δ ((Core.fix_ g)[σ]) A[σ]
        by (eapply substitution_tm; [ exact TY | exact TS | exact CΔ ]).
      have TNσ : typing Δ (Core.fix_ (g[σ])) A[σ] := TNσ0.
      have CY : conv Γ (Core.fix_ g) (Core.fix_ g') A
        by (eapply c_fix_cong; [ exact TA | exact Tg | exact Tg' | exact Cgg' ]).
      have convNN'0 : conv Δ ((Core.fix_ g)[σ]) ((Core.fix_ g')[σ]) A[σ]
        by (eapply substitution_conv; [ exact CY | exact TS | exact CΔ ]).
      have convNN' : conv Δ (Core.fix_ (g[σ])) (Core.fix_ (g'[σ])) A[σ] := convNN'0.
      (* the edge codomain also evaluates the (non-dependent) codomain type *)
      have evB_af : EvalRel A ρ (app f u_sel).
      { destruct (is_bot (app f u_sel)) eqn:Hbaf.
        - have -> : app f u_sel = bot by apply is_bot_eq; rewrite Hbaf. apply EvalRel_bot.
        - have NB : ~ is_bot (app f u_sel) by rewrite Hbaf.
          move: (@EvalRel_Pi_app_type _ A (⟨↑⟩ A) ρ b f evTpi Vρ u_sel
                   (app f u_sel) Vusel erefl NB (Core.fix_ g) evN_usel).
          rewrite subst1_shift. done. }
      have Caaf : compatible a (app f u_sel)
        by (eapply EvalRel_compatible; [ exact Vρ | exact evA_a | exact evB_af ]).
      have ELub : EvalRel A ρ (lub a (app f u_sel))
        by (exact (proj2 (EvalRel_compatible_lub Vρ evA_a evB_af) _ erefl)).
      have Waf : wt (app f u_sel) tuniv := wt_ty_tuniv (wt_Selection_abs WTbig Sel).
      have hUc : wt (lub a (app f u_sel)) tuniv := wt_lub (wt_ty_tuniv WT) Caaf Waf.
      have evU : EvalRel Core.tuniv ρ tuniv by (cbn; apply le_refl).
      have LEu_vsel : le u v_sel.
      { rewrite le_fun_cons in LEfun.
        have LEua := proj1 (andb_prop _ _ LEfun).
        rewrite Eq_vsel in LEua. exact LEua. }
      move=> RB Hrank.
      pose RBf := S (max (max (rk (abs gt)) (rk (tpi b f))) (max (rk u) (rk a))).
      have RKusel : rk u_sel <= rk_fun gt := rk_Selection_key Sel.
      have RKb : rk b < rk (tpi b f) by (cbn; lia).
      have RKfg : rk_fun gt < rk (abs gt) by (cbn; lia).
      have HfM : max (rk (abs gt)) (rk (tpi b f)) < S RBf by (unfold RBf; lia).
      have HfN : max (rk u_sel) (rk b) < RBf by (unfold RBf; lia).
      have HrC : max (rk (lub a (app f u_sel))) (rk tuniv) < RBf.
      { have L1 := rk_lub a (app f u_sel). have L2 := rk_app f u_sel.
        have Hf : rk_fun f < rk (tpi b f) by (cbn; lia).
        have Htu : rk tuniv <= rk (tpi b f) by (cbn; lia).
        unfold RBf; lia. }
      have Hvsel : rk v_sel < RBf.
      { have L := rk_Selection_val Sel. have Hf : rk_fun f < rk (tpi b f) by (cbn; lia).
        unfold RBf; lia. }
      have Hafsel : rk (app f u_sel) < RBf.
      { have L := rk_app f u_sel. have Hf : rk_fun f < rk (tpi b f) by (cbn; lia).
        unfold RBf; lia. }
      (* codomain-type block, COLLAPSED (the type is the fixed [A[σ]]) *)
      have [VTA _] := STA ρ m Δ σ σ TS TS (ConvSub_refl TS) Fρ VS VS
                        (ValSub_EqValSub VS) CΔ (lub a (app f u_sel)) tuniv hUc ELub evU.
      have VTc : Val RBf Δ A[σ] Core.tuniv hUc := VTA RBf HrC.
      have Ecod : forall (X : Tm m), A[σ >> ren_Tm ↑][X .: var] = A[σ]
        by (move=> X; asimpl; reflexivity).
      (* the step functions' conversion, at the enlarged function value *)
      have EM := SCg ρ m Δ σ TS Fρ VS CΔ (abs gt) (tpi b f) WTbig evMbig evTpi
                   (S RBf) HfM.
      rewrite EqVal_abs in EM.
      move: EM => [_ [_ [VPiM' EPi]]].
      move: EPi => [A0 [B0 [HRpi [CTpi paev]]]].
      move: VPiM' => [A0' [B0' [HRpi' [CTpi' [_ pae']]]]].
      asimpl in HRpi. asimpl in HRpi'.
      have [EA0 EB0] := HeadRed_tpi_eq HRpi. subst A0 B0.
      have [EA0' EB0'] := HeadRed_tpi_eq HRpi'. subst A0' B0'.
      (* function variation: [app g[σ] (fix_ g[σ])] vs [app g'[σ] (fix_ g[σ])] *)
      have Efun := paev u_sel v_sel Sel WTu_sel (Core.fix_ (g[σ])) TNσ (valArg RBf HfN).
      (* argument variation: [app g'[σ] (fix_ g[σ])] vs [app g'[σ] (fix_ g'[σ])] *)
      have Earg := pae' u_sel v_sel Sel WTu_sel (Core.fix_ (g[σ])) (Core.fix_ (g'[σ]))
                     convNN' (eqArg RBf HfN).
      have Ecomb := EqVal_trans Hvsel Hafsel Efun Earg.
      apply (EqVal_fuel_any (k := RBf) (k' := RB));
        [ unfold RBf; lia | unfold RBf; lia | lia | lia | ].
      asimpl in Ecomb. rewrite Ecod in Ecomb.
      exact (@EqVal_app_transport _ Δ _ _ _ u v_sel a (app f u_sel)
               (wt_Selection_abs WTbig Sel) WT hUc Caaf LEu_vsel RBf VTc Ecomb). }
    (* head-expand both sides along [hr_fix] *)
    have Cfix : conv Γ (Core.fix_ g) (Core.app g (Core.fix_ g)) A
      by (eapply c_fix; [ exact TA | exact Tg ]).
    have Cfix' : conv Γ (Core.fix_ g') (Core.app g' (Core.fix_ g')) A
      by (eapply c_fix; [ exact TA | exact Tg' ]).
    have CfixS00 : conv Δ ((Core.fix_ g)[σ]) ((Core.app g (Core.fix_ g))[σ]) A[σ]
      by (eapply substitution_conv; [ exact Cfix | exact TS | exact CΔ ]).
    have CfixS : conv Δ (Core.fix_ (g[σ])) (Core.app (g[σ]) (Core.fix_ (g[σ]))) A[σ]
      := CfixS00.
    have CfixS'00 : conv Δ ((Core.fix_ g')[σ]) ((Core.app g' (Core.fix_ g'))[σ]) A[σ]
      by (eapply substitution_conv; [ exact Cfix' | exact TS | exact CΔ ]).
    have CfixS' : conv Δ (Core.fix_ (g'[σ])) (Core.app (g'[σ]) (Core.fix_ (g'[σ]))) A[σ]
      := CfixS'00.
    have HRfix : forall (h : Tm m),
        HeadRed (Core.fix_ h) (Core.app h (Core.fix_ h))
      by (move=> h; eapply ms_trans; [ apply hr_fix | apply ms_refl ]).
    move=> RB Hrank.
    eapply EqVal_headred_expand;
      [ exact (HRfix (g[σ])) | exact (HRfix (g'[σ])) | exact CfixS | exact CfixS'
      | exact (Ecore RB Hrank) ].
Qed.

(** Congruence for [Y] (Agda [conv-Y-cong] / [NAT/Adequacy/YCross.agda]): all
    the work is in [sc_fix_approx]; here we merely open the existential Kleene
    index carried by [EvalRel (fix_ g) ρ u]. *)
Lemma sc_fix_cong (A g g' : Tm n) :
  typing Γ A Core.tuniv ->
  typing Γ g (Core.tpi A (⟨↑⟩ A)) ->
  typing Γ g' (Core.tpi A (⟨↑⟩ A)) ->
  conv Γ g g' (Core.tpi A (⟨↑⟩ A)) ->
  semantic_typing Γ A Core.tuniv ->
  semantic_typing Γ g (Core.tpi A (⟨↑⟩ A)) ->
  semantic_typing Γ g' (Core.tpi A (⟨↑⟩ A)) ->
  semantic_conv2 Γ g g' (Core.tpi A (⟨↑⟩ A)) ->
(* ------------------------- *)
  semantic_conv2 Γ (Core.fix_ g) (Core.fix_ g') A.
Proof.
  move=> TA Tg Tg' Cgg' STA STg STg' SCg.
  move=> ρ m Δ σ TS Fρ VS CΔ u a WT evY evA.
  move: evY => [k HA].
  eapply sc_fix_approx;
    [ exact TA | exact Tg | exact Tg' | exact Cgg' | exact STA | exact STg
    | exact SCg | exact TS | exact Fρ | exact VS | exact CΔ | exact HA | exact evA ].
Qed.

(* =====================================================================
   Adequacy for the identity fragment (Agda [ID/Adequacy/*]).

   *** THE REMAINING GAPS OF THE [ID] PORT.  The Agda counterpart is the
       eight-file J driver: [JApp], [JAppE], [JCase], [JDriver],
       [JEndpoint], [JMotive], [JRef], [JTypeEq]. ***

   [st_tid] and [st_rfl] are the formers and follow [st_tpi] / [st_abs]:
   the [tid]/[rfl] arms of [Val]/[EqVal] are exactly the records
   [Rec.ValTyId] / [Rec.ValId] built in [raw_validity.v], and every field is
   either syntactic (the recorded [HeadRed] and [Red3] conversions, from
   [red1_conv]) or a component appeal to the hypotheses.

   [st_jcase] is the driver: on the informative branch the proof's value is
   [rfl w], and [ValId] hands back both the witness's validity and its two
   endpoint equalities -- which is exactly what the motive's [PiApp] edges
   need.  [sc_jcase_beta] then head-contracts along [hr_jcase] with
   [c_jcase_beta] as the step conversion, in the [sc_beta] style; because
   both sides have the *same* type there is no type transport to do.
   ===================================================================== *)

(* ---- the identity *type* former, on the model of [st_tpi] ---- *)

Lemma st_tid_Val_edge (A a b : Tm n)
  (TA : typing Γ A Core.tuniv) (Ta : typing Γ a A) (Tb : typing Γ b A)
  (STA : semantic_typing Γ A Core.tuniv)
  (STa : semantic_typing Γ a A) (STb : semantic_typing Γ b A)
  ρ m (Δ : Ctx m) (σ σ' : Sub n m)
  (TS : typing_subst Δ σ Γ) (TS' : typing_subst Δ σ' Γ) (CS : ConvSub Δ Γ σ σ')
  (Fρ : fits Γ ρ) (VS : ValSub Δ Γ σ ρ) (VS' : ValSub Δ Γ σ' ρ)
  (EVS : EqValSub Δ Γ σ σ' ρ) (CΔ : ctx Δ) u a0 (WT : wt u a0)
  (evId : EvalRel (Core.tid A a b) ρ u) (evU0 : EvalRel Core.tuniv ρ a0) :
  forall RB, max (rk u) (rk a0) < RB ->
    Val RB Δ (Core.tid A a b)[σ] Core.tuniv[σ] WT.
Proof.
  have Vρ : valid_env ρ := fits_valid_env Fρ.
  have TAs : typing Δ A[σ] Core.tuniv
    by (move: (substitution_tm _ _ _ _ _ TA TS CΔ) => hh; cbn in hh; exact hh).
  have Tas : typing Δ a[σ] A[σ] by (eapply substitution_tm; [ exact Ta | exact TS | exact CΔ ]).
  have Tbs : typing Δ b[σ] A[σ] by (eapply substitution_tm; [ exact Tb | exact TS | exact CΔ ]).
  have evU : EvalRel Core.tuniv ρ tuniv by (cbn; apply le_refl).
  cbn in evId.
  move=> RB Hrank. destruct RB; [ exact I | ].
  destruct u as [ | | | | | | | t v w | | | | ]; try done.
  - (* u = bot *) apply Val_Bot.
  - (* u = tid t v w *)
    move: evId => [Vid [evAt [evav evbw]]].
    have Eatu : a0 = tuniv by (inversion WT; auto). subst a0.
    have [valA _] :=
      STA ρ m Δ σ σ' TS TS' CS Fρ VS VS' EVS CΔ t tuniv (wt_tid_dom WT) evAt evU.
    have [valLhs _] :=
      STa ρ m Δ σ σ' TS TS' CS Fρ VS VS' EVS CΔ v t (wt_tid_lhs WT) evav evAt.
    have [valRhs _] :=
      STb ρ m Δ σ σ' TS TS' CS Fρ VS VS' EVS CΔ w t (wt_tid_rhs WT) evbw evAt.
    rewrite Val_tuniv. rewrite ValTy_tid.
    (* the domain sits at [tuniv], whose rank is 1, so the low-fuel boundary
       needs the same [rk_bot_inv] dodge as [st_tpi] *)
    have valDom : Val RB Δ A[σ] Core.tuniv (wt_tid_dom WT).
    { destruct (le_lt_dec 2 RB) as [HRB|HRB].
      - eapply Val_irr; eapply valA; cbn in Hrank |- *; lia.
      - have Et : t = bot by (apply rk_bot_inv; cbn in Hrank; lia).
        move: (wt_tid_dom WT). rewrite Et. move=> ww. apply Val_Bot. }
    exists A[σ]. exists a[σ]. exists b[σ].
    split; [ apply ms_refl | ].
    split; [ exact TAs | ]. split; [ exact Tas | ]. split; [ exact Tbs | ].
    split; [ exact (wt_valid_tm WT) | ].
    split; [ exact valDom | ].
    split.
    + eapply Val_irr. eapply valLhs. cbn in Hrank |- *; lia.
    + eapply Val_irr. eapply valRhs. cbn in Hrank |- *; lia.
Qed.

Lemma st_tid_EqVal_edge (A a b : Tm n)
  (TA : typing Γ A Core.tuniv) (Ta : typing Γ a A) (Tb : typing Γ b A)
  (STA : semantic_typing Γ A Core.tuniv)
  (STa : semantic_typing Γ a A) (STb : semantic_typing Γ b A)
  ρ m (Δ : Ctx m) (σ σ' : Sub n m)
  (TS : typing_subst Δ σ Γ) (TS' : typing_subst Δ σ' Γ) (CS : ConvSub Δ Γ σ σ')
  (Fρ : fits Γ ρ) (VS : ValSub Δ Γ σ ρ) (VS' : ValSub Δ Γ σ' ρ)
  (EVS : EqValSub Δ Γ σ σ' ρ) (CΔ : ctx Δ) u a0 (WT : wt u a0)
  (evId : EvalRel (Core.tid A a b) ρ u) (evU0 : EvalRel Core.tuniv ρ a0) :
  forall RB, max (rk u) (rk a0) < RB ->
    EqVal RB Δ (Core.tid A a b)[σ] (Core.tid A a b)[σ'] Core.tuniv[σ] WT.
Proof.
  have Vρ : valid_env ρ := fits_valid_env Fρ.
  have evU : EvalRel Core.tuniv ρ tuniv by (cbn; apply le_refl).
  have evId0 := evId. cbn in evId.
  move=> RB Hrank. destruct RB; [ exact I | ].
  destruct u as [ | | | | | | | t v w | | | | ]; try done.
  - (* u = bot *) apply EqVal_Bot.
  - move: evId => [Vid [evAt [evav evbw]]].
    have Eatu : a0 = tuniv by (inversion WT; auto). subst a0.
    have VMv : Val (S RB) Δ (Core.tid A a b)[σ] Core.tuniv[σ] WT
      by (eapply st_tid_Val_edge; eassumption).
    have VNv : Val (S RB) Δ (Core.tid A a b)[σ'] Core.tuniv[σ'] WT.
    { eapply st_tid_Val_edge with (σ' := σ'); try eassumption.
      - exact (ConvSub_refl TS').
      - exact (ValSub_EqValSub VS'). }
    rewrite Val_tuniv in VMv. rewrite Val_tuniv in VNv.
    have convAA' : conv Δ A[σ] A[σ'] Core.tuniv := subst_conv_cross TA CΔ TS TS' CS.
    have convaa' : conv Δ a[σ] a[σ'] A[σ] := subst_conv_cross Ta CΔ TS TS' CS.
    have convbb' : conv Δ b[σ] b[σ'] A[σ] := subst_conv_cross Tb CΔ TS TS' CS.
    have [_ eqA] :=
      STA ρ m Δ σ σ' TS TS' CS Fρ VS VS' EVS CΔ t tuniv (wt_tid_dom WT) evAt evU.
    have [_ eqLhs] :=
      STa ρ m Δ σ σ' TS TS' CS Fρ VS VS' EVS CΔ v t (wt_tid_lhs WT) evav evAt.
    have [_ eqRhs] :=
      STb ρ m Δ σ σ' TS TS' CS Fρ VS VS' EVS CΔ w t (wt_tid_rhs WT) evbw evAt.
    have eqDom : EqVal RB Δ A[σ] A[σ'] Core.tuniv (wt_tid_dom WT).
    { destruct (le_lt_dec 2 RB) as [HRB|HRB].
      - eapply EqVal_irr; eapply eqA; cbn in Hrank |- *; lia.
      - have Et : t = bot by (apply rk_bot_inv; cbn in Hrank; lia).
        move: (wt_tid_dom WT). rewrite Et. move=> ww. apply EqVal_Bot. }
    rewrite EqVal_tuniv.
    split; [ exact VMv | ]. split; [ exact VNv | ].
    rewrite EqValTy_tid.
    split; [ exact VMv | ]. split; [ exact VNv | ].
    exists A[σ]. exists a[σ]. exists b[σ]. split; [ apply ms_refl | ].
    exists A[σ']. exists a[σ']. exists b[σ']. split; [ apply ms_refl | ].
    split; [ exact convAA' | ]. split; [ exact convaa' | ]. split; [ exact convbb' | ].
    split; [ exact (wt_valid_tm WT) | ].
    split; [ exact eqDom | ].
    split.
    + eapply EqVal_irr. eapply eqLhs. cbn in Hrank |- *; lia.
    + eapply EqVal_irr. eapply eqRhs. cbn in Hrank |- *; lia.
Qed.

Lemma st_tid (A a b : Tm n) :
  typing Γ A Core.tuniv ->
  typing Γ a A ->
  typing Γ b A ->
  semantic_typing Γ A Core.tuniv ->
  semantic_typing Γ a A ->
  semantic_typing Γ b A ->
(* ------------------------- *)
  semantic_typing Γ (Core.tid A a b) Core.tuniv.
Proof.
  move=> TA Ta Tb STA STa STb.
  move=> ρ m Δ σ σ' TS TS' CS Fρ VS VS' EVS CΔ u a0 WT evId evU0.
  split.
  - eapply st_tid_Val_edge; eassumption.
  - eapply st_tid_EqVal_edge; eassumption.
Qed.

(* ---- the proof former.  Its [Val] cell is [ValTy] of the type together with
   [ValId], whose witness data is entirely [a]'s own validity: the two endpoint
   conversions are reflexivity, since [rfl a : tid A a a] is the diagonal. ---- *)

Lemma st_rfl_Val_edge (A a : Tm n)
  (TA : typing Γ A Core.tuniv) (Ta : typing Γ a A)
  (STA : semantic_typing Γ A Core.tuniv) (STa : semantic_typing Γ a A)
  ρ m (Δ : Ctx m) (σ σ' : Sub n m)
  (TS : typing_subst Δ σ Γ) (TS' : typing_subst Δ σ' Γ) (CS : ConvSub Δ Γ σ σ')
  (Fρ : fits Γ ρ) (VS : ValSub Δ Γ σ ρ) (VS' : ValSub Δ Γ σ' ρ)
  (EVS : EqValSub Δ Γ σ σ' ρ) (CΔ : ctx Δ) u a0 (WT : wt u a0)
  (evR : EvalRel (Core.rfl a) ρ u) (evId : EvalRel (Core.tid A a a) ρ a0) :
  forall RB, max (rk u) (rk a0) < RB ->
    Val RB Δ (Core.rfl a)[σ] (Core.tid A a a)[σ] WT.
Proof.
  have Vρ : valid_env ρ := fits_valid_env Fρ.
  have TAs : typing Δ A[σ] Core.tuniv
    by (move: (substitution_tm _ _ _ _ _ TA TS CΔ) => hh; cbn in hh; exact hh).
  have Tas : typing Δ a[σ] A[σ] by (eapply substitution_tm; [ exact Ta | exact TS | exact CΔ ]).
  have TRs : typing Δ (Core.rfl a[σ]) (Core.tid A[σ] a[σ] a[σ])
    by (eapply t_rfl; [ exact TAs | exact Tas ]).
  have evId0 := evId. cbn in evR, evId.
  move=> RB Hrank. destruct RB; [ exact I | ].
  (* [try done] also disposes of the [bot] type code and the [bot] element:
     [Val] is [True] at both *)
  destruct a0 as [ | | | | | | | t v w | | | | ]; try done.
  destruct u as [ | | | | | | | | ww | | | ]; try done.
  (* u = rfl ww, type code = tid t v w *)
  move: evId => [Vid [evAt [evav evaw]]].
  rewrite Val_rfl.
  (* the type record: exactly [st_tid_Val_edge] at [b := a] *)
  have VTy : Val (S RB) Δ (Core.tid A a a)[σ] Core.tuniv[σ] (wt_rfl_ty WT).
  { eapply st_tid_Val_edge;
      [ exact TA | exact Ta | exact Ta | exact STA | exact STa | exact STa
      | exact TS | exact TS' | exact CS | exact Fρ | exact VS | exact VS'
      | exact EVS | exact CΔ | exact evId0 | cbn; apply le_refl; done
      | cbn in Hrank |- *; lia ]. }
  have [valWit _] :=
    STa ρ m Δ σ σ' TS TS' CS Fρ VS VS' EVS CΔ ww t (wt_rfl_wit WT) evR evAt.
  have VW : Val RB Δ a[σ] A[σ] (wt_rfl_wit WT)
    by (eapply valWit; cbn in Hrank |- *; lia).
  split; [ eapply Val_ValTy; exact VTy | ].
  exists A[σ]. exists a[σ]. exists a[σ]. split; [ apply ms_refl | ].
  exists a[σ]. split; [ apply ms_refl | ].
  split; [ apply c_refl; exact TRs | ].
  split; [ apply c_refl; exact Tas | ].
  split; [ apply c_refl; exact Tas | ].
  split; [ exact VW | ].
  split; [ eapply Val_EqVal; exact VW | eapply Val_EqVal; exact VW ].
Qed.

Lemma st_rfl_EqVal_edge (A a : Tm n)
  (TA : typing Γ A Core.tuniv) (Ta : typing Γ a A)
  (STA : semantic_typing Γ A Core.tuniv) (STa : semantic_typing Γ a A)
  ρ m (Δ : Ctx m) (σ σ' : Sub n m)
  (TS : typing_subst Δ σ Γ) (TS' : typing_subst Δ σ' Γ) (CS : ConvSub Δ Γ σ σ')
  (Fρ : fits Γ ρ) (VS : ValSub Δ Γ σ ρ) (VS' : ValSub Δ Γ σ' ρ)
  (EVS : EqValSub Δ Γ σ σ' ρ) (CΔ : ctx Δ) u a0 (WT : wt u a0)
  (evR : EvalRel (Core.rfl a) ρ u) (evId : EvalRel (Core.tid A a a) ρ a0) :
  forall RB, max (rk u) (rk a0) < RB ->
    EqVal RB Δ (Core.rfl a)[σ] (Core.rfl a)[σ'] (Core.tid A a a)[σ] WT.
Proof.
  have Vρ : valid_env ρ := fits_valid_env Fρ.
  have TAs : typing Δ A[σ] Core.tuniv
    by (move: (substitution_tm _ _ _ _ _ TA TS CΔ) => hh; cbn in hh; exact hh).
  have TAs' : typing Δ A[σ'] Core.tuniv
    by (move: (substitution_tm _ _ _ _ _ TA TS' CΔ) => hh; cbn in hh; exact hh).
  have Tas : typing Δ a[σ] A[σ] by (eapply substitution_tm; [ exact Ta | exact TS | exact CΔ ]).
  have Tas' : typing Δ a[σ'] A[σ'] by (eapply substitution_tm; [ exact Ta | exact TS' | exact CΔ ]).
  have convAA' : conv Δ A[σ] A[σ'] Core.tuniv := subst_conv_cross TA CΔ TS TS' CS.
  have convaa' : conv Δ a[σ] a[σ'] A[σ] := subst_conv_cross Ta CΔ TS TS' CS.
  (* the primed proof, retyped at the unprimed identity type *)
  have convIds : conv Δ (Core.tid A[σ] a[σ] a[σ]) (Core.tid A[σ'] a[σ'] a[σ']) Core.tuniv
    by (eapply c_tid;
          [ exact TAs | exact Tas | exact Tas | exact convAA' | exact convaa'
          | exact convaa' ]).
  have Tas'0 : typing Δ a[σ'] A[σ]
    by (eapply t_conv; [ exact Tas' | apply c_sym; exact convAA' ]).
  have TRs : typing Δ (Core.rfl a[σ]) (Core.tid A[σ] a[σ] a[σ])
    by (eapply t_rfl; [ exact TAs | exact Tas ]).
  have TRs' : typing Δ (Core.rfl a[σ']) (Core.tid A[σ] a[σ] a[σ])
    by (eapply t_conv;
          [ eapply t_rfl; [ exact TAs' | exact Tas' ] | apply c_sym; exact convIds ]).
  have evId0 := evId. cbn in evR, evId.
  move=> RB Hrank. destruct RB; [ exact I | ].
  destruct a0 as [ | | | | | | | t v w | | | | ]; try done.
  destruct u as [ | | | | | | | | ww | | | ]; try done.
  move: evId => [Vid [evAt [evav evaw]]].
  rewrite EqVal_rfl.
  have VTy : Val (S RB) Δ (Core.tid A a a)[σ] Core.tuniv[σ] (wt_rfl_ty WT).
  { eapply st_tid_Val_edge;
      [ exact TA | exact Ta | exact Ta | exact STA | exact STa | exact STa
      | exact TS | exact TS' | exact CS | exact Fρ | exact VS | exact VS'
      | exact EVS | exact CΔ | exact evId0 | cbn; apply le_refl; done
      | cbn in Hrank |- *; lia ]. }
  have [valWit eqWit] :=
    STa ρ m Δ σ σ' TS TS' CS Fρ VS VS' EVS CΔ ww t (wt_rfl_wit WT) evR evAt.
  have VW : Val RB Δ a[σ] A[σ] (wt_rfl_wit WT)
    by (eapply valWit; cbn in Hrank |- *; lia).
  have EW : EqVal RB Δ a[σ] a[σ'] A[σ] (wt_rfl_wit WT)
    by (eapply eqWit; cbn in Hrank |- *; lia).
  have EWs : EqVal RB Δ a[σ'] a[σ] A[σ] (wt_rfl_wit WT)
    by (eapply EqVal_sym; [ cbn in Hrank |- *; lia | cbn in Hrank |- *; lia | exact EW ]).
  have VW' : Val RB Δ a[σ'] A[σ] (wt_rfl_wit WT) := EqVal_Val2 EW.
  split; [ eapply Val_ValTy; exact VTy | ].
  (* [ValId] of the unprimed side *)
  have IdM : ValId RB Δ (Core.rfl a[σ]) (Core.tid A a a)[σ] WT.
  { exists A[σ]. exists a[σ]. exists a[σ]. split; [ apply ms_refl | ].
    exists a[σ]. split; [ apply ms_refl | ].
    split; [ apply c_refl; exact TRs | ].
    split; [ apply c_refl; exact Tas | ].
    split; [ apply c_refl; exact Tas | ].
    split; [ exact VW | ].
    split; [ eapply Val_EqVal; exact VW | eapply Val_EqVal; exact VW ]. }
  (* ... and of the primed side, still at the *unprimed* type *)
  have IdN : ValId RB Δ (Core.rfl a[σ']) (Core.tid A a a)[σ] WT.
  { exists A[σ]. exists a[σ]. exists a[σ]. split; [ apply ms_refl | ].
    exists a[σ']. split; [ apply ms_refl | ].
    split; [ apply c_refl; exact TRs' | ].
    split; [ apply c_sym; exact convaa' | ].
    split; [ apply c_sym; exact convaa' | ].
    split; [ exact VW' | ].
    split; [ exact EWs | exact EWs ]. }
  split; [ exact IdM | ]. split; [ exact IdN | ].
  split; [ exact IdM | ]. split; [ exact IdN | ].
  exists a[σ]. exists a[σ']. split; [ apply ms_refl | ]. split; [ apply ms_refl | ].
  exists A[σ]. exists a[σ]. exists a[σ]. split; [ apply ms_refl | ].
  split; [ exact convaa' | exact EW ].
Qed.

Lemma st_rfl (A a : Tm n) :
  typing Γ A Core.tuniv ->
  typing Γ a A ->
  semantic_typing Γ A Core.tuniv ->
  semantic_typing Γ a A ->
(* ------------------------- *)
  semantic_typing Γ (Core.rfl a) (Core.tid A a a).
Proof.
  move=> TA Ta STA STa.
  move=> ρ m Δ σ σ' TS TS' CS Fρ VS VS' EVS CΔ u a0 WT evR evId.
  split.
  - eapply st_rfl_Val_edge; eassumption.
  - eapply st_rfl_EqVal_edge; eassumption.
Qed.

(** The [J] goal's type is a valid *type* at every code it evaluates to.

    One [Val]-only walk of [C]'s three application edges.  [motive_ty]'s final
    codomain is [tuniv], so the walk ends in a [ValTy].  All three arguments
    ([a], [b], [p]) are Γ-terms, so their [Val]s at the selection codes are
    just [STa]/[STb]/[STp] re-asked at those codes -- no transport needed, in
    contrast to the witness term of the [EqValTy] walk.

    This is the [ValTy] that [Val_app_transport] needs in order to carry the
    base branch's edge result from the edge's code onto the goal's code. *)
Lemma jcase_type_spine (A a b C p : Tm n)
  (TA : typing Γ A Core.tuniv) (Ta : typing Γ a A) (Tb : typing Γ b A)
  (TC : typing Γ C (motive_ty A)) (Tp : typing Γ p (Core.tid A a b))
  (STa : semantic_typing Γ a A) (STb : semantic_typing Γ b A)
  (STC : semantic_typing Γ C (motive_ty A))
  (STp : semantic_typing Γ p (Core.tid A a b))
  ρ m (Δ : Ctx m) (σ σ' : Sub n m)
  (TS : typing_subst Δ σ Γ) (TS' : typing_subst Δ σ' Γ) (CS : ConvSub Δ Γ σ σ')
  (Fρ : fits Γ ρ) (VS : ValSub Δ Γ σ ρ) (VS' : ValSub Δ Γ σ' ρ)
  (EVS : EqValSub Δ Γ σ σ' ρ) (CΔ : ctx Δ)
  (aT : elt) (hT : wt aT tuniv)
  (evT : EvalRel (Core.app (Core.app (Core.app C a) b) p) ρ aT) :
  forall k, max (rk aT) (rk tuniv) < k ->
    Val k Δ (Core.app (Core.app (Core.app C[σ] a[σ]) b[σ]) p[σ]) Core.tuniv hT.
Proof.
  move=> k Hk.
  have Vρ : valid_env ρ := fits_valid_env Fρ.
  have evU : EvalRel Core.tuniv ρ tuniv by (cbn; apply le_refl).
  have Tas : typing Δ a[σ] A[σ]
    by (eapply substitution_tm; [ exact Ta | exact TS | exact CΔ ]).
  have Tbs : typing Δ b[σ] A[σ]
    by (eapply substitution_tm; [ exact Tb | exact TS | exact CΔ ]).
  have Tps : typing Δ p[σ] (Core.tid A[σ] a[σ] b[σ]).
  { move: (substitution_tm _ _ _ _ _ Tp TS CΔ) => hh. cbn in hh. exact hh. }
  destruct (is_bot aT) eqn:HaT.
  { (* the goal type takes [bot]: [ValTy] is trivial there.  Note the *type*
       code here is [tuniv], so this is [Val_Bot] on the element code, not
       [Val_isbot]. *)
    have E : aT = bot by (apply is_bot_eq; rewrite HaT).
    move: hT. rewrite E => hT'. apply Val_Bot. }
  (* ---- unfold the goal type's own spine, to choose the codes ---- *)
  have evT0 := evT. cbn [EvalRel] in evT0. rewrite HaT in evT0.
  move: evT0 => [w1 [ev21 evp1]].
  have NB1 : is_bot (w1 ↦ aT) = false by (rewrite /singleton HaT).
  rewrite NB1 in ev21. move: ev21 => [w2 [ev32 evb2]].
  have NB2 : is_bot (w2 ↦ (w1 ↦ aT)) = false by (rewrite /singleton NB1).
  rewrite NB2 in ev32. move: ev32 => [w3 [evC3 eva3]].
  (* ---- level 1: the motive itself ---- *)
  have ITc : InvTyped Γ C (motive_ty A) ρ := typing_EvalRel TC Fρ.
  have [vc [ac [WTc [LEc [evCbig evMot]]]]] := ITc _ evC3.
  have [g3 [b3 [f3 [Evc [Eac LE2]]]]] := spine_descend NB2 LEc WTc.
  subst vc. subst ac.
  have evMotC := evMot. rewrite /motive_ty in evMotC. cbn [EvalRel] in evMotC.
  move: evMotC => [Vb3 [Vf3 [evA_b3 [a3' [evA_b3' EB3fun]]]]].
  have Vg3 : valid_fun g3 := proj1 (andb_prop _ _ (wt_valid_tm WTc)).
  have Vw3 : valid w3 := EvalRel_valid eva3.
  have [u3 [v3 [Sel3 [Le_u3 Eq_v3]]]] := selectionBelow Vg3 Vw3.
  have [WTu3 WTv3] : wt u3 b3 /\ wt v3 (app f3 u3).
  { eapply wt_Selection_cod;
      [ exact (wt_abs_ty WTc) | exact (wt_abs_inv1 WTc)
      | move=> ui vi Hin; exact (wt_abs_inv2 WTc Hin erefl)
      | exact Vg3 | exact Sel3 ]. }
  have Vu3 : valid u3 := wt_valid_tm WTu3.
  (* fuel: above the motive's own code and the goal's code.  Every later code
     is a sub-value of [abs g3] / [tpi b3 f3], so one additive bound serves. *)
  pose RBc := S (rk (abs g3) + rk (tpi b3 f3) + rk aT).
  have Rg3 : rk_fun g3 < rk (abs g3) by (cbn; lia).
  have Rb3 : rk b3 < rk (tpi b3 f3) by (cbn; lia).
  have Rf3 : rk_fun f3 < rk (tpi b3 f3) by (cbn; lia).
  have Ru3 : rk u3 <= rk_fun g3 := rk_Selection_key Sel3.
  have Rv3 : rk v3 <= rk_fun g3 := rk_Selection_val Sel3.
  have Rcod3 : rk (app f3 u3) <= rk_fun f3 := rk_app f3 u3.
  have [valC _] :=
    STC ρ m Δ σ σ' TS TS' CS Fρ VS VS' EVS CΔ (abs g3) (tpi b3 f3) WTc evCbig evMot.
  have eva_u3 : EvalRel a ρ u3
    by (eapply EvalRel_down; [ exact Vρ | exact Vu3 | exact eva3 | exact Le_u3 ]).
  have [valA1 _] :=
    STa ρ m Δ σ σ' TS TS' CS Fρ VS VS' EVS CΔ u3 b3 WTu3 eva_u3 evA_b3.
  have HRmot : HeadRed ((motive_ty A)[σ])
      (Core.tpi A[σ] (Core.tpi ((A[σ])⟨↑⟩)
         (Core.tpi (Core.tid (((A[σ])⟨↑⟩)⟨↑⟩) (Core.var (shift var_zero))
                      (Core.var var_zero)) Core.tuniv)))
    by (rewrite subst_motive_ty; apply ms_refl).
  have V1 : Val (S (S RBc)) Δ (Core.app C[σ] a[σ])
              (Core.tpi A[σ] (Core.tpi (Core.tid ((A[σ])⟨↑⟩) ((a[σ])⟨↑⟩)
                                 (Core.var var_zero)) Core.tuniv))
              (wt_Selection_abs WTc Sel3).
  { rewrite -motive_cod1_subst.
    eapply spine_Val;
      [ exact HRmot
      | exact (valC (S (S (S RBc))) ltac:(unfold RBc; lia))
      | exact Tas
      | exact (valA1 (S (S RBc)) ltac:(unfold RBc; lia)) ]. }
  (* ---- level 2 ---- *)
  rewrite Eq_v3 in LE2.
  have [g2 [b2 [f2 [Ev3 [Ecod2 LE1']]]]] := spine_descend NB1 LE2 WTv3.
  (* [Eq_v3] also mentions [v3], and [subst] would orient through it; it has
     already done its job in [LE2] *)
  clear Eq_v3. subst v3.
  have NBcod2 : ~ is_bot (app f3 u3) by (rewrite Ecod2; done).
  have Rcod2 : rk (tpi b2 f2) <= rk_fun f3 by (rewrite -Ecod2; exact Rcod3).
  (* the level-2 type also takes the edge's codomain code, which is where the
     level-2 domain code [b2] comes from *)
  have evCod2 : EvalRel
      (Core.tpi A (Core.tpi (Core.tid (A⟨↑⟩) (a⟨↑⟩) (Core.var var_zero))
                     Core.tuniv)) ρ (app f3 u3).
  { rewrite -motive_cod1_subst.
    eapply EvalRel_Pi_app_type;
      [ exact evMot | exact Vρ | exact Vu3 | reflexivity | exact NBcod2
      | exact eva_u3 ]. }
  rewrite Ecod2 in evCod2. have evCod2C := evCod2.
  cbn [EvalRel] in evCod2.
  move: evCod2 => [Vb2 [Vf2 [evA_b2 [a2' [evA_b2' EB2fun]]]]].
  (* [Val] matches on the type code, so rewrite it *before* using [V1]: the code
     occurs only in the type of the [wt] index, hence the generalise-then-rewrite
     dance (see [spine_descend]'s comment). *)
  move: V1. move: (wt_Selection_abs WTc Sel3). rewrite Ecod2.
  move=> hC2 V1'.
  have Vg2 : valid_fun g2 := proj1 (andb_prop _ _ (wt_valid_tm hC2)).
  have Vw2 : valid w2 := EvalRel_valid evb2.
  have [u2 [v2 [Sel2 [Le_u2 Eq_v2]]]] := selectionBelow Vg2 Vw2.
  have [WTu2 WTv2] : wt u2 b2 /\ wt v2 (app f2 u2).
  { eapply wt_Selection_cod;
      [ exact (wt_abs_ty hC2) | exact (wt_abs_inv1 hC2)
      | move=> ui vi Hin; exact (wt_abs_inv2 hC2 Hin erefl)
      | exact Vg2 | exact Sel2 ]. }
  have Vu2 : valid u2 := wt_valid_tm WTu2.
  have Rg2 : rk_fun g2 < rk (abs g2) by (cbn; lia).
  have Rb2 : rk b2 < rk (tpi b2 f2) by (cbn; lia).
  have Rf2 : rk_fun f2 < rk (tpi b2 f2) by (cbn; lia).
  have Ru2 : rk u2 <= rk_fun g2 := rk_Selection_key Sel2.
  have Rv2 : rk v2 <= rk_fun g2 := rk_Selection_val Sel2.
  have Rcod2b : rk (app f2 u2) <= rk_fun f2 := rk_app f2 u2.
  have evb_u2 : EvalRel b ρ u2
    by (eapply EvalRel_down; [ exact Vρ | exact Vu2 | exact evb2 | exact Le_u2 ]).
  have [valB1 _] :=
    STb ρ m Δ σ σ' TS TS' CS Fρ VS VS' EVS CΔ u2 b2 WTu2 evb_u2 evA_b2.
  have V2 : Val (S RBc) Δ (Core.app (Core.app C[σ] a[σ]) b[σ])
              (Core.tpi (Core.tid A[σ] a[σ] b[σ]) Core.tuniv)
              (wt_Selection_abs hC2 Sel2).
  { rewrite -motive_cod2_subst.
    eapply spine_Val;
      [ apply ms_refl | exact V1' | exact Tbs
      | exact (valB1 (S RBc) ltac:(unfold RBc; lia)) ]. }
  (* ---- level 3: the proof argument ---- *)
  rewrite Eq_v2 in LE1'.
  have [g1 [b1 [f1 [Ev2 [Ecod1 LE0]]]]] := spine_descend HaT LE1' WTv2.
  clear Eq_v2. subst v2.
  have NBcod1 : ~ is_bot (app f2 u2) by (rewrite Ecod1; done).
  have Rcod1 : rk (tpi b1 f1) <= rk_fun f2 by (rewrite -Ecod1; exact Rcod2b).
  have evCod1 : EvalRel (Core.tpi (Core.tid A a b) Core.tuniv) ρ (app f2 u2).
  { rewrite -motive_cod2_subst.
    eapply EvalRel_Pi_app_type;
      [ exact evCod2C | exact Vρ | exact Vu2 | reflexivity | exact NBcod1
      | exact evb_u2 ]. }
  rewrite Ecod1 in evCod1. have evCod1C := evCod1.
  cbn [EvalRel] in evCod1.
  move: evCod1 => [Vb1 [Vf1 [evId_b1 [a1' [evId_b1' EB1fun]]]]].
  move: V2. move: (wt_Selection_abs hC2 Sel2). rewrite Ecod1.
  move=> hC1 V2'.
  have Vg1 : valid_fun g1 := proj1 (andb_prop _ _ (wt_valid_tm hC1)).
  have Vw1 : valid w1 := EvalRel_valid evp1.
  have [u1 [v1 [Sel1 [Le_u1 Eq_v1]]]] := selectionBelow Vg1 Vw1.
  have [WTu1 WTv1] : wt u1 b1 /\ wt v1 (app f1 u1).
  { eapply wt_Selection_cod;
      [ exact (wt_abs_ty hC1) | exact (wt_abs_inv1 hC1)
      | move=> ui vi Hin; exact (wt_abs_inv2 hC1 Hin erefl)
      | exact Vg1 | exact Sel1 ]. }
  have Vu1 : valid u1 := wt_valid_tm WTu1.
  have Rg1 : rk_fun g1 < rk (abs g1) by (cbn; lia).
  have Rb1 : rk b1 < rk (tpi b1 f1) by (cbn; lia).
  have Rf1 : rk_fun f1 < rk (tpi b1 f1) by (cbn; lia).
  have Ru1 : rk u1 <= rk_fun g1 := rk_Selection_key Sel1.
  have Rv1 : rk v1 <= rk_fun g1 := rk_Selection_val Sel1.
  have Rcod1b : rk (app f1 u1) <= rk_fun f1 := rk_app f1 u1.
  have evp_u1 : EvalRel p ρ u1
    by (eapply EvalRel_down; [ exact Vρ | exact Vu1 | exact evp1 | exact Le_u1 ]).
  have [valP1 _] :=
    STp ρ m Δ σ σ' TS TS' CS Fρ VS VS' EVS CΔ u1 b1 WTu1 evp_u1 evId_b1.
  (* state the codomain in substituted form: [?B0[?N..] =?= Core.tuniv] is a
     higher-order problem [eapply] will not solve, but matching against
     [Core.tuniv[p[σ]..]] is first-order *)
  have V3 : Val RBc Δ (Core.app (Core.app (Core.app C[σ] a[σ]) b[σ]) p[σ])
              ((Core.tuniv : Tm (S m))[(p[σ])..]) (wt_Selection_abs hC1 Sel1).
  { eapply spine_Val;
      [ apply ms_refl | exact V2' | exact Tps
      | exact (valP1 RBc ltac:(unfold RBc; lia)) ]. }
  (* ---- land on the requested code ----
     [motive_ty]'s final codomain is [tuniv], so the last codomain code sits
     *below* [tuniv]; the [ValTy] obligation of the transport is therefore the
     [tuniv] branch of [ValTy], i.e. [True]. *)
  have evUf : EvalRel Core.tuniv ρ (app f1 u1).
  { destruct (is_bot (app f1 u1)) eqn:Hbf.
    - have E : app f1 u1 = bot by (apply is_bot_eq; rewrite Hbf).
      rewrite E. apply EvalRel_bot.
    - (* again: state the codomain in substituted form, so the match is
         first-order *)
      have hh : EvalRel ((Core.tuniv : Tm (S n))[p..]) ρ (app f1 u1).
      { eapply EvalRel_Pi_app_type;
          [ exact evCod1C | exact Vρ | exact Vu1 | reflexivity
          | (rewrite Hbf; done) | exact evp_u1 ]. }
      exact hh. }
  have Lf1 : le (app f1 u1) tuniv by (move: evUf; cbn; done).
  have LEaTv1 : le aT v1 by (rewrite Eq_v1 in LE0; exact LE0).
  have hUtu : wt tuniv tuniv := wt_tuniv.
  have Waf1 : wt (app f1 u1) tuniv := wt_ty_tuniv WTv1.
  have VTU : Val RBc Δ Core.tuniv Core.tuniv hUtu by (unfold RBc; exact I).
  apply (Val_fuel_any (k := RBc) (k' := k));
    [ unfold RBc; lia | (cbn; unfold RBc; lia) | lia | (cbn in Hk |- *; lia) | ].
  (* [Val_transport_up]'s [h']/[hUa] are not addressable by name (the latter
     does not occur in its statement), so go through [@] *)
  eapply (@Val_transport_up _ Δ
            (Core.app (Core.app (Core.app C[σ] a[σ]) b[σ]) p[σ]) Core.tuniv
            v1 aT (app f1 u1) tuniv
            (wt_Selection_abs hC1 Sel1) hT Waf1 hUtu);
    [ exact LEaTv1 | exact Lf1 | exact VTU | exact V3 ].
Qed.

(** [JTypeEq] (Agda ID's [JMotive] / [JTypeEq]): the motive applied to the
    *witness* and the motive applied to the *endpoints* are reducibly equal
    types.

    One walk of [C[σ]]'s three application edges.  Each level composes a
    function-step ([spine_EqVal_fun], varying the function) with an
    argument-step ([spine_EqVal_arg], varying the argument) via [EqVal_trans].
    The two steps land at *different* types -- the left spine instantiates the
    motive at the witness, the right spine at the endpoints -- and the
    reconciling [EqValTy] is the [PiEdgeEqTy] component of the level above,
    which is exactly what that level's [PiEdgeEq] produced.

    Each level therefore needs *two* selections: one in the value code's table
    [g_i] (for [PiApp*]) and one in the type code's table [f_i] (for
    [PiEdge*]).  [selectionBelow f_i u_i] lines them up, since it returns
    [app f_i u_i = v]: the type-level selection's value is exactly the
    element-level codomain code.

    The spine codes are supplied by the caller (from
    [EvalRel_base_cod_spine_codes]) *together with the bounds placing them
    below the witness* -- the witness's reducible equalities to the endpoints
    live at the witness's own code and can only be restricted downwards. *)
Lemma jcase_motive_EqVal (A a b C p : Tm n)
  (TA : typing Γ A Core.tuniv) (Ta : typing Γ a A) (Tb : typing Γ b A)
  (TC : typing Γ C (motive_ty A)) (Tp : typing Γ p (Core.tid A a b))
  (STA : semantic_typing Γ A Core.tuniv)
  (STa : semantic_typing Γ a A) (STb : semantic_typing Γ b A)
  (STC : semantic_typing Γ C (motive_ty A))
  (STp : semantic_typing Γ p (Core.tid A a b))
  ρ m (Δ : Ctx m) (σ σ' : Sub n m)
  (TS : typing_subst Δ σ Γ) (TS' : typing_subst Δ σ' Γ) (CS : ConvSub Δ Γ σ σ')
  (Fρ : fits Γ ρ) (VS : ValSub Δ Γ σ ρ) (VS' : ValSub Δ Γ σ' ρ)
  (EVS : EqValSub Δ Γ σ σ' ρ) (CΔ : ctx Δ)
  (* the witness package, from [STp] at the proof's own code *)
  wmax tc upc vpc (WTp : wt (rfl wmax) (tid tc upc vpc))
  (evPbig : EvalRel p ρ (rfl wmax))
  (evA_tc : EvalRel A ρ tc)
  (P0 : Tm m)
  (HRp : HeadRed p[σ] (Core.rfl P0))
  (cvPa : conv Δ P0 a[σ] A[σ]) (cvPb : conv Δ P0 b[σ] A[σ])
  (cvPp : conv Δ p[σ] (Core.rfl P0) (Core.tid A[σ] a[σ] b[σ]))
  (IdPk : forall k, max (rk (rfl wmax)) (rk (tid tc upc vpc)) < k ->
      Val k Δ P0 A[σ] (wt_rfl_wit WTp)
      /\ EqVal k Δ P0 a[σ] A[σ] (wt_rfl_wit WTp)
      /\ EqVal k Δ P0 b[σ] A[σ] (wt_rfl_wit WTp))
  (* the spine codes at the target code [aT], with their bounds *)
  (aT : elt) (hAf : wt aT tuniv) (HaT : is_bot aT = false)
  w1 w2 w3
  (evC3 : EvalRel C ρ (w3 ↦ (w2 ↦ (w1 ↦ aT))))
  (L3 : le w3 wmax) (L2 : le w2 wmax) (L1 : le w1 (rfl wmax))
  (eva3 : EvalRel a ρ w3) (evb2 : EvalRel b ρ w2) (evp1 : EvalRel p ρ w1) :
  forall k, max (rk aT) (rk tuniv) < k ->
    EqVal k Δ (Core.app (Core.app (Core.app C[σ] P0) P0) (Core.rfl P0))
              (Core.app (Core.app (Core.app C[σ] a[σ]) b[σ]) p[σ])
              Core.tuniv hAf.
Proof.
  move=> k Hk.
  have Vρ : valid_env ρ := fits_valid_env Fρ.
  have evU : EvalRel Core.tuniv ρ tuniv by (cbn; apply le_refl).
  have Vwmax : valid wmax by (move: (EvalRel_valid evPbig); cbn; done).
  have Wt_tc : wt tc tuniv := wt_ty_tuniv (wt_rfl_wit WTp).
  have TAs : typing Δ A[σ] Core.tuniv
    by (move: (substitution_tm _ _ _ _ _ TA TS CΔ) => hh; cbn in hh; exact hh).
  have Tas : typing Δ a[σ] A[σ]
    by (eapply substitution_tm; [ exact Ta | exact TS | exact CΔ ]).
  have Tbs : typing Δ b[σ] A[σ]
    by (eapply substitution_tm; [ exact Tb | exact TS | exact CΔ ]).
  have Tps : typing Δ p[σ] (Core.tid A[σ] a[σ] b[σ]).
  { move: (substitution_tm _ _ _ _ _ Tp TS CΔ) => hh. cbn in hh. exact hh. }
  have TP0 : typing Δ P0 A[σ] := proj1 (conv_typing cvPa).
  (* ---- the witness's data, restricted to any code below [wmax] ---- *)
  have transW : forall c0 u0 (hu : wt u0 c0) kk,
      le u0 wmax -> EvalRel A ρ c0 ->
      max (rk (lub c0 tc)) (rk tuniv) < kk ->
      max (rk (rfl wmax)) (rk (tid tc upc vpc)) < kk ->
      Val kk Δ P0 A[σ] hu
      /\ EqVal kk Δ P0 a[σ] A[σ] hu
      /\ EqVal kk Δ P0 b[σ] A[σ] hu.
  { move=> c0 u0 hu kk Lu evc Hk1 Hk2.
    have Wc0 : wt c0 tuniv := wt_ty_tuniv hu.
    have Cc : compatible c0 tc
      by (eapply EvalRel_compatible; [ exact Vρ | exact evc | exact evA_tc ]).
    have hUl : wt (lub c0 tc) tuniv := wt_lub Wc0 Cc Wt_tc.
    have evl : EvalRel A ρ (lub c0 tc)
      := proj2 (EvalRel_compatible_lub Vρ evc evA_tc) _ erefl.
    have [valAl _] :=
      STA ρ m Δ σ σ' TS TS' CS Fρ VS VS' EVS CΔ (lub c0 tc) tuniv hUl evl evU.
    have [VP [EA EB]] := IdPk kk Hk2.
    split.
    { eapply (@Val_app_transport _ Δ P0 A[σ] u0 wmax c0 tc
                (wt_rfl_wit WTp) hu hUl);
        [ exact Cc | exact Lu | exact (valAl kk Hk1) | exact VP ]. }
    split.
    { eapply (@EqVal_app_transport _ Δ P0 a[σ] A[σ] u0 wmax c0 tc
                (wt_rfl_wit WTp) hu hUl);
        [ exact Cc | exact Lu | exact (valAl kk Hk1) | exact EA ]. }
    { eapply (@EqVal_app_transport _ Δ P0 b[σ] A[σ] u0 wmax c0 tc
                (wt_rfl_wit WTp) hu hUl);
        [ exact Cc | exact Lu | exact (valAl kk Hk1) | exact EB ]. } }
  (* ---- level 1: the motive itself ---- *)
  have NBaT1 : is_bot (w1 ↦ aT) = false by (rewrite /singleton HaT).
  have NBaT2 : is_bot (w2 ↦ (w1 ↦ aT)) = false by (rewrite /singleton NBaT1).
  have ITc : InvTyped Γ C (motive_ty A) ρ := typing_EvalRel TC Fρ.
  have [vc [ac [WTc [LEc [evCbig evMot]]]]] := ITc _ evC3.
  have [g3 [b3 [f3 [Evc [Eac LEn2]]]]] := spine_descend NBaT2 LEc WTc.
  subst vc. subst ac.
  have evMotC := evMot. rewrite /motive_ty in evMotC. cbn [EvalRel] in evMotC.
  move: evMotC => [Vb3 [Vf3 [evA_b3 [a3' [evA_b3' EB3fun]]]]].
  have Vg3 : valid_fun g3 := proj1 (andb_prop _ _ (wt_valid_tm WTc)).
  have Vw3 : valid w3 := EvalRel_valid eva3.
  (* the element-level selection, in the value code's table [g3] *)
  have [u3 [v3 [Sel3 [Le_u3 Eq_v3]]]] := selectionBelow Vg3 Vw3.
  have [WTu3 WTv3] : wt u3 b3 /\ wt v3 (app f3 u3).
  { eapply wt_Selection_cod;
      [ exact (wt_abs_ty WTc) | exact (wt_abs_inv1 WTc)
      | move=> ui vi Hin; exact (wt_abs_inv2 WTc Hin erefl)
      | exact Vg3 | exact Sel3 ]. }
  have Vu3 : valid u3 := wt_valid_tm WTu3.
  (* ... and the type-level selection, in the type code's table [f3].  Its
     value is [app f3 u3], i.e. exactly the element-level codomain code, which
     is what lines the two up. *)
  have [uf3 [vf3 [SelF3 [Le_uf3 Eq_vf3]]]] := selectionBelow Vf3 Vu3.
  subst vf3.
  have WTuf3 : wt uf3 b3
    by (eapply wt_Selection;
        [ exact (wt_tpi_dom (wt_abs_ty WTc)) | exact Vf3
        | exact (wt_tpi_keys (wt_abs_ty WTc)) | exact SelF3 ]).
  have Vuf3 : valid uf3 := wt_valid_tm WTuf3.
  (* fuel: three levels consume three units, so start at [S (S (S RB0))] *)
  pose RB0 := S (rk (abs g3) + rk (tpi b3 f3) + rk aT
                 + rk (rfl wmax) + rk (tid tc upc vpc)).
  have Rg3 : rk_fun g3 < rk (abs g3) by (cbn; lia).
  have Rb3 : rk b3 < rk (tpi b3 f3) by (cbn; lia).
  have Rf3 : rk_fun f3 < rk (tpi b3 f3) by (cbn; lia).
  have Rtc : rk tc < rk (tid tc upc vpc) by (cbn; lia).
  have Rtu : rk tuniv = 1 by reflexivity.
  have Ru3 : rk u3 <= rk_fun g3 := rk_Selection_key Sel3.
  have Rv3 : rk v3 <= rk_fun g3 := rk_Selection_val Sel3.
  have Ruf3 : rk uf3 <= rk_fun f3 := rk_Selection_key SelF3.
  have Rcod3 : rk (app f3 u3) <= rk_fun f3 := rk_app f3 u3.
  have Rlub3 : rk (lub b3 tc) <= max (rk b3) (rk tc) := rk_lub b3 tc.
  have Lu3 : le u3 wmax
    by (eapply (@le_trans u3 w3 wmax);
        [ exact Vu3 | exact Vw3 | exact Vwmax | exact Le_u3 | exact L3 ]).
  have Luf3 : le uf3 wmax
    by (eapply (@le_trans uf3 u3 wmax);
        [ exact Vuf3 | exact Vu3 | exact Vwmax | exact Le_uf3 | exact Lu3 ]).
  have [valC _] :=
    STC ρ m Δ σ σ' TS TS' CS Fρ VS VS' EVS CΔ
        (abs g3) (tpi b3 f3) WTc evCbig evMot.
  have VCk := valC (S (S (S (S RB0)))) ltac:(unfold RB0; lia).
  have eva_u3 : EvalRel a ρ u3
    by (eapply EvalRel_down; [ exact Vρ | exact Vu3 | exact eva3 | exact Le_u3 ]).
  have [valA3 _] :=
    STa ρ m Δ σ σ' TS TS' CS Fρ VS VS' EVS CΔ u3 b3 WTu3 eva_u3 evA_b3.
  have HRmot : HeadRed ((motive_ty A)[σ])
      (Core.tpi A[σ] (Core.tpi ((A[σ])⟨↑⟩)
         (Core.tpi (Core.tid (((A[σ])⟨↑⟩)⟨↑⟩) (Core.var (shift var_zero))
                      (Core.var var_zero)) Core.tuniv)))
    by (rewrite subst_motive_ty; apply ms_refl).
  (* the right spine, level 1 *)
  have V1R : Val (S (S (S RB0))) Δ (Core.app C[σ] a[σ])
              (Core.tpi A[σ] (Core.tpi (Core.tid ((A[σ])⟨↑⟩) ((a[σ])⟨↑⟩)
                                 (Core.var var_zero)) Core.tuniv))
              (wt_Selection_abs WTc Sel3).
  { rewrite -motive_cod1_subst.
    eapply spine_Val;
      [ exact HRmot | exact VCk | exact Tas
      | exact (valA3 (S (S (S RB0))) ltac:(unfold RB0; lia)) ]. }
  (* the witness's data at the two selection keys *)
  have [_ [EqA3 _]] :=
    transW b3 u3 WTu3 (S (S (S RB0))) Lu3 evA_b3
      ltac:(unfold RB0; lia) ltac:(unfold RB0; lia).
  have [VPf3 [EqAf3 _]] :=
    transW b3 uf3 WTuf3 (S (S (S RB0))) Luf3 evA_b3
      ltac:(unfold RB0; lia) ltac:(unfold RB0; lia).
  (* level 1's [EqVal]: the function is the same on both sides, so this is a
     single argument-step, with no transport to compose *)
  have E1 : EqVal (S (S (S RB0))) Δ (Core.app C[σ] P0) (Core.app C[σ] a[σ])
              (Core.tpi A[σ] (Core.tpi (Core.tid ((A[σ])⟨↑⟩) (P0⟨↑⟩)
                                 (Core.var var_zero)) Core.tuniv))
              (wt_Selection_abs WTc Sel3).
  { rewrite -motive_cod1_subst.
    eapply spine_EqVal_arg;
      [ exact HRmot | exact VCk | exact cvPa | exact EqA3 ]. }
  (* ... and the [EqValTy] the *next* level will need, straight off the motive
     type's own [PiEdgeEq] *)
  have VTmot : ValTy (S (S (S RB0))) Δ ((motive_ty A)[σ]) (wt_abs_ty WTc)
    by (move: VCk; rewrite Val_abs; move=> [hh _]; exact hh).
  move: VTmot =>
    [A1 [B1 [HR1 [TA1 [TB1 [Vpi3 [VdomA [pev3 pee3]]]]]]]].
  have [EA1 EB1] := HeadRed_tpi_det HR1 HRmot. subst A1 B1.
  have ETy1 : EqValTy (S (S RB0)) Δ
      ((Core.tpi ((A[σ])⟨↑⟩)
          (Core.tpi (Core.tid (((A[σ])⟨↑⟩)⟨↑⟩) (Core.var (shift var_zero))
                       (Core.var var_zero)) Core.tuniv))[P0..])
      ((Core.tpi ((A[σ])⟨↑⟩)
          (Core.tpi (Core.tid (((A[σ])⟨↑⟩)⟨↑⟩) (Core.var (shift var_zero))
                       (Core.var var_zero)) Core.tuniv))[(a[σ])..])
      (wt_Selection_codU (wt_abs_ty WTc) SelF3).
  { have hh := pee3 uf3 (app f3 u3) SelF3 WTuf3 P0 a[σ] cvPa EqAf3.
    rewrite EqVal_tuniv in hh. exact (proj2 (proj2 hh)). }
  (* ---- level 2 ---- *)
  rewrite Eq_v3 in LEn2.
  have [g2 [b2 [f2 [Ev3 [Ecod2 LEn1]]]]] := spine_descend NBaT1 LEn2 WTv3.
  clear Eq_v3. subst v3.
  have NBcod2 : ~ is_bot (app f3 u3) by (rewrite Ecod2; done).
  have Rcod2t : rk (tpi b2 f2) <= rk_fun f3 by (rewrite -Ecod2; exact Rcod3).
  have evCod2 : EvalRel
      (Core.tpi A (Core.tpi (Core.tid (A⟨↑⟩) (a⟨↑⟩) (Core.var var_zero))
                     Core.tuniv)) ρ (app f3 u3).
  { rewrite -motive_cod1_subst.
    eapply EvalRel_Pi_app_type;
      [ exact evMot | exact Vρ | exact Vu3 | reflexivity | exact NBcod2
      | exact eva_u3 ]. }
  rewrite Ecod2 in evCod2. have evCod2C := evCod2.
  cbn [EvalRel] in evCod2.
  move: evCod2 => [Vb2 [Vf2 [evA_b2 [a2' [evA_b2' EB2fun]]]]].
  (* rewrite the level-2 codes before using anything indexed by them *)
  move: ETy1. move: E1. move: V1R.
  move: (wt_Selection_codU (wt_abs_ty WTc) SelF3).
  move: (wt_Selection_abs WTc Sel3).
  rewrite Ecod2.
  move=> hC2 hCod2 V1R' E1' ETy1'.
  have Vg2 : valid_fun g2 := proj1 (andb_prop _ _ (wt_valid_tm hC2)).
  have Vw2 : valid w2 := EvalRel_valid evb2.
  have [u2 [v2 [Sel2 [Le_u2 Eq_v2]]]] := selectionBelow Vg2 Vw2.
  have [WTu2 WTv2] : wt u2 b2 /\ wt v2 (app f2 u2).
  { eapply wt_Selection_cod;
      [ exact (wt_abs_ty hC2) | exact (wt_abs_inv1 hC2)
      | move=> ui vi Hin; exact (wt_abs_inv2 hC2 Hin erefl)
      | exact Vg2 | exact Sel2 ]. }
  have Vu2 : valid u2 := wt_valid_tm WTu2.
  have [uf2 [vf2 [SelF2 [Le_uf2 Eq_vf2]]]] := selectionBelow Vf2 Vu2.
  subst vf2.
  have WTuf2 : wt uf2 b2
    by (eapply wt_Selection;
        [ exact (wt_tpi_dom hCod2) | exact Vf2
        | exact (wt_tpi_keys hCod2) | exact SelF2 ]).
  have Vuf2 : valid uf2 := wt_valid_tm WTuf2.
  have Rg2 : rk_fun g2 < rk (abs g2) by (cbn; lia).
  have Rb2 : rk b2 < rk (tpi b2 f2) by (cbn; lia).
  have Rf2 : rk_fun f2 < rk (tpi b2 f2) by (cbn; lia).
  have Ru2 : rk u2 <= rk_fun g2 := rk_Selection_key Sel2.
  have Rv2 : rk v2 <= rk_fun g2 := rk_Selection_val Sel2.
  have Ruf2 : rk uf2 <= rk_fun f2 := rk_Selection_key SelF2.
  have Rcod2b : rk (app f2 u2) <= rk_fun f2 := rk_app f2 u2.
  have Rlub2 : rk (lub b2 tc) <= max (rk b2) (rk tc) := rk_lub b2 tc.
  have Lu2 : le u2 wmax
    by (eapply (@le_trans u2 w2 wmax);
        [ exact Vu2 | exact Vw2 | exact Vwmax | exact Le_u2 | exact L2 ]).
  have Luf2 : le uf2 wmax
    by (eapply (@le_trans uf2 u2 wmax);
        [ exact Vuf2 | exact Vu2 | exact Vwmax | exact Le_uf2 | exact Lu2 ]).
  have evb_u2 : EvalRel b ρ u2
    by (eapply EvalRel_down; [ exact Vρ | exact Vu2 | exact evb2 | exact Le_u2 ]).
  have [valB2 _] :=
    STb ρ m Δ σ σ' TS TS' CS Fρ VS VS' EVS CΔ u2 b2 WTu2 evb_u2 evA_b2.
  have [VP2 [_ EqB2]] :=
    transW b2 u2 WTu2 (S (S RB0)) Lu2 evA_b2
      ltac:(unfold RB0; lia) ltac:(unfold RB0; lia).
  have [VPf2 [EqA2f EqB2f]] :=
    transW b2 uf2 WTuf2 (S (S RB0)) Luf2 evA_b2
      ltac:(unfold RB0; lia) ltac:(unfold RB0; lia).
  (* the right spine, level 2 *)
  have V2R : Val (S (S RB0)) Δ (Core.app (Core.app C[σ] a[σ]) b[σ])
              (Core.tpi (Core.tid A[σ] a[σ] b[σ]) Core.tuniv)
              (wt_Selection_abs hC2 Sel2).
  { rewrite -motive_cod2_subst.
    eapply spine_Val;
      [ apply ms_refl | exact V1R' | exact Tbs
      | exact (valB2 (S (S RB0)) ltac:(unfold RB0; lia)) ]. }
  (* the function-step and the argument-step ... *)
  have E2a : EqVal (S (S RB0)) Δ (Core.app (Core.app C[σ] P0) P0)
               (Core.app (Core.app C[σ] a[σ]) P0)
               (Core.tpi (Core.tid A[σ] P0 P0) Core.tuniv)
               (wt_Selection_abs hC2 Sel2).
  { rewrite -motive_cod2_subst.
    eapply spine_EqVal_fun;
      [ apply ms_refl | exact E1' | exact TP0 | exact VP2 ]. }
  have E2b : EqVal (S (S RB0)) Δ (Core.app (Core.app C[σ] a[σ]) P0)
               (Core.app (Core.app C[σ] a[σ]) b[σ])
               (Core.tpi (Core.tid A[σ] a[σ] P0) Core.tuniv)
               (wt_Selection_abs hC2 Sel2).
  { rewrite -motive_cod2_subst.
    eapply spine_EqVal_arg;
      [ apply ms_refl | exact V1R' | exact cvPb | exact EqB2 ]. }
  (* ... land at different types.  Both are retargeted all the way to the
     *right* spine's type [tpi (tid A[σ] a[σ] b[σ]) tuniv]: that is the only
     one whose [ValTy] is available at the level-3 domain code, since the
     code's endpoints approximate [a] and [b] and the witness's own data
     cannot reach the [b] one.

     Two reconciling [EqValTy]s are needed.  Varying the *first* endpoint is
     [PiEdgeEqTy] of [ETy1] (the level above's type equality); varying the
     *second* is [PiEdgeEq] of the right level-1 type's own [ValTy].  Note the
     fuel: [PiEdge*] inside [ValTy k] / [EqValTy k] yields a [k]-level
     [EqVal], and turning that back into an [EqValTy] costs a unit, so each
     result is raised with [EqVal_fuel_any] first. *)
  rewrite !motive_cod1_subst in ETy1'.
  move: ETy1' =>
    [VTX [VTY [AX [BX [HRX [AY [BY [HRY [cAXY [cBXY [Vpi2 [EdomXY peety]]]]]]]]]]]].
  have [EAX EBX] := HeadRed_tpi_eq HRX. subst AX BX.
  have [EAY EBY] := HeadRed_tpi_eq HRY. subst AY BY.
  have VT1R : ValTy (S (S RB0)) Δ
      (Core.tpi A[σ] (Core.tpi (Core.tid ((A[σ])⟨↑⟩) ((a[σ])⟨↑⟩)
                         (Core.var var_zero)) Core.tuniv)) (wt_abs_ty hC2)
    by (move: V1R'; rewrite Val_abs; move=> [hh _]; exact hh).
  move: VT1R => [AR [BR [HRR [TAR [TBR [VpiR [VdomR [pevR peeR]]]]]]]].
  have [EAR EBR] := HeadRed_tpi_eq HRR. subst AR BR.
  have cvTy2 : conv Δ (Core.tpi (Core.tid A[σ] P0 P0) Core.tuniv)
                      (Core.tpi (Core.tid A[σ] a[σ] P0) Core.tuniv) Core.tuniv
    by (eapply motive_cod2_inst_conv;
        [ exact TAs | exact TP0 | exact Tas | exact TP0 | exact cvPa ]).
  have cvTy3 : conv Δ (Core.tpi (Core.tid A[σ] a[σ] P0) Core.tuniv)
                      (Core.tpi (Core.tid A[σ] a[σ] b[σ]) Core.tuniv) Core.tuniv
    by (eapply motive_cod2_inst_conv2;
        [ exact TAs | exact Tas | exact TP0 | exact Tbs | exact cvPb ]).
  (* (i) the first endpoint moves *)
  have ETy2 : EqValTy (S (S RB0)) Δ
      (Core.tpi (Core.tid A[σ] P0 P0) Core.tuniv)
      (Core.tpi (Core.tid A[σ] a[σ] P0) Core.tuniv)
      (wt_Selection_codU hCod2 SelF2).
  { have hh := peety uf2 (app f2 u2) SelF2 WTuf2 P0 TP0 VPf2.
    rewrite !motive_cod2_subst in hh.
    have hh2 : EqVal (S (S (S RB0))) Δ
        (Core.tpi (Core.tid A[σ] P0 P0) Core.tuniv)
        (Core.tpi (Core.tid A[σ] a[σ] P0) Core.tuniv)
        Core.tuniv (wt_Selection_codU hCod2 SelF2).
    { eapply (EqVal_fuel_any (k := S (S RB0)) (k' := S (S (S RB0))));
        [ (unfold RB0; lia) | (unfold RB0; lia)
        | (unfold RB0; lia) | (unfold RB0; lia) | exact hh ]. }
    rewrite EqVal_tuniv in hh2. exact (proj2 (proj2 hh2)). }
  (* (ii) ... and the second *)
  have ETy3 : EqValTy (S (S RB0)) Δ
      (Core.tpi (Core.tid A[σ] a[σ] P0) Core.tuniv)
      (Core.tpi (Core.tid A[σ] a[σ] b[σ]) Core.tuniv)
      (wt_Selection_codU hCod2 SelF2).
  { have hh := peeR uf2 (app f2 u2) SelF2 WTuf2 P0 b[σ] cvPb EqB2f.
    rewrite !motive_cod2_subst in hh.
    have hh2 : EqVal (S (S (S RB0))) Δ
        (Core.tpi (Core.tid A[σ] a[σ] P0) Core.tuniv)
        (Core.tpi (Core.tid A[σ] a[σ] b[σ]) Core.tuniv)
        Core.tuniv (wt_Selection_codU (wt_abs_ty hC2) SelF2).
    { eapply (EqVal_fuel_any (k := S (S RB0)) (k' := S (S (S RB0))));
        [ (unfold RB0; lia) | (unfold RB0; lia)
        | (unfold RB0; lia) | (unfold RB0; lia) | exact hh ]. }
    rewrite EqVal_tuniv in hh2.
    eapply EqValTy_irr. exact (proj2 (proj2 hh2)). }
  have E2 : EqVal (S (S RB0)) Δ (Core.app (Core.app C[σ] P0) P0)
              (Core.app (Core.app C[σ] a[σ]) b[σ])
              (Core.tpi (Core.tid A[σ] a[σ] b[σ]) Core.tuniv)
              (wt_Selection_abs hC2 Sel2).
  { have E2a' : EqVal (S (S RB0)) Δ (Core.app (Core.app C[σ] P0) P0)
                  (Core.app (Core.app C[σ] a[σ]) P0)
                  (Core.tpi (Core.tid A[σ] a[σ] P0) Core.tuniv)
                  (wt_Selection_abs hC2 Sel2).
    { eapply (EqVal_EqVal_fwd (B := Core.tpi (Core.tid A[σ] a[σ] P0) Core.tuniv));
        [ (unfold RB0; lia) | (unfold RB0; lia) | exact cvTy2 | exact E2a
        | exact ETy2 ]. }
    have E2ab : EqVal (S (S RB0)) Δ (Core.app (Core.app C[σ] P0) P0)
                  (Core.app (Core.app C[σ] a[σ]) b[σ])
                  (Core.tpi (Core.tid A[σ] a[σ] P0) Core.tuniv)
                  (wt_Selection_abs hC2 Sel2).
    { eapply (EqVal_trans (M2 := Core.app (Core.app C[σ] a[σ]) P0));
        [ (unfold RB0; lia) | (unfold RB0; lia) | exact E2a' | exact E2b ]. }
    eapply (EqVal_EqVal_fwd (B := Core.tpi (Core.tid A[σ] a[σ] b[σ]) Core.tuniv));
      [ (unfold RB0; lia) | (unfold RB0; lia) | exact cvTy3 | exact E2ab
      | exact ETy3 ]. }
  (* ---- level 3: the proof argument ---- *)
  rewrite Eq_v2 in LEn1.
  have [g1 [b1 [f1 [Ev2 [Ecod1 LEn0]]]]] := spine_descend HaT LEn1 WTv2.
  clear Eq_v2. subst v2.
  (* the level-3 function code, obtained by rewriting a plain [wt] statement --
     no generalise-dance needed for this one *)
  have hC1 : wt (abs g1) (tpi b1 f1) by (rewrite -Ecod1; exact WTv2).
  have NBcod1 : ~ is_bot (app f2 u2) by (rewrite Ecod1; done).
  have Rcod1t : rk (tpi b1 f1) <= rk_fun f2 by (rewrite -Ecod1; exact Rcod2b).
  have evCod1 : EvalRel (Core.tpi (Core.tid A a b) Core.tuniv) ρ (app f2 u2).
  { rewrite -motive_cod2_subst.
    eapply EvalRel_Pi_app_type;
      [ exact evCod2C | exact Vρ | exact Vu2 | reflexivity | exact NBcod1
      | exact evb_u2 ]. }
  rewrite Ecod1 in evCod1. have evCod1C := evCod1.
  cbn [EvalRel] in evCod1.
  move: evCod1 => [Vb1 [Vf1 [evId_b1 [a1' [evId_b1' EB1fun]]]]].
  have Vg1 : valid_fun g1 := proj1 (andb_prop _ _ (wt_valid_tm hC1)).
  have Vw1 : valid w1 := EvalRel_valid evp1.
  have [u1 [v1 [Sel1 [Le_u1 Eq_v1]]]] := selectionBelow Vg1 Vw1.
  have [WTu1 WTv1] : wt u1 b1 /\ wt v1 (app f1 u1).
  { eapply wt_Selection_cod;
      [ exact (wt_abs_ty hC1) | exact (wt_abs_inv1 hC1)
      | move=> ui vi Hin; exact (wt_abs_inv2 hC1 Hin erefl)
      | exact Vg1 | exact Sel1 ]. }
  have Vu1 : valid u1 := wt_valid_tm WTu1.
  have Rg1 : rk_fun g1 < rk (abs g1) by (cbn; lia).
  have Rb1 : rk b1 < rk (tpi b1 f1) by (cbn; lia).
  have Rf1 : rk_fun f1 < rk (tpi b1 f1) by (cbn; lia).
  have Ru1 : rk u1 <= rk_fun g1 := rk_Selection_key Sel1.
  have Rv1 : rk v1 <= rk_fun g1 := rk_Selection_val Sel1.
  have Rcod1b : rk (app f1 u1) <= rk_fun f1 := rk_app f1 u1.
  have Lu1 : le u1 (rfl wmax)
    by (eapply (@le_trans u1 w1 (rfl wmax));
        [ exact Vu1 | exact Vw1 | (cbn; exact Vwmax) | exact Le_u1 | exact L1 ]).
  (* now move [V2R] / [E2] onto the level-3 function code.  Their index is
     [wt_Selection_abs hC2 Sel2], which does not mention [b1], so the case
     analysis in the argument lemmas below stays local. *)
  move: E2. move: V2R.
  move: (wt_Selection_abs hC2 Sel2).
  rewrite Ecod1.
  move=> hC1' V2R'0 E2'0.
  have V2R' : Val (S (S RB0)) Δ (Core.app (Core.app C[σ] a[σ]) b[σ])
                (Core.tpi (Core.tid A[σ] a[σ] b[σ]) Core.tuniv) hC1.
  { eapply Val_irr. exact V2R'0. }
  have E2' : EqVal (S (S RB0)) Δ (Core.app (Core.app C[σ] P0) P0)
               (Core.app (Core.app C[σ] a[σ]) b[σ])
               (Core.tpi (Core.tid A[σ] a[σ] b[σ]) Core.tuniv) hC1.
  { eapply EqVal_irr. exact E2'0. }
  have evp_u1 : EvalRel p ρ u1
    by (eapply EvalRel_down; [ exact Vρ | exact Vu1 | exact evp1 | exact Le_u1 ]).
  (* ---- the level-3 arguments: Coquand's rule at the level-3 domain code.
     The domain type is the *right* spine's [tid A[σ] a[σ] b[σ]], whose [ValTy]
     at that code is available because the code's endpoints approximate [a] and
     [b].  The code analysis is local to this [have]. *)
  have TRoff : typing Δ (Core.rfl P0) (Core.tid A[σ] a[σ] b[σ])
    by (eapply rfl_offdiag_typing;
        [ exact TAs | exact TP0 | exact Tas | exact Tbs | exact cvPa | exact cvPb ]).
  have [VargL EargR] :
      Val (S RB0) Δ (Core.rfl P0) (Core.tid A[σ] a[σ] b[σ]) WTu1
      /\ EqVal (S RB0) Δ (Core.rfl P0) p[σ] (Core.tid A[σ] a[σ] b[σ]) WTu1.
  { destruct b1 as [ | | | | | | | tb xb yb | | | | ];
      try solve [ (split; exact I) | (cbn in evId_b1; done) ].
    destruct u1 as [ | | | | | | | | u0 | | | ]; try solve [ (split; exact I) ].
    cbn in evId_b1. move: evId_b1 => [Vidb [evA_tb [ev_xb ev_yb]]].
    have Rtb : rk tb < rk (tid tb xb yb) by (cbn; lia).
    have Rxb : rk xb < rk (tid tb xb yb) by (cbn; lia).
    have Ryb : rk yb < rk (tid tb xb yb) by (cbn; lia).
    have Rlub_tb : rk (lub tb tc) <= max (rk tb) (rk tc) := rk_lub tb tc.
    have Lu0 : le u0 wmax.
    { move: (le_rfl_inv Lu1) => [w' [Ew Lw]].
      have Ew' : wmax = w' by (injection Ew; done). subst w'. exact Lw. }
    have [VP1 [EqA1 EqB1]] :=
      transW tb u0 (wt_rfl_wit WTu1) RB0 Lu0 evA_tb
        ltac:(unfold RB0; lia) ltac:(unfold RB0; lia).
    have [valA_tb _] :=
      STA ρ m Δ σ σ' TS TS' CS Fρ VS VS' EVS CΔ
          tb tuniv (wt_tid_dom (wt_rfl_ty WTu1)) evA_tb evU.
    have [valA_xb _] :=
      STa ρ m Δ σ σ' TS TS' CS Fρ VS VS' EVS CΔ
          xb tb (wt_tid_lhs (wt_rfl_ty WTu1)) ev_xb evA_tb.
    have [valB_yb _] :=
      STb ρ m Δ σ σ' TS TS' CS Fρ VS VS' EVS CΔ
          yb tb (wt_tid_rhs (wt_rfl_ty WTu1)) ev_yb evA_tb.
    have VTid : ValTy RB0 Δ (Core.tid A[σ] a[σ] b[σ]) (wt_rfl_ty WTu1).
    { rewrite ValTy_tid.
      exists A[σ], a[σ], b[σ]. split; [ apply ms_refl | ].
      split; [ exact TAs | ]. split; [ exact Tas | ]. split; [ exact Tbs | ].
      split; [ exact (wt_valid_tm (wt_rfl_ty WTu1)) | ].
      split; [ exact (valA_tb RB0 ltac:(unfold RB0; cbn; lia)) | ].
      split; [ exact (valA_xb RB0 ltac:(unfold RB0; lia))
             | exact (valB_yb RB0 ltac:(unfold RB0; lia)) ]. }
    split.
    - eapply Val_rfl_offdiag;
        [ exact VTid | exact TRoff | exact cvPa | exact cvPb
        | exact VP1 | exact EqA1 | exact EqB1 ].
    - eapply EqVal_rfl_offdiag;
        [ exact VTid | exact TRoff | exact TP0 | exact HRp | exact cvPp
        | exact cvPa | exact cvPb | exact VP1 | exact EqA1 | exact EqB1 ]. }
  (* ---- level 3's two steps; both land at [tuniv], so no transport ---- *)
  have E3a : EqVal (S RB0) Δ
               (Core.app (Core.app (Core.app C[σ] P0) P0) (Core.rfl P0))
               (Core.app (Core.app (Core.app C[σ] a[σ]) b[σ]) (Core.rfl P0))
               ((Core.tuniv : Tm (S m))[(Core.rfl P0)..])
               (wt_Selection_abs hC1 Sel1).
  { eapply spine_EqVal_fun;
      [ apply ms_refl | exact E2' | exact TRoff | exact VargL ]. }
  have E3b : EqVal (S RB0) Δ
               (Core.app (Core.app (Core.app C[σ] a[σ]) b[σ]) (Core.rfl P0))
               (Core.app (Core.app (Core.app C[σ] a[σ]) b[σ]) p[σ])
               ((Core.tuniv : Tm (S m))[(Core.rfl P0)..])
               (wt_Selection_abs hC1 Sel1).
  { eapply spine_EqVal_arg;
      [ apply ms_refl | exact V2R' | (apply c_sym; exact cvPp) | exact EargR ]. }
  have E3 : EqVal (S RB0) Δ
              (Core.app (Core.app (Core.app C[σ] P0) P0) (Core.rfl P0))
              (Core.app (Core.app (Core.app C[σ] a[σ]) b[σ]) p[σ])
              Core.tuniv (wt_Selection_abs hC1 Sel1).
  { eapply (EqVal_trans
              (M2 := Core.app (Core.app (Core.app C[σ] a[σ]) b[σ]) (Core.rfl P0)));
      [ (unfold RB0; lia) | (unfold RB0; lia) | exact E3a | exact E3b ]. }
  (* ---- land on the requested code ---- *)
  have evUf : EvalRel Core.tuniv ρ (app f1 u1).
  { destruct (is_bot (app f1 u1)) eqn:Hbf.
    - have E : app f1 u1 = bot by (apply is_bot_eq; rewrite Hbf).
      rewrite E. apply EvalRel_bot.
    - have hh : EvalRel ((Core.tuniv : Tm (S n))[p..]) ρ (app f1 u1).
      { eapply EvalRel_Pi_app_type;
          [ exact evCod1C | exact Vρ | exact Vu1 | reflexivity
          | (rewrite Hbf; done) | exact evp_u1 ]. }
      exact hh. }
  have Lf1 : le (app f1 u1) tuniv by (move: evUf; cbn; done).
  have LEaTv1 : le aT v1 by (rewrite Eq_v1 in LEn0; exact LEn0).
  have hUtu : wt tuniv tuniv := wt_tuniv.
  have Waf1 : wt (app f1 u1) tuniv := wt_ty_tuniv WTv1.
  have VTU : Val (S RB0) Δ Core.tuniv Core.tuniv hUtu by exact I.
  apply (EqVal_fuel_any (k := S RB0) (k' := k));
    [ (unfold RB0; lia) | (unfold RB0; lia) | lia | (cbn in Hk |- *; lia) | ].
  eapply (@EqVal_transport_up _ Δ
            (Core.app (Core.app (Core.app C[σ] P0) P0) (Core.rfl P0))
            (Core.app (Core.app (Core.app C[σ] a[σ]) b[σ]) p[σ]) Core.tuniv
            v1 aT (app f1 u1) tuniv
            (wt_Selection_abs hC1 Sel1) hAf Waf1 hUtu);
    [ exact LEaTv1 | exact Lf1 | exact VTU | exact E3 ].
Qed.

(** Adequacy of the [J] eliminator (Agda ID's
    [JApp / JAppE / JCase / JDriver / JEndpoint / JMotive / JRef / JTypeEq]).

    Shape of the argument.  [EvalRel (jcase C d p)] records the result [u] as
    the edge [w' ↦ u] of the base branch [d], where [rfl w'] is a value of the
    proof [p].  So:

    - [STp] at the proof's own code hands back a [ValId] record: the witness
      *term* [P0] with [HeadRed p[σ] (rfl P0)] and -- Coquand's membership rule
      -- conversions *and* reducible equalities from [P0] to **both**
      endpoints.  This is where [idInjectivity] really gets used.
    - [reduction.HeadRed_jcase] and [typing.jcase_drive_conv] then drive
      [(jcase C d p)[σ]] to [app d[σ] P0] at the goal's type, so
      [Val_beta_expand] reduces the goal to a [Val] of [app d[σ] P0].
    - [STd]'s value edge ([PiAppVal], which accepts an arbitrary Δ-term)
      applied to [P0] supplies that [Val], but at [d]'s codomain type
      [app (app (app C[σ] P0) P0) (rfl P0)].
    - Moving it to the goal's type is Agda's [JTypeEq]: the [EqValTy] between
      the motive applied to the witness and the motive applied to [a], [b], [p].
*)
Lemma st_jcase (A a b C d p : Tm n) :
  typing Γ A Core.tuniv ->
  typing Γ a A ->
  typing Γ b A ->
  typing Γ C (motive_ty A) ->
  typing Γ d (base_ty A C) ->
  typing Γ p (Core.tid A a b) ->
  semantic_typing Γ A Core.tuniv ->
  semantic_typing Γ a A ->
  semantic_typing Γ b A ->
  semantic_typing Γ C (motive_ty A) ->
  semantic_typing Γ d (base_ty A C) ->
  semantic_typing Γ p (Core.tid A a b) ->
(* ------------------------- *)
  semantic_typing Γ (Core.jcase C d p)
    (Core.app (Core.app (Core.app C a) b) p).
Proof.
  move=> TA Ta Tb TC Td Tp STA STa STb STC STd STp.
  move=> ρ m Δ σ σ' TS TS' CS Fρ VS VS' EVS CΔ u a0 WT evJ evT.
  have Vρ : valid_env ρ := fits_valid_env Fρ.
  (* everything up to the final transports is shared by the two conjuncts, so
     the [split] comes last *)
  destruct (is_bot u) eqn:Hu.
  { have Eu : u = bot by (apply is_bot_eq; rewrite Hu). subst u.
    split; move=> RB Hrank; [ apply Val_Bot | apply EqVal_Bot ]. }
    (* the proof's value drives the eliminator *)
    cbn in evJ. move: evJ => [wp [evP Ebr]].
    destruct wp as [ | | | | | | | | w' | | | ]; try done.
    { (* the proof takes [bot], so the result does too *)
      move: Ebr => [_ /le_bot_inv Eu]. subst u. by rewrite /= in Hu. }
    (* enlarge the proof's value to a well-typed one: its type code is an [Id]
       code, and [wt] on it *is* Coquand's rule *)
    have ITp : InvTyped Γ p (Core.tid A a b) ρ := typing_EvalRel Tp Fρ.
    have [pv [ap [WTp [LEp [evPbig evIdCode]]]]] := ITp _ evP.
    move: (le_rfl_inv LEp) => [w'' [Epv Lw'w'']]. subst pv.
    destruct ap as [ | | | | | | | t up vp | | | | ];
      try solve [ cbn in evIdCode; done | (move: (wt_bot_inv WTp); discriminate) ].
    have evIdC := evIdCode. cbn in evIdC.
    move: evIdC => [Vid [evA_t [eva_up evb_vp]]].
    (* [STp]'s record, available at every fuel above the proof's rank *)
    have [valP _] :=
      STp ρ m Δ σ σ' TS TS' CS Fρ VS VS' EVS CΔ
          (rfl w'') (tid t up vp) WTp evPbig evIdCode.
    have valPk : forall k, max (rk (rfl w'')) (rk (tid t up vp)) < k ->
        ValTy k Δ (Core.tid A a b)[σ] (wt_rfl_ty WTp)
        /\ ValId k Δ p[σ] (Core.tid A a b)[σ] WTp.
    { move=> k Hk. have hh := valP (S k) ltac:(lia). rewrite Val_rfl in hh. exact hh. }
    (* name the witness term once, at one fuel *)
    pose kP := S (max (rk (rfl w'')) (rk (tid t up vp))).
    have HkP : max (rk (rfl w'')) (rk (tid t up vp)) < kP by (unfold kP; lia).
    have [_ IdP0] := valPk kP HkP.
    move: IdP0 =>
      [A0 [a0' [b0' [HRid [P0 [HRp [cvP [cvPa [cvPb [VP0 [EP0a EP0b]]]]]]]]]]].
    cbn in HRid. have [EA0 [Ea0 Eb0]] := HeadRed_tid_eq HRid. subst A0 a0' b0'.
    (* ... and re-derive the record at an arbitrary fuel, at the *same* witness
       ([HeadRed_rfl_det] pins it down) *)
    have IdPk : forall k, max (rk (rfl w'')) (rk (tid t up vp)) < k ->
        Val k Δ P0 A[σ] (wt_rfl_wit WTp)
        /\ EqVal k Δ P0 a[σ] A[σ] (wt_rfl_wit WTp)
        /\ EqVal k Δ P0 b[σ] A[σ] (wt_rfl_wit WTp).
    { move=> k Hk. have [_ Idk] := valPk k Hk.
      move: Idk =>
        [A1 [a1 [b1 [HRid1 [P1 [HRp1 [cv1 [cva1 [cvb1 [V1 [E1a E1b]]]]]]]]]]].
      cbn in HRid1. have [E1 [E2 E3]] := HeadRed_tid_eq HRid1. subst A1 a1 b1.
      have EP : P1 = P0 by (eapply HeadRed_rfl_det; [ exact HRp1 | exact HRp ]).
      subst P1. split; [ exact V1 | split; [ exact E1a | exact E1b ] ]. }
    (* the syntactic side of the driver *)
    have TAs : typing Δ A[σ] Core.tuniv
      by (move: (substitution_tm _ _ _ _ _ TA TS CΔ) => hh; cbn in hh; exact hh).
    have Tas : typing Δ a[σ] A[σ]
      by (eapply substitution_tm; [ exact Ta | exact TS | exact CΔ ]).
    have Tbs : typing Δ b[σ] A[σ]
      by (eapply substitution_tm; [ exact Tb | exact TS | exact CΔ ]).
    have TCs : typing Δ C[σ] (motive_ty A[σ]).
    { move: (substitution_tm _ _ _ _ _ TC TS CΔ) => hh.
      rewrite subst_motive_ty in hh. exact hh. }
    have Tds : typing Δ d[σ] (base_ty A[σ] C[σ]).
    { move: (substitution_tm _ _ _ _ _ Td TS CΔ) => hh.
      rewrite subst_base_ty in hh. exact hh. }
    have Tps : typing Δ p[σ] (Core.tid A[σ] a[σ] b[σ]).
    { move: (substitution_tm _ _ _ _ _ Tp TS CΔ) => hh. cbn in hh. exact hh. }
    have TP0 : typing Δ P0 A[σ] := proj1 (conv_typing cvPa).
    have cvPp : conv Δ p[σ] (Core.rfl P0) (Core.tid A[σ] a[σ] b[σ])
      by (move: cvP; cbn; done).
    have DRIVE : conv Δ (Core.jcase C[σ] d[σ] p[σ]) (Core.app d[σ] P0)
                   (Core.app (Core.app (Core.app C[σ] a[σ]) b[σ]) p[σ])
      by (eapply jcase_drive_conv;
          [ exact TAs | exact TP0 | exact Tas | exact Tbs | exact TCs | exact Tds
          | exact Tps | exact cvPa | exact cvPb | exact cvPp ]).
    have HRJ : HeadRed (Core.jcase C[σ] d[σ] p[σ]) (Core.app d[σ] P0)
      by (eapply HeadRed_jcase; exact HRp).
    (* ---- [d]'s value edge, applied to the witness term [P0] ---- *)
    have evU : EvalRel Core.tuniv ρ tuniv by (cbn; apply le_refl).
    have Vw'  : valid w'  by (move: (EvalRel_valid evP); cbn; done).
    have Vw'' : valid w'' by (move: (EvalRel_valid evPbig); cbn; done).
    have ITd : InvTyped Γ d (base_ty A C) ρ := typing_EvalRel Td Fρ.
    have [vd [ad [WTd [LEd [evDbig evBase]]]]] := ITd _ Ebr.
    unfold singleton in LEd. rewrite Hu in LEd.
    have [g [Evd LEfun]] := le_abs_inv LEd. subst vd.
    destruct ad as [ | | | | | bd fd | | | | | | ];
      try solve [ exfalso; clear -WTd; inversion WTd ].
    have evBaseC := evBase. rewrite /base_ty in evBaseC. cbn in evBaseC.
    move: evBaseC => [Vbd [Vfd [evA_bd [ad2 [evA_bd2 EBfun]]]]].
    have Vg : valid_fun g := proj1 (andb_prop _ _ (wt_valid_tm WTd)).
    have [u_sel [v_sel [Sel [Le_usel Eq_vsel]]]] := selectionBelow Vg Vw'.
    have [WTu_sel WTv_sel] : wt u_sel bd /\ wt v_sel (app fd u_sel).
    { eapply wt_Selection_cod;
        [ exact (wt_abs_ty WTd) | exact (wt_abs_inv1 WTd)
        | move=> ui vi Hin; exact (wt_abs_inv2 WTd Hin erefl)
        | exact Vg | exact Sel ]. }
    have Vusel : valid u_sel := wt_valid_tm WTu_sel.
    have LEu_vsel : le u v_sel.
    { rewrite le_fun_cons in LEfun.
      have LEua := proj1 (andb_prop _ _ LEfun).
      rewrite Eq_vsel in LEua. exact LEua. }
    (* the argument's [Val], moved from the *proof's* code [(w'', t)] to the
       *function's* selection code [(u_sel, bd)] through the join [lub bd t] --
       [Val_app_transport] is exactly this dance.  [Val] of [A[σ]] at the join
       comes from [STA], which is quantified over every code [A] evaluates. *)
    have Wt_t  : wt t tuniv := wt_ty_tuniv (wt_rfl_wit WTp).
    have Wt_bd : wt bd tuniv := wt_tpi_dom (wt_abs_ty WTd).
    have Cbdt : compatible bd t
      by (eapply EvalRel_compatible; [ exact Vρ | exact evA_bd | exact evA_t ]).
    have hUlub : wt (lub bd t) tuniv := wt_lub Wt_bd Cbdt Wt_t.
    have evA_lub : EvalRel A ρ (lub bd t)
      := proj2 (EvalRel_compatible_lub Vρ evA_bd evA_t) _ erefl.
    have [valA_lub _] :=
      STA ρ m Δ σ σ' TS TS' CS Fρ VS VS' EVS CΔ (lub bd t) tuniv hUlub evA_lub evU.
    have LEuselw'' : le u_sel w''
      by (eapply (@le_trans u_sel w' w'');
          [ exact Vusel | exact Vw' | exact Vw'' | exact Le_usel | exact Lw'w'' ]).
    have VargK : forall k,
        max (rk (lub bd t)) (rk tuniv) < k ->
        max (rk (rfl w'')) (rk (tid t up vp)) < k ->
        Val k Δ P0 A[σ] WTu_sel.
    { move=> k Hk1 Hk2.
      eapply (@Val_app_transport _ Δ P0 A[σ] u_sel w'' bd t
                (wt_rfl_wit WTp) WTu_sel hUlub);
        [ exact Cbdt | exact LEuselw'' | exact (valA_lub k Hk1)
        | exact (proj1 (IdPk k Hk2)) ]. }
    (* ---- the value edge itself ---- *)
    pose RBf := S (max (max (rk (abs g)) (rk (tpi bd fd)))
                       (max (max (rk u) (rk a0))
                            (max (rk (rfl w'')) (rk (tid t up vp))))).
    have RKlub : rk (lub bd t) <= max (rk bd) (rk t) := rk_lub bd t.
    have RKbd : rk bd < rk (tpi bd fd) by (cbn; lia).
    have RKt  : rk t < rk (tid t up vp) by (cbn; lia).
    have RKpi : 1 <= rk (tpi bd fd) by (cbn; lia).
    have RKtu : rk tuniv = 1 by reflexivity.
    have HfD : max (rk (abs g)) (rk (tpi bd fd)) < S RBf by (unfold RBf; lia).
    have HfA : max (rk (lub bd t)) (rk tuniv) < RBf by (unfold RBf; lia).
    have HfP : max (rk (rfl w'')) (rk (tid t up vp)) < RBf by (unfold RBf; lia).
    have [valDbig _] :=
      STd ρ m Δ σ σ' TS TS' CS Fρ VS VS' EVS CΔ
          (abs g) (tpi bd fd) WTd evDbig evBase.
    have VD := valDbig (S RBf) HfD. rewrite Val_abs in VD.
    move: VD => [_ VPi]. move: VPi => [A0d [B0d [HRpi [CTpi [pav _]]]]].
    rewrite subst_base_ty /base_ty in HRpi.
    have [EA0d EB0d] := HeadRed_tpi_eq HRpi. subst A0d B0d.
    have Vapp := pav u_sel v_sel Sel WTu_sel P0 TP0 (VargK RBf HfA HfP).
    (* [d]'s codomain, instantiated at the witness.  Normalise the substitution
       as a standalone term equality: [asimpl] on the whole [Val] statement is
       ruinously slow here. *)
    have EqB : (Core.app (Core.app (Core.app (C[σ])⟨↑⟩ (Core.var var_zero))
                            (Core.var var_zero))
                  (Core.rfl (Core.var var_zero)))[P0..]
             = Core.app (Core.app (Core.app C[σ] P0) P0) (Core.rfl P0)
      by (asimpl; reflexivity).
    rewrite EqB in Vapp.
    (* ---- the goal's type also takes the edge's codomain code ----
       [d]'s codomain edge instantiates the motive at codes below the selected
       argument, and Coquand's rule makes [a], [b] and [p] all take the
       witness, so [EvalRel_base_cod_spine] converts that instantiation into
       one of the *goal's* spine.  This is what makes [a0] and [app fd u_sel]
       compatible, hence [Val_app_transport] applicable. *)
    have Eaw'' : EvalRel a ρ w''
      by (eapply EvalRel_down;
          [ exact Vρ | exact Vw'' | exact eva_up | exact (wt_rfl_le_lhs WTp) ]).
    have Ebw'' : EvalRel b ρ w''
      by (eapply EvalRel_down;
          [ exact Vρ | exact Vw'' | exact evb_vp | exact (wt_rfl_le_rhs WTp) ]).
    have [xs [WTxs [LExs EBxs]]] :
      exists xs (_ : wt xs ad2), le xs u_sel
        /\ EvalRel (Core.app (Core.app (Core.app C⟨↑⟩ (Core.var var_zero))
                                (Core.var var_zero))
                      (Core.rfl (Core.var var_zero)))
             (xs .: ρ) (app fd u_sel)
      by (apply (EBfun u_sel (app fd u_sel) Vusel); reflexivity).
    have Vxs : valid xs := wt_valid_tm WTxs.
    have LExsw'' : le xs w''
      by (eapply (@le_trans xs u_sel w'');
          [ exact Vxs | exact Vusel | exact Vw'' | exact LExs | exact LEuselw'' ]).
    have evT_af :
      EvalRel (Core.app (Core.app (Core.app C a) b) p) ρ (app fd u_sel)
      by (eapply EvalRel_base_cod_spine;
          [ exact Vρ | exact Vxs | exact LExsw'' | exact Eaw'' | exact Ebw''
          | exact evPbig | exact EBxs ]).
    have Caf : compatible a0 (app fd u_sel)
      by (eapply EvalRel_compatible; [ exact Vρ | exact evT | exact evT_af ]).
    have Waf : wt (app fd u_sel) tuniv := wt_ty_tuniv (wt_Selection_abs WTd Sel).
    have hUcT : wt (lub a0 (app fd u_sel)) tuniv
      := wt_lub (wt_ty_tuniv WT) Caf Waf.
    have evT_lub :
      EvalRel (Core.app (Core.app (Core.app C a) b) p) ρ (lub a0 (app fd u_sel))
      := proj2 (EvalRel_compatible_lub Vρ evT evT_af) _ erefl.
    have RKvsel : rk v_sel <= rk_fun g := rk_Selection_val Sel.
    have RKg : rk_fun g < rk (abs g) by (cbn; lia).
    have RKfd : rk_fun fd < rk (tpi bd fd) by (cbn; lia).
    have RKcod : rk (app fd u_sel) <= rk_fun fd := rk_app fd u_sel.
    have RKlubT : rk (lub a0 (app fd u_sel)) <= max (rk a0) (rk (app fd u_sel))
      := rk_lub a0 (app fd u_sel).
    (* the edge's codomain code is informative: otherwise [wt_bot_inv] would
       force the selection value, hence the result [u], to be [bot] *)
    have Bfa : is_bot (app fd u_sel) = false.
    { destruct (is_bot (app fd u_sel)) eqn:Hb; [ | reflexivity ].
      exfalso.
      have E : app fd u_sel = bot by (apply is_bot_eq; rewrite Hb).
      move: WTv_sel. rewrite E => WTr.
      move: (wt_bot_inv WTr) => Ev. rewrite Ev in LEu_vsel.
      move: LEu_vsel => /le_bot_inv Eu. subst u. by rewrite /= in Hu. }
    (* ---- JTypeEq at the edge's codomain code ----
       the spine codes there are below the witness by construction, which is
       exactly what [jcase_motive_EqVal] needs *)
    have [ws1 [ws2 [ws3 [evC3s [Ls3 [Ls2 [Ls1 [evas3 [evbs2 evps1]]]]]]]]] :=
      EvalRel_base_cod_spine_codes Vρ Vxs LExsw'' Eaw'' Ebw'' evPbig Bfa EBxs.
    have EQTY : forall kk, max (rk (app fd u_sel)) (rk tuniv) < kk ->
        EqVal kk Δ (Core.app (Core.app (Core.app C[σ] P0) P0) (Core.rfl P0))
                   (Core.app (Core.app (Core.app C[σ] a[σ]) b[σ]) p[σ])
                   Core.tuniv Waf.
    { eapply jcase_motive_EqVal;
        [ exact TA | exact Ta | exact Tb | exact TC | exact Tp
        | exact STA | exact STa | exact STb | exact STC | exact STp
        | exact TS | exact TS' | exact CS | exact Fρ | exact VS | exact VS'
        | exact EVS | exact CΔ | exact evPbig | exact evA_t
        | exact HRp | exact cvPa | exact cvPb | exact cvPp | exact IdPk
        | exact Bfa | exact evC3s | exact Ls3 | exact Ls2 | exact Ls1
        | exact evas3 | exact evbs2 | exact evps1 ]. }
    have ETY : EqValTy RBf Δ
        (Core.app (Core.app (Core.app C[σ] P0) P0) (Core.rfl P0))
        (Core.app (Core.app (Core.app C[σ] a[σ]) b[σ]) p[σ]) Waf.
    { have hh := EQTY (S RBf) ltac:(unfold RBf; lia).
      rewrite EqVal_tuniv in hh. exact (proj2 (proj2 hh)). }
    have CVTY : conv Δ
        (Core.app (Core.app (Core.app C[σ] P0) P0) (Core.rfl P0))
        (Core.app (Core.app (Core.app C[σ] a[σ]) b[σ]) p[σ]) Core.tuniv
      by (eapply motive_app_conv_witness;
          [ exact TAs | exact TP0 | exact Tas | exact Tbs | exact TCs | exact Tps
          | exact cvPa | exact cvPb | exact cvPp ]).
    (* move the edge result onto the goal's type ... *)
    have VappT : Val RBf Δ (Core.app d[σ] P0)
                   (Core.app (Core.app (Core.app C[σ] a[σ]) b[σ]) p[σ])
                   (wt_Selection_abs WTd Sel).
    { eapply (Val_EqVal_fwd
                (B := Core.app (Core.app (Core.app C[σ] a[σ]) b[σ]) p[σ]));
        [ (unfold RBf; lia) | (unfold RBf; lia) | exact CVTY | exact Vapp
        | exact ETY ]. }
    (* ... and the goal type's own [ValTy] at the join, for the code transport *)
    have VTgoal : Val RBf Δ
        (Core.app (Core.app (Core.app C[σ] a[σ]) b[σ]) p[σ]) Core.tuniv hUcT.
    { eapply jcase_type_spine;
        [ exact TA | exact Ta | exact Tb | exact TC | exact Tp
        | exact STa | exact STb | exact STC | exact STp
        | exact TS | exact TS' | exact CS | exact Fρ | exact VS | exact VS'
        | exact EVS | exact CΔ | exact evT_lub | (unfold RBf; lia) ]. }
    (* ---- finish: fuel, head-expansion, code transport ---- *)
    split; move=> RB Hrank.
    + (* ---------- the [Val] conjunct ---------- *)
      apply (Val_fuel_any (k := RBf) (k' := RB));
        [ (unfold RBf; lia) | (unfold RBf; lia)
        | (cbn in Hrank |- *; lia) | (cbn in Hrank |- *; lia) | ].
      eapply Val_beta_expand; [ exact HRJ | exact DRIVE | ].
      eapply (@Val_app_transport _ Δ (Core.app d[σ] P0)
                (Core.app (Core.app (Core.app C[σ] a[σ]) b[σ]) p[σ])
                u v_sel a0 (app fd u_sel)
                (wt_Selection_abs WTd Sel) WT hUcT);
        [ exact Caf | exact LEu_vsel | exact VTgoal | exact VappT ].
    + (* ---------- the [EqVal] conjunct ---------- *)
      (* the σ'-side witness, from [STp]'s [EqVal] conjunct's [EqValId] *)
      have [_ eqP] :=
        STp ρ m Δ σ σ' TS TS' CS Fρ VS VS' EVS CΔ
            (rfl w'') (tid t up vp) WTp evPbig evIdCode.
      have eqPk : forall k, max (rk (rfl w'')) (rk (tid t up vp)) < k ->
          ValTy k Δ (Core.tid A a b)[σ] (wt_rfl_ty WTp)
          /\ ValId k Δ p[σ] (Core.tid A a b)[σ] WTp
          /\ ValId k Δ p[σ'] (Core.tid A a b)[σ] WTp
          /\ EqValId k Δ p[σ] p[σ'] (Core.tid A a b)[σ] WTp.
      { move=> k Hk. have hh := eqP (S k) ltac:(lia).
        rewrite EqVal_rfl in hh. exact hh. }
      have [_ [_ [IdP' EqIdP]]] := eqPk kP HkP.
      move: EqIdP =>
        [_ [_ [M0 [N0 [HRm [HRn
          [A0e [a0e [b0e [HRide [cvMN EqMN]]]]]]]]]]].
      cbn in HRide. have [Z1 [Z2 Z3]] := HeadRed_tid_eq HRide. subst A0e a0e b0e.
      have EM : M0 = P0 by (eapply HeadRed_rfl_det; [ exact HRm | exact HRp ]).
      subst M0.
      move: IdP' =>
        [A2 [a2 [b2 [HRid2 [Q0 [HRq [cvq [cvqa [cvqb [VQ [EqQa EqQb]]]]]]]]]]].
      cbn in HRid2. have [Y1 [Y2 Y3]] := HeadRed_tid_eq HRid2. subst A2 a2 b2.
      have EQ0 : Q0 = N0 by (eapply HeadRed_rfl_det; [ exact HRq | exact HRn ]).
      subst Q0.
      (* ... at every fuel, with [HeadRed_rfl_det] pinning both witnesses *)
      have EqPk : forall k, max (rk (rfl w'')) (rk (tid t up vp)) < k ->
          EqVal k Δ P0 N0 A[σ] (wt_rfl_wit WTp).
      { move=> k Hk. have [_ [_ [_ EqIdk]]] := eqPk k Hk.
        move: EqIdk =>
          [_ [_ [M1 [N1 [HRm1 [HRn1
            [A1 [a1 [b1 [HRid1 [cv1 Eq1]]]]]]]]]]].
        cbn in HRid1. have [X1 [X2 X3]] := HeadRed_tid_eq HRid1. subst A1 a1 b1.
        have EM1 : M1 = P0 by (eapply HeadRed_rfl_det; [ exact HRm1 | exact HRp ]).
        have EN1 : N1 = N0 by (eapply HeadRed_rfl_det; [ exact HRn1 | exact HRn ]).
        subst M1 N1. exact Eq1. }
      (* ---- the σ'-side driver, retyped to the σ-side goal type ---- *)
      have TAs' : typing Δ A[σ'] Core.tuniv
        by (move: (substitution_tm _ _ _ _ _ TA TS' CΔ) => hh; cbn in hh; exact hh).
      have Tas' : typing Δ a[σ'] A[σ']
        by (eapply substitution_tm; [ exact Ta | exact TS' | exact CΔ ]).
      have Tbs' : typing Δ b[σ'] A[σ']
        by (eapply substitution_tm; [ exact Tb | exact TS' | exact CΔ ]).
      have TCs' : typing Δ C[σ'] (motive_ty A[σ']).
      { move: (substitution_tm _ _ _ _ _ TC TS' CΔ) => hh.
        rewrite subst_motive_ty in hh. exact hh. }
      have Tds' : typing Δ d[σ'] (base_ty A[σ'] C[σ']).
      { move: (substitution_tm _ _ _ _ _ Td TS' CΔ) => hh.
        rewrite subst_base_ty in hh. exact hh. }
      have Tps' : typing Δ p[σ'] (Core.tid A[σ'] a[σ'] b[σ']).
      { move: (substitution_tm _ _ _ _ _ Tp TS' CΔ) => hh. cbn in hh. exact hh. }
      have cAcross : conv Δ A[σ] A[σ'] Core.tuniv
        := subst_conv_cross TA CΔ TS TS' CS.
      have cacross : conv Δ a[σ] a[σ'] A[σ] := subst_conv_cross Ta CΔ TS TS' CS.
      have cbcross : conv Δ b[σ] b[σ'] A[σ] := subst_conv_cross Tb CΔ TS TS' CS.
      have TN0 : typing Δ N0 A[σ] := proj1 (conv_typing cvqa).
      have TN0' : typing Δ N0 A[σ']
        by (eapply t_conv; [ exact TN0 | exact cAcross ]).
      have cvqa' : conv Δ N0 a[σ'] A[σ'].
      { eapply c_conv; [ | exact cAcross ].
        eapply c_trans; [ exact cvqa | exact cacross ]. }
      have cvqb' : conv Δ N0 b[σ'] A[σ'].
      { eapply c_conv; [ | exact cAcross ].
        eapply c_trans; [ exact cvqb | exact cbcross ]. }
      have cIdcross : conv Δ (Core.tid A[σ] a[σ] b[σ])
                             (Core.tid A[σ'] a[σ'] b[σ']) Core.tuniv
        by (eapply c_tid;
            [ exact TAs | exact Tas | exact Tbs | exact cAcross
            | exact cacross | exact cbcross ]).
      have cvq' : conv Δ p[σ'] (Core.rfl N0) (Core.tid A[σ'] a[σ'] b[σ']).
      { eapply c_conv; [ | exact cIdcross ]. move: cvq. cbn. done. }
      have Tcross : conv Δ
          (Core.app (Core.app (Core.app C[σ'] a[σ']) b[σ']) p[σ'])
          ((Core.app (Core.app (Core.app C a) b) p)[σ]) Core.tuniv.
      { have Ttype : typing Γ (Core.app (Core.app (Core.app C a) b) p) Core.tuniv
          by (eapply motive_app_typing;
              [ exact TA | exact Ta | exact Tb | exact TC | exact Tp ]).
        apply c_sym.
        move: (subst_conv_cross Ttype CΔ TS TS' CS) => hh. cbn in hh. exact hh. }
      have DRIVE' : conv Δ (Core.jcase C[σ'] d[σ'] p[σ']) (Core.app d[σ'] N0)
                      ((Core.app (Core.app (Core.app C a) b) p)[σ]).
      { eapply c_conv; [ | exact Tcross ].
        eapply jcase_drive_conv;
          [ exact TAs' | exact TN0' | exact Tas' | exact Tbs' | exact TCs'
          | exact Tds' | exact Tps' | exact cvqa' | exact cvqb' | exact cvq' ]. }
      have HRJ' : HeadRed (Core.jcase C[σ'] d[σ'] p[σ']) (Core.app d[σ'] N0)
        by (eapply HeadRed_jcase; exact HRn).
      (* ---- the core: [d]'s cross edge, then its argument edge ---- *)
      have [_ eqDbig] :=
        STd ρ m Δ σ σ' TS TS' CS Fρ VS VS' EVS CΔ
            (abs g) (tpi bd fd) WTd evDbig evBase.
      have ED := eqDbig (S RBf) HfD. rewrite EqVal_abs in ED.
      move: ED => [_ [_ [VPid' EPid]]].
      move: EPid => [A0e2 [B0e2 [HRpi2 [CTpi2 paev]]]].
      rewrite subst_base_ty /base_ty in HRpi2.
      have [Ea2 Eb2] := HeadRed_tpi_eq HRpi2. subst A0e2 B0e2.
      move: VPid' => [A0e3 [B0e3 [HRpi3 [CTpi3 [pav' pae']]]]].
      rewrite subst_base_ty /base_ty in HRpi3.
      have [Ea3 Eb3] := HeadRed_tpi_eq HRpi3. subst A0e3 B0e3.
      have EqPsel : EqVal RBf Δ P0 N0 A[σ] WTu_sel.
      { eapply (@EqVal_app_transport _ Δ P0 N0 A[σ] u_sel w'' bd t
                  (wt_rfl_wit WTp) WTu_sel hUlub);
          [ exact Cbdt | exact LEuselw'' | exact (valA_lub RBf HfA)
          | exact (EqPk RBf HfP) ]. }
      have EA1 := paev u_sel v_sel Sel WTu_sel P0 TP0 (VargK RBf HfA HfP).
      have EA2 := pae' u_sel v_sel Sel WTu_sel P0 N0 cvMN EqPsel.
      rewrite EqB in EA1. rewrite EqB in EA2.
      have EAcore : EqVal RBf Δ (Core.app d[σ] P0) (Core.app d[σ'] N0)
                      (Core.app (Core.app (Core.app C[σ] P0) P0) (Core.rfl P0))
                      (wt_Selection_abs WTd Sel).
      { eapply (EqVal_trans (M2 := Core.app d[σ'] P0));
          [ (unfold RBf; lia) | (unfold RBf; lia) | exact EA1 | exact EA2 ]. }
      (* ---- finish, exactly as the [Val] half ---- *)
      have EAgoal : EqVal RBf Δ (Core.app d[σ] P0) (Core.app d[σ'] N0)
                      (Core.app (Core.app (Core.app C[σ] a[σ]) b[σ]) p[σ])
                      (wt_Selection_abs WTd Sel).
      { eapply (EqVal_EqVal_fwd
                  (B := Core.app (Core.app (Core.app C[σ] a[σ]) b[σ]) p[σ]));
          [ (unfold RBf; lia) | (unfold RBf; lia) | exact CVTY | exact EAcore
          | exact ETY ]. }
      apply (EqVal_fuel_any (k := RBf) (k' := RB));
        [ (unfold RBf; lia) | (unfold RBf; lia)
        | (cbn in Hrank |- *; lia) | (cbn in Hrank |- *; lia) | ].
      eapply EqVal_headred_expand;
        [ exact HRJ | exact HRJ' | exact DRIVE | exact DRIVE' | ].
      eapply (@EqVal_app_transport _ Δ (Core.app d[σ] P0) (Core.app d[σ'] N0)
                (Core.app (Core.app (Core.app C[σ] a[σ]) b[σ]) p[σ])
                u v_sel a0 (app fd u_sel)
                (wt_Selection_abs WTd Sel) WT hUcT);
        [ exact Caf | exact LEu_vsel | exact VTgoal | exact EAgoal ].
Qed.

(** [c_tid] congruence.  Unlike [sc_tpi] this needs no [semantic_typing] of the
    primed components: the primed side's [ValTyId] record is read off the
    component [semantic_conv2]s via [EqVal_Val2], with the two endpoints
    transported from [A[σ]] to [A'[σ]] by [Val_EqVal_fwd].  The [EqValTy] that
    transport needs is [SCA] taken at fuel [S RB] rather than [RB] -- at [S RB]
    the [rk tuniv = 1] boundary that forces the [rk_bot_inv] dodge below is not
    in the way. *)
Lemma sc_tid (A A' a a' b b' : Tm n) :
  typing Γ A Core.tuniv -> typing Γ a A -> typing Γ b A ->
  conv Γ A A' Core.tuniv -> conv Γ a a' A -> conv Γ b b' A ->
  semantic_typing Γ A Core.tuniv ->
  semantic_typing Γ a A ->
  semantic_typing Γ b A ->
  semantic_conv2 Γ A A' Core.tuniv ->
  semantic_conv2 Γ a a' A ->
  semantic_conv2 Γ b b' A ->
(* ------------------------- *)
  semantic_conv2 Γ (Core.tid A a b) (Core.tid A' a' b') Core.tuniv.
Proof.
  move=> TA Ta Tb cA ca cb STA STa STb SCA SCa SCb.
  (* the primed endpoints are typed at the *primed* domain *)
  have TA' : typing Γ A' Core.tuniv := proj2 (conv_typing cA).
  have Ta' : typing Γ a' A'
    by (eapply t_conv; [ exact (proj2 (conv_typing ca)) | exact cA ]).
  have Tb' : typing Γ b' A'
    by (eapply t_conv; [ exact (proj2 (conv_typing cb)) | exact cA ]).
  move=> ρ m Δ σ TS FR VS CΔ u a0 WT evId evU0.
  have Vρ : valid_env ρ := fits_valid_env FR.
  have evU : EvalRel Core.tuniv ρ tuniv by (cbn; apply le_refl).
  have TAs : typing Δ A[σ] Core.tuniv
    by (move: (substitution_tm _ _ _ _ _ TA TS CΔ) => hh; cbn in hh; exact hh).
  have TA's : typing Δ A'[σ] Core.tuniv
    by (move: (substitution_tm _ _ _ _ _ TA' TS CΔ) => hh; cbn in hh; exact hh).
  have Ta's : typing Δ a'[σ] A'[σ]
    by (eapply substitution_tm; [ exact Ta' | exact TS | exact CΔ ]).
  have Tb's : typing Δ b'[σ] A'[σ]
    by (eapply substitution_tm; [ exact Tb' | exact TS | exact CΔ ]).
  have cAs : conv Δ A[σ] A'[σ] Core.tuniv
    := substitution_conv Γ A A' Core.tuniv Δ σ cA TS CΔ.
  have cas : conv Δ a[σ] a'[σ] A[σ]
    := substitution_conv Γ a a' A Δ σ ca TS CΔ.
  have cbs : conv Δ b[σ] b'[σ] A[σ]
    := substitution_conv Γ b b' A Δ σ cb TS CΔ.
  move=> RB Hrank. destruct RB; [ exact I | ].
  have evId0 := evId. cbn in evId.
  destruct u as [ | | | | | | | t v w | | | | ]; try done.
  { (* u = bot *) apply EqVal_Bot. }
  move: evId => [Vid [evAt [evav evbw]]].
  have Eatu : a0 = tuniv by (inversion WT; auto). subst a0.
  have HrkT : rk t < RB by (cbn in Hrank; lia).
  have HrkV : rk v < RB by (cbn in Hrank; lia).
  have HrkW : rk w < RB by (cbn in Hrank; lia).
  (* the unprimed side: [st_tid_Val_edge] on the diagonal [σ' := σ] *)
  have VMv : Val (S RB) Δ (Core.tid A a b)[σ] Core.tuniv[σ] WT.
  { eapply st_tid_Val_edge with (σ' := σ); try eassumption.
    - exact (ConvSub_refl TS).
    - exact (ValSub_EqValSub VS). }
  rewrite Val_tuniv in VMv.
  (* the component equalities *)
  have eqA := SCA ρ m Δ σ TS FR VS CΔ t tuniv (wt_tid_dom WT) evAt evU.
  have eqL := SCa ρ m Δ σ TS FR VS CΔ v t (wt_tid_lhs WT) evav evAt.
  have eqR := SCb ρ m Δ σ TS FR VS CΔ w t (wt_tid_rhs WT) evbw evAt.
  have eqLhs : EqVal RB Δ a[σ] a'[σ] A[σ] (wt_tid_lhs WT)
    by (apply eqL; cbn in Hrank |- *; lia).
  have eqRhs : EqVal RB Δ b[σ] b'[σ] A[σ] (wt_tid_rhs WT)
    by (apply eqR; cbn in Hrank |- *; lia).
  (* the domain sits at [tuniv]: at fuel [RB] the [rk tuniv = 1] boundary needs
     the [rk_bot_inv] dodge, exactly as in [st_tid_EqVal_edge] *)
  have eqDom : EqVal RB Δ A[σ] A'[σ] Core.tuniv (wt_tid_dom WT).
  { destruct (le_lt_dec 2 RB) as [HRB|HRB].
    - eapply EqVal_irr; eapply eqA; cbn in Hrank |- *; lia.
    - have Et : t = bot by (apply rk_bot_inv; cbn in Hrank; lia).
      move: (wt_tid_dom WT). rewrite Et. move=> ww. apply EqVal_Bot. }
  (* ... but at fuel [S RB] there is no boundary, which is what gives the
     [EqValTy] used to retype the primed endpoints *)
  have eqTyA : EqValTy RB Δ A[σ] A'[σ] (wt_tid_dom WT).
  { have hh : EqVal (S RB) Δ A[σ] A'[σ] Core.tuniv (wt_tid_dom WT)
      by (apply eqA; cbn in Hrank |- *; lia).
    rewrite EqVal_tuniv in hh. exact (proj2 (proj2 hh)). }
  (* the primed side's record, read off the component equalities *)
  have VNv : Val (S RB) Δ (Core.tid A' a' b')[σ] Core.tuniv[σ] WT.
  { rewrite Val_tuniv. rewrite ValTy_tid.
    exists A'[σ]. exists a'[σ]. exists b'[σ].
    split; [ apply ms_refl | ].
    split; [ exact TA's | ]. split; [ exact Ta's | ]. split; [ exact Tb's | ].
    split; [ exact (wt_valid_tm WT) | ].
    split; [ eapply EqVal_Val2; exact eqDom | ].
    split.
    - eapply Val_EqVal_fwd;
        [ exact HrkV | exact HrkT | exact cAs
        | eapply EqVal_Val2; exact eqLhs | exact eqTyA ].
    - eapply Val_EqVal_fwd;
        [ exact HrkW | exact HrkT | exact cAs
        | eapply EqVal_Val2; exact eqRhs | exact eqTyA ]. }
  rewrite Val_tuniv in VNv.
  rewrite EqVal_tuniv.
  split; [ exact VMv | ]. split; [ exact VNv | ].
  rewrite EqValTy_tid.
  split; [ exact VMv | ]. split; [ exact VNv | ].
  exists A[σ]. exists a[σ]. exists b[σ]. split; [ apply ms_refl | ].
  exists A'[σ]. exists a'[σ]. exists b'[σ]. split; [ apply ms_refl | ].
  split; [ exact cAs | ]. split; [ exact cas | ]. split; [ exact cbs | ].
  split; [ exact (wt_valid_tm WT) | ].
  split; [ exact eqDom | ].
  split; [ exact eqLhs | exact eqRhs ].
Qed.

(** [c_rfl] congruence.  A near-clone of [st_rfl_EqVal_edge] with the second
    substitution replaced by the second *term*: there the right-hand side was
    [rfl a[σ']] related to [rfl a[σ]] by [subst_conv_cross], here it is
    [rfl a'[σ]] related by the substituted [conv Γ a a' A].  Both live at the
    *unprimed* identity type [(tid A a a)[σ]], so [t_rfl] on the right has to be
    retyped through the [c_tid] congruence. *)
Lemma sc_rfl (A a a' : Tm n) :
  typing Γ A Core.tuniv -> typing Γ a A -> conv Γ a a' A ->
  semantic_typing Γ A Core.tuniv ->
  semantic_typing Γ a A ->
  semantic_conv2 Γ a a' A ->
(* ------------------------- *)
  semantic_conv2 Γ (Core.rfl a) (Core.rfl a') (Core.tid A a a).
Proof.
  move=> TA Ta ca STA STa SCa.
  have Ta' : typing Γ a' A := proj2 (conv_typing ca).
  move=> ρ m Δ σ TS FR VS CΔ u a0 WT evR evId.
  have Vρ : valid_env ρ := fits_valid_env FR.
  have TAs : typing Δ A[σ] Core.tuniv
    by (move: (substitution_tm _ _ _ _ _ TA TS CΔ) => hh; cbn in hh; exact hh).
  have Tas : typing Δ a[σ] A[σ] by (eapply substitution_tm; [ exact Ta | exact TS | exact CΔ ]).
  have Ta's : typing Δ a'[σ] A[σ] by (eapply substitution_tm; [ exact Ta' | exact TS | exact CΔ ]).
  have cas : conv Δ a[σ] a'[σ] A[σ] := substitution_conv Γ a a' A Δ σ ca TS CΔ.
  (* the two identity types agree, which is how the right [rfl] gets retyped *)
  have convIds : conv Δ (Core.tid A[σ] a[σ] a[σ]) (Core.tid A[σ] a'[σ] a'[σ]) Core.tuniv
    by (eapply c_tid;
          [ exact TAs | exact Tas | exact Tas | apply c_refl; exact TAs
          | exact cas | exact cas ]).
  have TRs : typing Δ (Core.rfl a[σ]) (Core.tid A[σ] a[σ] a[σ])
    by (eapply t_rfl; [ exact TAs | exact Tas ]).
  have TRs' : typing Δ (Core.rfl a'[σ]) (Core.tid A[σ] a[σ] a[σ])
    by (eapply t_conv;
          [ eapply t_rfl; [ exact TAs | exact Ta's ] | apply c_sym; exact convIds ]).
  have evId0 := evId. cbn in evR, evId.
  move=> RB Hrank. destruct RB; [ exact I | ].
  destruct a0 as [ | | | | | | | t v w | | | | ]; try done.
  destruct u as [ | | | | | | | | ww | | | ]; try done.
  move: evId => [Vid [evAt [evav evaw]]].
  rewrite EqVal_rfl.
  have VTy : Val (S RB) Δ (Core.tid A a a)[σ] Core.tuniv[σ] (wt_rfl_ty WT).
  { eapply st_tid_Val_edge with (σ' := σ);
      [ exact TA | exact Ta | exact Ta | exact STA | exact STa | exact STa
      | exact TS | exact TS | exact (ConvSub_refl TS) | exact FR | exact VS
      | exact VS | exact (ValSub_EqValSub VS) | exact CΔ | exact evId0
      | cbn; apply le_refl; done
      | cbn in Hrank |- *; lia ]. }
  have [valWit _] :=
    STa ρ m Δ σ σ TS TS (ConvSub_refl TS) FR VS VS (ValSub_EqValSub VS) CΔ
        ww t (wt_rfl_wit WT) evR evAt.
  have VW : Val RB Δ a[σ] A[σ] (wt_rfl_wit WT)
    by (eapply valWit; cbn in Hrank |- *; lia).
  have eqWit := SCa ρ m Δ σ TS FR VS CΔ ww t (wt_rfl_wit WT) evR evAt.
  have EW : EqVal RB Δ a[σ] a'[σ] A[σ] (wt_rfl_wit WT)
    by (eapply eqWit; cbn in Hrank |- *; lia).
  have EWs : EqVal RB Δ a'[σ] a[σ] A[σ] (wt_rfl_wit WT)
    by (eapply EqVal_sym; [ cbn in Hrank |- *; lia | cbn in Hrank |- *; lia | exact EW ]).
  have VW' : Val RB Δ a'[σ] A[σ] (wt_rfl_wit WT) := EqVal_Val2 EW.
  split; [ eapply Val_ValTy; exact VTy | ].
  have IdM : ValId RB Δ (Core.rfl a[σ]) (Core.tid A a a)[σ] WT.
  { exists A[σ]. exists a[σ]. exists a[σ]. split; [ apply ms_refl | ].
    exists a[σ]. split; [ apply ms_refl | ].
    split; [ apply c_refl; exact TRs | ].
    split; [ apply c_refl; exact Tas | ].
    split; [ apply c_refl; exact Tas | ].
    split; [ exact VW | ].
    split; [ eapply Val_EqVal; exact VW | eapply Val_EqVal; exact VW ]. }
  have IdN : ValId RB Δ (Core.rfl a'[σ]) (Core.tid A a a)[σ] WT.
  { exists A[σ]. exists a[σ]. exists a[σ]. split; [ apply ms_refl | ].
    exists a'[σ]. split; [ apply ms_refl | ].
    split; [ apply c_refl; exact TRs' | ].
    split; [ apply c_sym; exact cas | ].
    split; [ apply c_sym; exact cas | ].
    split; [ exact VW' | ].
    split; [ exact EWs | exact EWs ]. }
  split; [ exact IdM | ]. split; [ exact IdN | ].
  split; [ exact IdM | ]. split; [ exact IdN | ].
  exists a[σ]. exists a'[σ]. split; [ apply ms_refl | ]. split; [ apply ms_refl | ].
  exists A[σ]. exists a[σ]. exists a[σ]. split; [ apply ms_refl | ].
  split; [ exact cas | exact EW ].
Qed.

(** J-beta.  Exactly the [sc_ncase_Z] shape: the two sides sit at the *same*
    type, [hr_jcase] is a single head step, so the whole thing is [st_jcase] on
    the diagonal followed by [EqVal_headred_contract]. *)
Lemma sc_jcase_beta (A a0 C d : Tm n) :
  typing Γ A Core.tuniv -> typing Γ a0 A ->
  typing Γ C (motive_ty A) -> typing Γ d (base_ty A C) ->
  semantic_typing Γ A Core.tuniv ->
  semantic_typing Γ a0 A ->
  semantic_typing Γ C (motive_ty A) ->
  semantic_typing Γ d (base_ty A C) ->
(* ------------------------- *)
  semantic_conv2 Γ (Core.jcase C d (Core.rfl a0)) (Core.app d a0)
    (Core.app (Core.app (Core.app C a0) a0) (Core.rfl a0)).
Proof.
  move=> TA Ta0 TC Td STA STa0 STC STd.
  have TR : typing Γ (Core.rfl a0) (Core.tid A a0 a0)
    by (eapply t_rfl; [ exact TA | exact Ta0 ]).
  have STR : semantic_typing Γ (Core.rfl a0) (Core.tid A a0 a0)
    by (eapply st_rfl; [ exact TA | exact Ta0 | exact STA | exact STa0 ]).
  have TJ : typing Γ (Core.jcase C d (Core.rfl a0))
              (Core.app (Core.app (Core.app C a0) a0) (Core.rfl a0))
    by (eapply t_jcase;
        [ exact TA | exact Ta0 | exact Ta0 | exact TC | exact Td | exact TR ]).
  have STJ : semantic_typing Γ (Core.jcase C d (Core.rfl a0))
               (Core.app (Core.app (Core.app C a0) a0) (Core.rfl a0))
    by (eapply st_jcase;
        [ exact TA | exact Ta0 | exact Ta0 | exact TC | exact Td | exact TR
        | exact STA | exact STa0 | exact STa0 | exact STC | exact STd | exact STR ]).
  have CJ : conv Γ (Core.jcase C d (Core.rfl a0)) (Core.app d a0)
              (Core.app (Core.app (Core.app C a0) a0) (Core.rfl a0))
    by (eapply c_jcase_beta; [ exact TA | exact Ta0 | exact TC | exact Td ]).
  move=> ρ m Δ σ TS FR VS CD u a WT evJ evT RB Hrank.
  have eqJ :=
    proj2 (STJ ρ m Δ σ σ TS TS (ConvSub_refl TS) FR VS VS (ValSub_EqValSub VS)
             CD u a WT evJ evT).
  have CJS : conv Δ (Core.jcase C d (Core.rfl a0))[σ] ((Core.app d a0)[σ])
                    ((Core.app (Core.app (Core.app C a0) a0) (Core.rfl a0))[σ])
    by (eapply substitution_conv; [ exact CJ | exact TS | exact CD ]).
  have CreflS : conv Δ (Core.jcase C d (Core.rfl a0))[σ]
                       (Core.jcase C d (Core.rfl a0))[σ]
                       ((Core.app (Core.app (Core.app C a0) a0) (Core.rfl a0))[σ])
    by (apply c_refl; eapply substitution_tm; [ exact TJ | exact TS | exact CD ]).
  eapply EqVal_headred_contract.
  - apply ms_refl.
  - eapply ms_trans; [ apply hr_jcase | apply ms_refl ].
  - exact CreflS.
  - apply c_sym; exact CJS.
  - exact (eqJ RB Hrank).
Qed.

(** Congruence of the [J] eliminator.  The same shape as [st_jcase]'s [EqVal]
    conjunct, with the primed *terms* in place of a second substitution -- so
    everything lives at one [σ] and no cross-substitution transport is needed.
    [jcase_motive_EqVal] and [jcase_type_spine] are reused unchanged: both
    speak about the *unprimed* spine, which is the goal's type. *)
Lemma sc_jcase (A a b C C' d d' p p' : Tm n) :
  typing Γ A Core.tuniv -> typing Γ a A -> typing Γ b A ->
  typing Γ C (motive_ty A) -> typing Γ d (base_ty A C) ->
  typing Γ p (Core.tid A a b) ->
  conv Γ C C' (motive_ty A) -> conv Γ d d' (base_ty A C) ->
  conv Γ p p' (Core.tid A a b) ->
  semantic_typing Γ A Core.tuniv ->
  semantic_typing Γ a A ->
  semantic_typing Γ b A ->
  semantic_typing Γ C (motive_ty A) ->
  semantic_typing Γ d (base_ty A C) ->
  semantic_typing Γ p (Core.tid A a b) ->
  semantic_conv2 Γ C C' (motive_ty A) ->
  semantic_conv2 Γ d d' (base_ty A C) ->
  semantic_conv2 Γ p p' (Core.tid A a b) ->
(* ------------------------- *)
  semantic_conv2 Γ (Core.jcase C d p) (Core.jcase C' d' p')
    (Core.app (Core.app (Core.app C a) b) p).
Proof.
  move=> TA Ta Tb TC Td Tp cC cd cp STA STa STb STC STd STp SCC SCd SCp.
  move=> ρ m Δ σ TS Fρ VS CΔ u a0 WT evJ evT RB Hrank.
  have Vρ : valid_env ρ := fits_valid_env Fρ.
  have CSd : ConvSub Δ Γ σ σ := ConvSub_refl TS.
  have EVSd : EqValSub Δ Γ σ σ ρ := ValSub_EqValSub VS.
  have evU : EvalRel Core.tuniv ρ tuniv by (cbn; apply le_refl).
  destruct (is_bot u) eqn:Hu.
  { have Eu : u = bot by (apply is_bot_eq; rewrite Hu). subst u. apply EqVal_Bot. }
  (* ---- the proof's value drives both eliminators ---- *)
  cbn in evJ. move: evJ => [wp [evP Ebr]].
  destruct wp as [ | | | | | | | | w' | | | ]; try done.
  { move: Ebr => [_ /le_bot_inv Eu]. subst u. by rewrite /= in Hu. }
  have ITp : InvTyped Γ p (Core.tid A a b) ρ := typing_EvalRel Tp Fρ.
  have [pv [ap [WTp [LEp [evPbig evIdCode]]]]] := ITp _ evP.
  move: (le_rfl_inv LEp) => [w'' [Epv Lw'w'']]. subst pv.
  destruct ap as [ | | | | | | | t up vp | | | | ];
    try solve [ cbn in evIdCode; done | (move: (wt_bot_inv WTp); discriminate) ].
  have evIdC := evIdCode. cbn in evIdC.
  move: evIdC => [Vid [evA_t [eva_up evb_vp]]].
  (* ---- the two witnesses, from [SCp]'s [EqValId] ---- *)
  have eqP := SCp ρ m Δ σ TS Fρ VS CΔ (rfl w'') (tid t up vp) WTp evPbig evIdCode.
  have eqPk : forall k, max (rk (rfl w'')) (rk (tid t up vp)) < k ->
      ValTy k Δ (Core.tid A a b)[σ] (wt_rfl_ty WTp)
      /\ ValId k Δ p[σ] (Core.tid A a b)[σ] WTp
      /\ ValId k Δ p'[σ] (Core.tid A a b)[σ] WTp
      /\ EqValId k Δ p[σ] p'[σ] (Core.tid A a b)[σ] WTp.
  { move=> k Hk. have hh := eqP (S k) ltac:(lia). rewrite EqVal_rfl in hh. exact hh. }
  pose kP := S (max (rk (rfl w'')) (rk (tid t up vp))).
  have HkP : max (rk (rfl w'')) (rk (tid t up vp)) < kP by (unfold kP; lia).
  have [_ [IdP [IdP' EqIdP]]] := eqPk kP HkP.
  move: IdP =>
    [A1 [a1 [b1 [HRid1 [P0 [HRp [cvPp [cvPa [cvPb [VP0 [EP0a EP0b]]]]]]]]]]].
  cbn in HRid1. have [Z1 [Z2 Z3]] := HeadRed_tid_eq HRid1. subst A1 a1 b1.
  move: IdP' =>
    [A2 [a2 [b2 [HRid2 [P0' [HRp' [cvPp' [cvPa' [cvPb' [VP0' [EP0a' EP0b']]]]]]]]]]].
  cbn in HRid2. have [Y1 [Y2 Y3]] := HeadRed_tid_eq HRid2. subst A2 a2 b2.
  move: EqIdP =>
    [_ [_ [M0 [N0 [HRm [HRn [A3 [a3 [b3 [HRid3 [cvMN EqMN]]]]]]]]]]].
  cbn in HRid3. have [X1 [X2 X3]] := HeadRed_tid_eq HRid3. subst A3 a3 b3.
  have EM : M0 = P0 by (eapply HeadRed_rfl_det; [ exact HRm | exact HRp ]).
  have EN : N0 = P0' by (eapply HeadRed_rfl_det; [ exact HRn | exact HRp' ]).
  subst M0 N0.
  (* the witness data at every fuel *)
  have IdPk : forall k, max (rk (rfl w'')) (rk (tid t up vp)) < k ->
      Val k Δ P0 A[σ] (wt_rfl_wit WTp)
      /\ EqVal k Δ P0 a[σ] A[σ] (wt_rfl_wit WTp)
      /\ EqVal k Δ P0 b[σ] A[σ] (wt_rfl_wit WTp).
  { move=> k Hk. have [_ [Idk _]] := eqPk k Hk.
    move: Idk =>
      [B1 [c1 [e1 [HRk [Q [HRq [cq [cqa [cqb [VQ [EQa EQb]]]]]]]]]]].
    cbn in HRk. have [W1 [W2 W3]] := HeadRed_tid_eq HRk. subst B1 c1 e1.
    have EQ : Q = P0 by (eapply HeadRed_rfl_det; [ exact HRq | exact HRp ]).
    subst Q. split; [ exact VQ | split; [ exact EQa | exact EQb ] ]. }
  have EqPk : forall k, max (rk (rfl w'')) (rk (tid t up vp)) < k ->
      EqVal k Δ P0 P0' A[σ] (wt_rfl_wit WTp).
  { move=> k Hk. have [_ [_ [_ EqIdk]]] := eqPk k Hk.
    move: EqIdk =>
      [_ [_ [M1 [N1 [HRm1 [HRn1 [B2 [c2 [e2 [HRk2 [cv2 Eq2]]]]]]]]]]].
    cbn in HRk2. have [V1 [V2 V3]] := HeadRed_tid_eq HRk2. subst B2 c2 e2.
    have EM1 : M1 = P0 by (eapply HeadRed_rfl_det; [ exact HRm1 | exact HRp ]).
    have EN1 : N1 = P0' by (eapply HeadRed_rfl_det; [ exact HRn1 | exact HRp' ]).
    subst M1 N1. exact Eq2. }
  (* ---- the syntactic side of both drivers ---- *)
  have TAs : typing Δ A[σ] Core.tuniv
    by (move: (substitution_tm _ _ _ _ _ TA TS CΔ) => hh; cbn in hh; exact hh).
  have Tas : typing Δ a[σ] A[σ]
    by (eapply substitution_tm; [ exact Ta | exact TS | exact CΔ ]).
  have Tbs : typing Δ b[σ] A[σ]
    by (eapply substitution_tm; [ exact Tb | exact TS | exact CΔ ]).
  have TCs : typing Δ C[σ] (motive_ty A[σ]).
  { move: (substitution_tm _ _ _ _ _ TC TS CΔ) => hh.
    rewrite subst_motive_ty in hh. exact hh. }
  have Tds : typing Δ d[σ] (base_ty A[σ] C[σ]).
  { move: (substitution_tm _ _ _ _ _ Td TS CΔ) => hh.
    rewrite subst_base_ty in hh. exact hh. }
  have Tps : typing Δ p[σ] (Core.tid A[σ] a[σ] b[σ]).
  { move: (substitution_tm _ _ _ _ _ Tp TS CΔ) => hh. cbn in hh. exact hh. }
  have TP0 : typing Δ P0 A[σ] := proj1 (conv_typing cvPa).
  have TP0' : typing Δ P0' A[σ] := proj1 (conv_typing cvPa').
  have cCs : conv Δ C[σ] C'[σ] (motive_ty A[σ]).
  { move: (substitution_conv _ _ _ _ _ σ cC TS CΔ) => hh.
    rewrite subst_motive_ty in hh. exact hh. }
  have cds : conv Δ d[σ] d'[σ] (base_ty A[σ] C[σ]).
  { move: (substitution_conv _ _ _ _ _ σ cd TS CΔ) => hh.
    rewrite subst_base_ty in hh. exact hh. }
  have cps : conv Δ p[σ] p'[σ] (Core.tid A[σ] a[σ] b[σ]).
  { move: (substitution_conv _ _ _ _ _ σ cp TS CΔ) => hh. cbn in hh. exact hh. }
  have TC's : typing Δ C'[σ] (motive_ty A[σ]) := proj2 (conv_typing cCs).
  have Td's : typing Δ d'[σ] (base_ty A[σ] C'[σ]).
  { eapply t_conv; [ exact (proj2 (conv_typing cds)) | ].
    eapply base_ty_conv; [ exact TAs | exact TCs | exact TC's | exact cCs ]. }
  have Tp's : typing Δ p'[σ] (Core.tid A[σ] a[σ] b[σ]) := proj2 (conv_typing cps).
  have DRIVE : conv Δ (Core.jcase C[σ] d[σ] p[σ]) (Core.app d[σ] P0)
                 (Core.app (Core.app (Core.app C[σ] a[σ]) b[σ]) p[σ])
    by (eapply jcase_drive_conv;
        [ exact TAs | exact TP0 | exact Tas | exact Tbs | exact TCs | exact Tds
        | exact Tps | exact cvPa | exact cvPb | exact cvPp ]).
  have HRJ : HeadRed (Core.jcase C[σ] d[σ] p[σ]) (Core.app d[σ] P0)
    by (eapply HeadRed_jcase; exact HRp).
  have DRIVE' : conv Δ (Core.jcase C'[σ] d'[σ] p'[σ]) (Core.app d'[σ] P0')
                  (Core.app (Core.app (Core.app C[σ] a[σ]) b[σ]) p[σ]).
  { eapply c_conv.
    - eapply jcase_drive_conv;
        [ exact TAs | exact TP0' | exact Tas | exact Tbs | exact TC's
        | exact Td's | exact Tp's | exact cvPa' | exact cvPb' | exact cvPp' ].
    - apply c_sym. eapply motive_app_conv;
        [ exact TAs | exact Tas | exact Tbs | exact TCs | exact TC's
        | exact Tps | exact cCs | exact cps ]. }
  have HRJ' : HeadRed (Core.jcase C'[σ] d'[σ] p'[σ]) (Core.app d'[σ] P0')
    by (eapply HeadRed_jcase; exact HRp').
  (* ---- [d]'s value edge at the witness (as in [st_jcase]) ---- *)
  have Vw'  : valid w'  by (move: (EvalRel_valid evP); cbn; done).
  have Vw'' : valid w'' by (move: (EvalRel_valid evPbig); cbn; done).
  have ITd : InvTyped Γ d (base_ty A C) ρ := typing_EvalRel Td Fρ.
  have [vd [ad [WTd [LEd [evDbig evBase]]]]] := ITd _ Ebr.
  unfold singleton in LEd. rewrite Hu in LEd.
  have [g [Evd LEfun]] := le_abs_inv LEd. subst vd.
  destruct ad as [ | | | | | bd fd | | | | | | ];
    try solve [ exfalso; clear -WTd; inversion WTd ].
  have evBaseC := evBase. rewrite /base_ty in evBaseC. cbn in evBaseC.
  move: evBaseC => [Vbd [Vfd [evA_bd [ad2 [evA_bd2 EBfun]]]]].
  have Vg : valid_fun g := proj1 (andb_prop _ _ (wt_valid_tm WTd)).
  have [u_sel [v_sel [Sel [Le_usel Eq_vsel]]]] := selectionBelow Vg Vw'.
  have [WTu_sel WTv_sel] : wt u_sel bd /\ wt v_sel (app fd u_sel).
  { eapply wt_Selection_cod;
      [ exact (wt_abs_ty WTd) | exact (wt_abs_inv1 WTd)
      | move=> ui vi Hin; exact (wt_abs_inv2 WTd Hin erefl)
      | exact Vg | exact Sel ]. }
  have Vusel : valid u_sel := wt_valid_tm WTu_sel.
  have LEu_vsel : le u v_sel.
  { rewrite le_fun_cons in LEfun.
    have LEua := proj1 (andb_prop _ _ LEfun).
    rewrite Eq_vsel in LEua. exact LEua. }
  have Wt_t  : wt t tuniv := wt_ty_tuniv (wt_rfl_wit WTp).
  have Wt_bd : wt bd tuniv := wt_tpi_dom (wt_abs_ty WTd).
  have Cbdt : compatible bd t
    by (eapply EvalRel_compatible; [ exact Vρ | exact evA_bd | exact evA_t ]).
  have hUlub : wt (lub bd t) tuniv := wt_lub Wt_bd Cbdt Wt_t.
  have evA_lub : EvalRel A ρ (lub bd t)
    := proj2 (EvalRel_compatible_lub Vρ evA_bd evA_t) _ erefl.
  have [valA_lub _] :=
    STA ρ m Δ σ σ TS TS CSd Fρ VS VS EVSd CΔ (lub bd t) tuniv hUlub evA_lub evU.
  have LEuselw'' : le u_sel w''
    by (eapply (@le_trans u_sel w' w'');
        [ exact Vusel | exact Vw' | exact Vw'' | exact Le_usel | exact Lw'w'' ]).
  have VargK : forall k,
      max (rk (lub bd t)) (rk tuniv) < k ->
      max (rk (rfl w'')) (rk (tid t up vp)) < k ->
      Val k Δ P0 A[σ] WTu_sel.
  { move=> k Hk1 Hk2.
    eapply (@Val_app_transport _ Δ P0 A[σ] u_sel w'' bd t
              (wt_rfl_wit WTp) WTu_sel hUlub);
      [ exact Cbdt | exact LEuselw'' | exact (valA_lub k Hk1)
      | exact (proj1 (IdPk k Hk2)) ]. }
  pose RBf := S (max (max (rk (abs g)) (rk (tpi bd fd)))
                     (max (max (rk u) (rk a0))
                          (max (rk (rfl w'')) (rk (tid t up vp))))).
  have RKlub : rk (lub bd t) <= max (rk bd) (rk t) := rk_lub bd t.
  have RKbd : rk bd < rk (tpi bd fd) by (cbn; lia).
  have RKt  : rk t < rk (tid t up vp) by (cbn; lia).
  have RKpi : 1 <= rk (tpi bd fd) by (cbn; lia).
  have RKtu : rk tuniv = 1 by reflexivity.
  have HfD : max (rk (abs g)) (rk (tpi bd fd)) < S RBf by (unfold RBf; lia).
  have HfA : max (rk (lub bd t)) (rk tuniv) < RBf by (unfold RBf; lia).
  have HfP : max (rk (rfl w'')) (rk (tid t up vp)) < RBf by (unfold RBf; lia).
  have RKvsel : rk v_sel <= rk_fun g := rk_Selection_val Sel.
  have RKg : rk_fun g < rk (abs g) by (cbn; lia).
  have RKfd : rk_fun fd < rk (tpi bd fd) by (cbn; lia).
  have RKcod : rk (app fd u_sel) <= rk_fun fd := rk_app fd u_sel.
  have RKlubT : rk (lub a0 (app fd u_sel)) <= max (rk a0) (rk (app fd u_sel))
    := rk_lub a0 (app fd u_sel).
  (* the core: [d]'s cross edge, then [d'[σ]]'s argument edge *)
  have eqDbig := SCd ρ m Δ σ TS Fρ VS CΔ (abs g) (tpi bd fd) WTd evDbig evBase.
  have ED := eqDbig (S RBf) HfD. rewrite EqVal_abs in ED.
  move: ED => [_ [_ [VPid' EPid]]].
  move: EPid => [A0e2 [B0e2 [HRpi2 [CTpi2 paev]]]].
  rewrite subst_base_ty /base_ty in HRpi2.
  have [Ea2 Eb2] := HeadRed_tpi_eq HRpi2. subst A0e2 B0e2.
  move: VPid' => [A0e3 [B0e3 [HRpi3 [CTpi3 [pav' pae']]]]].
  rewrite subst_base_ty /base_ty in HRpi3.
  have [Ea3 Eb3] := HeadRed_tpi_eq HRpi3. subst A0e3 B0e3.
  have EqPsel : EqVal RBf Δ P0 P0' A[σ] WTu_sel.
  { eapply (@EqVal_app_transport _ Δ P0 P0' A[σ] u_sel w'' bd t
              (wt_rfl_wit WTp) WTu_sel hUlub);
      [ exact Cbdt | exact LEuselw'' | exact (valA_lub RBf HfA)
      | exact (EqPk RBf HfP) ]. }
  have EA1 := paev u_sel v_sel Sel WTu_sel P0 TP0 (VargK RBf HfA HfP).
  have EA2 := pae' u_sel v_sel Sel WTu_sel P0 P0' cvMN EqPsel.
  have EqB : (Core.app (Core.app (Core.app (C[σ])⟨↑⟩ (Core.var var_zero))
                          (Core.var var_zero))
                (Core.rfl (Core.var var_zero)))[P0..]
           = Core.app (Core.app (Core.app C[σ] P0) P0) (Core.rfl P0)
    by (asimpl; reflexivity).
  rewrite EqB in EA1. rewrite EqB in EA2.
  have EAcore : EqVal RBf Δ (Core.app d[σ] P0) (Core.app d'[σ] P0')
                  (Core.app (Core.app (Core.app C[σ] P0) P0) (Core.rfl P0))
                  (wt_Selection_abs WTd Sel).
  { eapply (EqVal_trans (M2 := Core.app d'[σ] P0));
      [ (unfold RBf; lia) | (unfold RBf; lia) | exact EA1 | exact EA2 ]. }
  (* ---- the goal type at the edge's codomain code ---- *)
  have Eaw'' : EvalRel a ρ w''
    by (eapply EvalRel_down;
        [ exact Vρ | exact Vw'' | exact eva_up | exact (wt_rfl_le_lhs WTp) ]).
  have Ebw'' : EvalRel b ρ w''
    by (eapply EvalRel_down;
        [ exact Vρ | exact Vw'' | exact evb_vp | exact (wt_rfl_le_rhs WTp) ]).
  have [xs [WTxs [LExs EBxs]]] :
    exists xs (_ : wt xs ad2), le xs u_sel
      /\ EvalRel (Core.app (Core.app (Core.app C⟨↑⟩ (Core.var var_zero))
                              (Core.var var_zero))
                    (Core.rfl (Core.var var_zero)))
           (xs .: ρ) (app fd u_sel)
    by (apply (EBfun u_sel (app fd u_sel) Vusel); reflexivity).
  have Vxs : valid xs := wt_valid_tm WTxs.
  have LExsw'' : le xs w''
    by (eapply (@le_trans xs u_sel w'');
        [ exact Vxs | exact Vusel | exact Vw'' | exact LExs | exact LEuselw'' ]).
  have evT_af :
    EvalRel (Core.app (Core.app (Core.app C a) b) p) ρ (app fd u_sel)
    by (eapply EvalRel_base_cod_spine;
        [ exact Vρ | exact Vxs | exact LExsw'' | exact Eaw'' | exact Ebw''
        | exact evPbig | exact EBxs ]).
  have Caf : compatible a0 (app fd u_sel)
    by (eapply EvalRel_compatible; [ exact Vρ | exact evT | exact evT_af ]).
  have Waf : wt (app fd u_sel) tuniv := wt_ty_tuniv (wt_Selection_abs WTd Sel).
  have hUcT : wt (lub a0 (app fd u_sel)) tuniv
    := wt_lub (wt_ty_tuniv WT) Caf Waf.
  have evT_lub :
    EvalRel (Core.app (Core.app (Core.app C a) b) p) ρ (lub a0 (app fd u_sel))
    := proj2 (EvalRel_compatible_lub Vρ evT evT_af) _ erefl.
  have Bfa : is_bot (app fd u_sel) = false.
  { destruct (is_bot (app fd u_sel)) eqn:Hb; [ | reflexivity ].
    exfalso.
    have E : app fd u_sel = bot by (apply is_bot_eq; rewrite Hb).
    move: WTv_sel. rewrite E => WTr.
    move: (wt_bot_inv WTr) => Ev. rewrite Ev in LEu_vsel.
    move: LEu_vsel => /le_bot_inv Eu. subst u. by rewrite /= in Hu. }
  have [ws1 [ws2 [ws3 [evC3s [Ls3 [Ls2 [Ls1 [evas3 [evbs2 evps1]]]]]]]]] :=
    EvalRel_base_cod_spine_codes Vρ Vxs LExsw'' Eaw'' Ebw'' evPbig Bfa EBxs.
  have EQTY : forall kk, max (rk (app fd u_sel)) (rk tuniv) < kk ->
      EqVal kk Δ (Core.app (Core.app (Core.app C[σ] P0) P0) (Core.rfl P0))
                 (Core.app (Core.app (Core.app C[σ] a[σ]) b[σ]) p[σ])
                 Core.tuniv Waf.
  { eapply jcase_motive_EqVal;
      [ exact TA | exact Ta | exact Tb | exact TC | exact Tp
      | exact STA | exact STa | exact STb | exact STC | exact STp
      | exact TS | exact TS | exact CSd | exact Fρ | exact VS | exact VS
      | exact EVSd | exact CΔ | exact evPbig | exact evA_t
      | exact HRp | exact cvPa | exact cvPb | exact cvPp | exact IdPk
      | exact Bfa | exact evC3s | exact Ls3 | exact Ls2 | exact Ls1
      | exact evas3 | exact evbs2 | exact evps1 ]. }
  have ETY : EqValTy RBf Δ
      (Core.app (Core.app (Core.app C[σ] P0) P0) (Core.rfl P0))
      (Core.app (Core.app (Core.app C[σ] a[σ]) b[σ]) p[σ]) Waf.
  { have hh := EQTY (S RBf) ltac:(unfold RBf; lia).
    rewrite EqVal_tuniv in hh. exact (proj2 (proj2 hh)). }
  have CVTY : conv Δ
      (Core.app (Core.app (Core.app C[σ] P0) P0) (Core.rfl P0))
      (Core.app (Core.app (Core.app C[σ] a[σ]) b[σ]) p[σ]) Core.tuniv
    by (eapply motive_app_conv_witness;
        [ exact TAs | exact TP0 | exact Tas | exact Tbs | exact TCs | exact Tps
        | exact cvPa | exact cvPb | exact cvPp ]).
  have VTgoal : Val RBf Δ
      (Core.app (Core.app (Core.app C[σ] a[σ]) b[σ]) p[σ]) Core.tuniv hUcT.
  { eapply jcase_type_spine;
      [ exact TA | exact Ta | exact Tb | exact TC | exact Tp
      | exact STa | exact STb | exact STC | exact STp
      | exact TS | exact TS | exact CSd | exact Fρ | exact VS | exact VS
      | exact EVSd | exact CΔ | exact evT_lub | (unfold RBf; lia) ]. }
  have EAgoal : EqVal RBf Δ (Core.app d[σ] P0) (Core.app d'[σ] P0')
                  (Core.app (Core.app (Core.app C[σ] a[σ]) b[σ]) p[σ])
                  (wt_Selection_abs WTd Sel).
  { eapply (EqVal_EqVal_fwd
              (B := Core.app (Core.app (Core.app C[σ] a[σ]) b[σ]) p[σ]));
      [ (unfold RBf; lia) | (unfold RBf; lia) | exact CVTY | exact EAcore
      | exact ETY ]. }
  (* ---- finish ---- *)
  apply (EqVal_fuel_any (k := RBf) (k' := RB));
    [ (unfold RBf; lia) | (unfold RBf; lia)
    | (cbn in Hrank |- *; lia) | (cbn in Hrank |- *; lia) | ].
  eapply EqVal_headred_expand;
    [ exact HRJ | exact HRJ' | exact DRIVE | exact DRIVE' | ].
  eapply (@EqVal_app_transport _ Δ (Core.app d[σ] P0) (Core.app d'[σ] P0')
            (Core.app (Core.app (Core.app C[σ] a[σ]) b[σ]) p[σ])
            u v_sel a0 (app fd u_sel)
            (wt_Selection_abs WTd Sel) WT hUcT);
    [ exact Caf | exact LEu_vsel | exact VTgoal | exact EAgoal ].
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
  destruct u as [ | | | | | b f | | | | | | ]; try done.
  - (* u = bot: trivial *) apply Val_Bot.
  - (* u = tpi b f *)
    move: evAN => [Vb [Vf [evAdom [a' [evAdom' EFun]]]]].
    have Eatu : a = tuniv by (eapply wt_tpi_ty_tuniv; [ exact WT | exact evAB ]).
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
  destruct u as [ | | | | | b f | | | | | | ]; try done.
  - (* u = bot: trivial *) apply EqVal_Bot.
  - (* u = tpi b f *)
    move: evAN => [Vb [Vf [evAdom [a' [evAdom' EFun]]]]].
    have Eatu : a = tuniv by (eapply wt_tpi_ty_tuniv; [ exact WT | exact evAB ]). subst a.
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

(* The codomain's evaluation at the code [app f x]: the Sigma type's own
   [EvalRel_fun] edge, instantiated at the first component's code and folded
   back through the substitution ([EvalRel_subst1_backwards]).  This is Agda's
   [Sigma-edgewise] + [EvalRel-body-EvalFun] + [EvalRel-subst1-backward]
   chain, in one step. *)
Lemma sigma_cod_eval {q} (A0 : Tm q) (B0 : Tm (S q)) (M0 : Tm q) ρ b f x :
  valid_env ρ -> valid x ->
  EvalRel (Core.tsig A0 B0) ρ (tsig b f) ->
  EvalRel M0 ρ x ->
  EvalRel B0[M0..] ρ (app f x).
Proof.
  move=> Vρ Vx ESig EM.
  cbn in ESig. move: ESig => [Vb [Vf [EA [a' [EA' EFun]]]]].
  have [x0 [hx0 [Le0 EB0]]] := EFun x (app f x) Vx erefl.
  eapply EvalRel_subst1_backwards; [ exact Vρ | | exact EB0 ].
  eapply EvalRel_down;
    [ exact Vρ | eapply wt_valid_tm; exact hx0 | exact EM | exact Le0 ].
Qed.

(* ------------------------------------------------------------------
   Sigma formation.  A [tsig] type code carries the same table as a [tpi]
   one and [EvalRel (Core.tsig A B)] is *definitionally* [EvalRel
   (Core.tpi A B)] at the matching code ([EvalRel_tsig_tpi]), so the three
   Selection-indexed edges are the Pi ones, re-indexed through
   [wt_tsig_tpi].  The scripts below are [st_tpi_*_edge] verbatim.
   ------------------------------------------------------------------ *)
Lemma st_tsig_Val_edge (A : Tm n) (B : Tm (S n))
  (TA : typing Γ A Core.tuniv) (TB : typing (Γ ++ A) B Core.tuniv)
  (STA : semantic_typing Γ A Core.tuniv)
  (STB : semantic_typing (Γ ++ A) B Core.tuniv)
  ρ m (Δ : Ctx m) (σ σ' : Sub n m)
  (TS : typing_subst Δ σ Γ) (TS' : typing_subst Δ σ' Γ) (CS : ConvSub Δ Γ σ σ')
  (Fρ : fits Γ ρ) (VS : ValSub Δ Γ σ ρ) (VS' : ValSub Δ Γ σ' ρ)
  (EVS : EqValSub Δ Γ σ σ' ρ) (CΔ : ctx Δ) u a (WT : wt u a)
  (evAN : EvalRel (Core.tsig A B) ρ u) (evAB : EvalRel Core.tuniv ρ a) :
  forall RB, max (rk u) (rk a) < RB -> Val RB Δ (Core.tsig A B)[σ] Core.tuniv[σ] WT.
Proof.
  have Vρ : valid_env ρ := fits_valid_env Fρ.
  move: (substitution_tm _ _ _ _ _ TA TS CΔ) => TAs. cbn in TAs.
  have CE : ctx (Δ ++ A[σ]). eapply c_cons; eauto.
  have TSE : typing_subst (Δ ++ A[σ]) (⇑ σ) (Γ ++ A). eapply typing_subst_lift; eauto.
  have TBs : typing (Δ ++ A[σ]) B[⇑ σ] Core.tuniv.
  { have CC : typing (Δ ++ A[σ]) B[⇑ σ] Core.tuniv[⇑ σ].
    eapply substitution_tm; eauto. cbn in CC. auto. }
  have evU : EvalRel Core.tuniv ρ tuniv by (cbn; apply le_refl).
  have evAN0 := evAN.
  cbn in evAN.
  move=> RB Hrank. destruct RB; [ exact I | ].
  destruct u as [ | | | | | | | | | b f | | ]; try done.
  - (* u = bot *) apply Val_Bot.
  - (* u = tsig b f *)
    move: evAN => [Vb [Vf [evAdom [a' [evAdom' EFun]]]]].
    have Eatu : a = tuniv by (inversion WT; auto). subst a.
    have evANpi : EvalRel (Core.tpi A B) ρ (tpi b f) := EvalRel_tsig_tpi evAN0.
    have [valA _] :=
      STA ρ m Δ σ σ' TS TS' CS Fρ VS VS' EVS CΔ b tuniv (wt_tsig_dom WT) evAdom evU.
    rewrite Val_tuniv. rewrite ValTy_tsig. cbn [Rec.ValTySig].
    exists A[σ], B[⇑ σ].
    have valDom : Val RB Δ A[σ] Core.tuniv[σ] (wt_tsig_dom WT).
    { destruct (le_lt_dec 2 RB) as [HRB|HRB].
      - eapply Val_irr; eapply valA; cbn in Hrank |- *; lia.
      - have Eb : b = bot by (apply rk_bot_inv; cbn in Hrank; lia).
        move: (wt_tsig_dom WT). rewrite Eb. move=> w. apply Val_Bot. }
    repeat split;
      [ apply ms_refl | exact TAs | exact TBs | exact (wt_valid_tm WT)
      | exact valDom | | ].
    + eapply tpi_PiEdgeVal; (try eassumption); cbn in Hrank |- *; lia.
    + eapply tpi_PiEdgeEq; (try eassumption); cbn in Hrank |- *; lia.
Qed.

Lemma st_tsig_EqVal_edge (A : Tm n) (B : Tm (S n))
  (TA : typing Γ A Core.tuniv) (TB : typing (Γ ++ A) B Core.tuniv)
  (STA : semantic_typing Γ A Core.tuniv)
  (STB : semantic_typing (Γ ++ A) B Core.tuniv)
  ρ m (Δ : Ctx m) (σ σ' : Sub n m)
  (TS : typing_subst Δ σ Γ) (TS' : typing_subst Δ σ' Γ) (CS : ConvSub Δ Γ σ σ')
  (Fρ : fits Γ ρ) (VS : ValSub Δ Γ σ ρ) (VS' : ValSub Δ Γ σ' ρ)
  (EVS : EqValSub Δ Γ σ σ' ρ) (CΔ : ctx Δ) u a (WT : wt u a)
  (evAN : EvalRel (Core.tsig A B) ρ u) (evAB : EvalRel Core.tuniv ρ a) :
  forall RB, max (rk u) (rk a) < RB ->
    EqVal RB Δ (Core.tsig A B)[σ] (Core.tsig A B)[σ'] Core.tuniv[σ] WT.
Proof.
  have Vρ : valid_env ρ := fits_valid_env Fρ.
  have evU : EvalRel Core.tuniv ρ tuniv by (cbn; apply le_refl).
  have evAN0 := evAN.
  cbn in evAN.
  move=> RB Hrank. destruct RB; [ exact I | ].
  destruct u as [ | | | | | | | | | b f | | ]; try done.
  - (* u = bot *) apply EqVal_Bot.
  - (* u = tsig b f *)
    move: evAN => [Vb [Vf [evAdom [a' [evAdom' EFun]]]]].
    have Eatu : a = tuniv by (inversion WT; auto). subst a.
    have evANpi : EvalRel (Core.tpi A B) ρ (tpi b f) := EvalRel_tsig_tpi evAN0.
    have VMv : Val (S RB) Δ (Core.tsig A B)[σ] Core.tuniv[σ] WT.
    { eapply st_tsig_Val_edge; eassumption. }
    have VNv : Val (S RB) Δ (Core.tsig A B)[σ'] Core.tuniv[σ'] WT.
    { eapply st_tsig_Val_edge with (σ' := σ'); try eassumption.
      - exact (ConvSub_refl TS').
      - exact (ValSub_EqValSub VS'). }
    rewrite Val_tuniv in VMv. rewrite Val_tuniv in VNv.
    have convAA' : conv Δ A[σ] A[σ'] Core.tuniv := subst_conv_cross TA CΔ TS TS' CS.
    have codConv : conv (Δ ++ A[σ]) B[⇑ σ] B[⇑ σ'] Core.tuniv :=
      cod_subst_conv TA TB CΔ TS TS' CS.
    have [_ eqA] :=
      STA ρ m Δ σ σ' TS TS' CS Fρ VS VS' EVS CΔ b tuniv (wt_tsig_dom WT) evAdom evU.
    have eqDom : EqVal RB Δ A[σ] A[σ'] Core.tuniv (wt_tsig_dom WT).
    { destruct (le_lt_dec 2 RB) as [HRB|HRB].
      - eapply EqVal_irr; eapply eqA; cbn in Hrank |- *; lia.
      - have Eb : b = bot by (apply rk_bot_inv; cbn in Hrank; lia).
        move: (wt_tsig_dom WT). rewrite Eb. move=> w. apply EqVal_Bot. }
    rewrite EqVal_tuniv.
    split; [ exact VMv | ]. split; [ exact VNv | ].
    rewrite EqValTy_tsig. cbn [Rec.EqValTySig].
    split; [ exact VMv | ]. split; [ exact VNv | ].
    exists A[σ], B[⇑ σ]. split; [ apply ms_refl | ].
    exists A[σ'], B[⇑ σ']. split; [ apply ms_refl | ].
    split; [ exact convAA' | ].
    split; [ exact codConv | ].
    split; [ exact (wt_valid_tm WT) | ].
    split; [ exact eqDom | ].
    eapply tpi_PiEdgeEqTy; (try eassumption); cbn in Hrank |- *; lia.
Qed.

(* ------------------------------------------------------------------
   Pair introduction.  The type record is [st_tsig_Val_edge] at the pair's
   own type code; the two components are the IHs re-asked at the pair's
   component codes [x] and [app f x], the latter's type evaluation supplied
   by [sigma_cod_eval].
   ------------------------------------------------------------------ *)
Lemma st_mkpair_Val_edge (A : Tm n) (B : Tm (S n)) (M0 N0 : Tm n)
  (TA : typing Γ A Core.tuniv) (TB : typing (Γ ++ A) B Core.tuniv)
  (TM : typing Γ M0 A) (TN : typing Γ N0 B[M0..])
  (STA : semantic_typing Γ A Core.tuniv)
  (STB : semantic_typing (Γ ++ A) B Core.tuniv)
  (STM : semantic_typing Γ M0 A)
  (STN : semantic_typing Γ N0 B[M0..])
  ρ m (Δ : Ctx m) (σ σ' : Sub n m)
  (TS : typing_subst Δ σ Γ) (TS' : typing_subst Δ σ' Γ) (CS : ConvSub Δ Γ σ σ')
  (Fρ : fits Γ ρ) (VS : ValSub Δ Γ σ ρ) (VS' : ValSub Δ Γ σ' ρ)
  (EVS : EqValSub Δ Γ σ σ' ρ) (CΔ : ctx Δ) u a (WT : wt u a)
  (evP : EvalRel (Core.mkpair M0 N0) ρ u) (evS : EvalRel (Core.tsig A B) ρ a) :
  forall RB, max (rk u) (rk a) < RB ->
    Val RB Δ (Core.mkpair M0 N0)[σ] (Core.tsig A B)[σ] WT.
Proof.
  have Vρ : valid_env ρ := fits_valid_env Fρ.
  have TAs : typing Δ A[σ] Core.tuniv
    by (move: (substitution_tm _ _ _ _ _ TA TS CΔ) => hh; cbn in hh; exact hh).
  have CE : ctx (Δ ++ A[σ]) by (eapply c_cons; eauto).
  have TSE : typing_subst (Δ ++ A[σ]) (⇑ σ) (Γ ++ A) by (eapply typing_subst_lift; eauto).
  have TBs : typing (Δ ++ A[σ]) B[⇑ σ] Core.tuniv.
  { have CC : typing (Δ ++ A[σ]) B[⇑ σ] Core.tuniv[⇑ σ]
      by (eapply substitution_tm; eauto).
    cbn in CC. exact CC. }
  have TMs : typing Δ M0[σ] A[σ]
    by (eapply substitution_tm; [ exact TM | exact TS | exact CΔ ]).
  have TNs : typing Δ N0[σ] B[⇑ σ][M0[σ]..].
  { have hh : typing Δ (N0[σ]) (B[M0..][σ])
      by (eapply substitution_tm; [ exact TN | exact TS | exact CΔ ]).
    rewrite subst1_subst_comm in hh. exact hh. }
  have TSs : typing Δ (Core.tsig A[σ] B[⇑ σ]) Core.tuniv
    by (eapply t_tsig; [ exact TAs | exact TBs ]).
  have TPs : typing Δ (Core.mkpair M0[σ] N0[σ]) (Core.tsig A[σ] B[⇑ σ])
    by (eapply t_mkpair; [ exact TAs | exact TBs | exact TMs | exact TNs ]).
  have evU : EvalRel Core.tuniv ρ tuniv by (cbn; apply le_refl).
  have evS0 := evS. have evP0 := evP.
  move=> RB Hrank. destruct RB; [ exact I | ].
  destruct a as [ | | | | | | | | | b f | | ]; try done.
  destruct u as [ | | | | | | | | | | x y | ]; try done.
  (* u = mkpair x y at the type code tsig b f *)
  cbn in evP. move: evP => [Vxy [EMx ENy]].
  have Vx : valid x by (eapply valid_mkpair1; exact Vxy).
  have Vy : valid y by (eapply valid_mkpair2; exact Vxy).
  have evSc := evS. cbn in evSc. move: evSc => [Vb [Vf [EAb _]]].
  rewrite Val_mkpair.
  have VTy : Val (S RB) Δ (Core.tsig A B)[σ] Core.tuniv[σ] (wt_mkpair_ty WT).
  { eapply st_tsig_Val_edge;
      [ exact TA | exact TB | exact STA | exact STB
      | exact TS | exact TS' | exact CS | exact Fρ | exact VS | exact VS'
      | exact EVS | exact CΔ | exact evS0 | exact evU
      | cbn in Hrank |- *; lia ]. }
  split; [ eapply Val_ValTy; exact VTy | ].
  have [valM _] :=
    STM ρ m Δ σ σ' TS TS' CS Fρ VS VS' EVS CΔ x b (wt_mkpair_fst WT) EMx EAb.
  have VM1 : Val RB Δ M0[σ] A[σ] (wt_mkpair_fst WT)
    by (eapply valM; cbn in Hrank |- *; lia).
  have EBapp : EvalRel B[M0..] ρ (app f x)
    := sigma_cod_eval Vρ Vx evS0 EMx.
  have [valN _] :=
    STN ρ m Δ σ σ' TS TS' CS Fρ VS VS' EVS CΔ y (app f x) (wt_mkpair_snd WT) ENy EBapp.
  have VM2 : Val RB Δ N0[σ] B[⇑ σ][M0[σ]..] (wt_mkpair_snd WT).
  { rewrite -subst1_subst_comm.
    eapply valN; move: (rk_app f x) => Hax; cbn in Hrank |- *; lia. }
  exists A[σ]. exists B[⇑ σ]. split; [ apply ms_refl | ].
  split; [ apply c_refl; exact TSs | ].
  exists M0[σ]. exists N0[σ]. split; [ apply ms_refl | ].
  split; [ apply c_refl; exact TPs | ].
  split; [ exact TMs | ]. split; [ exact TNs | ].
  split; [ exact VM1 | exact VM2 ].
Qed.

Lemma st_mkpair_EqVal_edge (A : Tm n) (B : Tm (S n)) (M0 N0 : Tm n)
  (TA : typing Γ A Core.tuniv) (TB : typing (Γ ++ A) B Core.tuniv)
  (TM : typing Γ M0 A) (TN : typing Γ N0 B[M0..])
  (STA : semantic_typing Γ A Core.tuniv)
  (STB : semantic_typing (Γ ++ A) B Core.tuniv)
  (STM : semantic_typing Γ M0 A)
  (STN : semantic_typing Γ N0 B[M0..])
  ρ m (Δ : Ctx m) (σ σ' : Sub n m)
  (TS : typing_subst Δ σ Γ) (TS' : typing_subst Δ σ' Γ) (CS : ConvSub Δ Γ σ σ')
  (Fρ : fits Γ ρ) (VS : ValSub Δ Γ σ ρ) (VS' : ValSub Δ Γ σ' ρ)
  (EVS : EqValSub Δ Γ σ σ' ρ) (CΔ : ctx Δ) u a (WT : wt u a)
  (evP : EvalRel (Core.mkpair M0 N0) ρ u) (evS : EvalRel (Core.tsig A B) ρ a) :
  forall RB, max (rk u) (rk a) < RB ->
    EqVal RB Δ (Core.mkpair M0 N0)[σ] (Core.mkpair M0 N0)[σ'] (Core.tsig A B)[σ] WT.
Proof.
  have Vρ : valid_env ρ := fits_valid_env Fρ.
  have cΓ : ctx Γ by (eapply typing_ctx; exact TM).
  (* [B[M0..]] is a type, needed for its own cross-substitution conversion *)
  have TBM : typing Γ B[M0..] Core.tuniv.
  { have TS0 : typing_subst Γ (M0..) (Γ ++ A)
      by (eapply typing_subst_cons; [ asimpl; exact TM | apply typing_subst_id; exact cΓ ]).
    have hh := substitution_tm _ _ _ _ _ TB TS0 cΓ. cbn in hh. exact hh. }
  (* unprimed and primed substituted typings *)
  have TAs : typing Δ A[σ] Core.tuniv
    by (move: (substitution_tm _ _ _ _ _ TA TS CΔ) => hh; cbn in hh; exact hh).
  have TAs' : typing Δ A[σ'] Core.tuniv
    by (move: (substitution_tm _ _ _ _ _ TA TS' CΔ) => hh; cbn in hh; exact hh).
  have CE : ctx (Δ ++ A[σ]) by (eapply c_cons; eauto).
  have TSE : typing_subst (Δ ++ A[σ]) (⇑ σ) (Γ ++ A) by (eapply typing_subst_lift; eauto).
  have TBs : typing (Δ ++ A[σ]) B[⇑ σ] Core.tuniv.
  { have CC : typing (Δ ++ A[σ]) B[⇑ σ] Core.tuniv[⇑ σ]
      by (eapply substitution_tm; eauto).
    cbn in CC. exact CC. }
  have CE' : ctx (Δ ++ A[σ']) by (eapply c_cons; eauto).
  have TSE' : typing_subst (Δ ++ A[σ']) (⇑ σ') (Γ ++ A) by (eapply typing_subst_lift; eauto).
  have TBs' : typing (Δ ++ A[σ']) B[⇑ σ'] Core.tuniv.
  { have CC : typing (Δ ++ A[σ']) B[⇑ σ'] Core.tuniv[⇑ σ']
      by (eapply substitution_tm; eauto).
    cbn in CC. exact CC. }
  have TMs : typing Δ M0[σ] A[σ]
    by (eapply substitution_tm; [ exact TM | exact TS | exact CΔ ]).
  have TMs' : typing Δ M0[σ'] A[σ']
    by (eapply substitution_tm; [ exact TM | exact TS' | exact CΔ ]).
  have TNs : typing Δ N0[σ] B[⇑ σ][M0[σ]..].
  { have hh : typing Δ (N0[σ]) (B[M0..][σ])
      by (eapply substitution_tm; [ exact TN | exact TS | exact CΔ ]).
    rewrite subst1_subst_comm in hh. exact hh. }
  have TNs'p : typing Δ N0[σ'] B[⇑ σ'][M0[σ']..].
  { have hh : typing Δ (N0[σ']) (B[M0..][σ'])
      by (eapply substitution_tm; [ exact TN | exact TS' | exact CΔ ]).
    rewrite subst1_subst_comm in hh. exact hh. }
  have TSs : typing Δ (Core.tsig A[σ] B[⇑ σ]) Core.tuniv
    by (eapply t_tsig; [ exact TAs | exact TBs ]).
  have TSs' : typing Δ (Core.tsig A[σ'] B[⇑ σ']) Core.tuniv
    by (eapply t_tsig; [ exact TAs' | exact TBs' ]).
  have TPs : typing Δ (Core.mkpair M0[σ] N0[σ]) (Core.tsig A[σ] B[⇑ σ])
    by (eapply t_mkpair; [ exact TAs | exact TBs | exact TMs | exact TNs ]).
  have TPs' : typing Δ (Core.mkpair M0[σ'] N0[σ']) (Core.tsig A[σ'] B[⇑ σ'])
    by (eapply t_mkpair; [ exact TAs' | exact TBs' | exact TMs' | exact TNs'p ]).
  (* the cross-substitution conversions *)
  have convAA' : conv Δ A[σ] A[σ'] Core.tuniv := subst_conv_cross TA CΔ TS TS' CS.
  have codConv : conv (Δ ++ A[σ]) B[⇑ σ] B[⇑ σ'] Core.tuniv :=
    cod_subst_conv TA TB CΔ TS TS' CS.
  have convSS' : conv Δ (Core.tsig A[σ] B[⇑ σ]) (Core.tsig A[σ'] B[⇑ σ']) Core.tuniv
    by (eapply c_tsig;
          [ exact TAs | exact TAs' | exact TBs | exact TBs'
          | exact convAA' | exact codConv ]).
  have convMM' : conv Δ M0[σ] M0[σ'] A[σ] := subst_conv_cross TM CΔ TS TS' CS.
  have convBB' : conv Δ B[⇑ σ][M0[σ]..] B[⇑ σ'][M0[σ']..] Core.tuniv.
  { have hh : conv Δ (B[M0..][σ]) (B[M0..][σ']) Core.tuniv
      := subst_conv_cross TBM CΔ TS TS' CS.
    rewrite !subst1_subst_comm in hh. exact hh. }
  have convNN' : conv Δ N0[σ] N0[σ'] B[⇑ σ][M0[σ]..].
  { have hh : conv Δ (N0[σ]) (N0[σ']) (B[M0..][σ])
      := subst_conv_cross TN CΔ TS TS' CS.
    rewrite subst1_subst_comm in hh. exact hh. }
  (* primed terms, retyped at the unprimed types *)
  have TMs'0 : typing Δ M0[σ'] A[σ]
    by (eapply t_conv; [ exact TMs' | apply c_sym; exact convAA' ]).
  have evU : EvalRel Core.tuniv ρ tuniv by (cbn; apply le_refl).
  have evS0 := evS. have evP0 := evP.
  move=> RB Hrank. destruct RB; [ exact I | ].
  destruct a as [ | | | | | | | | | b f | | ]; try done.
  destruct u as [ | | | | | | | | | | x y | ]; try done.
  cbn in evP. move: evP => [Vxy [EMx ENy]].
  have Vx : valid x by (eapply valid_mkpair1; exact Vxy).
  have Vy : valid y by (eapply valid_mkpair2; exact Vxy).
  have evSc := evS. cbn in evSc. move: evSc => [Vb [Vf [EAb _]]].
  (* the unprimed pair record comes from the [Val] edge *)
  have VMv : Val (S RB) Δ (Core.mkpair M0 N0)[σ] (Core.tsig A B)[σ] WT.
  { eapply st_mkpair_Val_edge; eassumption. }
  rewrite Val_mkpair in VMv. move: VMv => [VTyd VPrM].
  (* component records for the primed side *)
  have EBapp : EvalRel B[M0..] ρ (app f x) := sigma_cod_eval Vρ Vx evS0 EMx.
  have [_ eqM] :=
    STM ρ m Δ σ σ' TS TS' CS Fρ VS VS' EVS CΔ x b (wt_mkpair_fst WT) EMx EAb.
  have EM1 : EqVal RB Δ M0[σ] M0[σ'] A[σ] (wt_mkpair_fst WT)
    by (eapply eqM; cbn in Hrank |- *; lia).
  have [_ eqN] :=
    STN ρ m Δ σ σ' TS TS' CS Fρ VS VS' EVS CΔ y (app f x) (wt_mkpair_snd WT) ENy EBapp.
  have EM2 : EqVal RB Δ N0[σ] N0[σ'] B[⇑ σ][M0[σ]..] (wt_mkpair_snd WT).
  { rewrite -subst1_subst_comm.
    eapply eqN; move: (rk_app f x) => Hax; cbn in Hrank |- *; lia. }
  (* the primed pair record: build it at the PRIMED type and transport the
     type term back along the type equality.  Building it by hand does not
     work -- [ValPair]'s second component sits at [B0[M1..]], so the primed
     record needs it at [B[⇑ σ][M0[σ']..]], and moving a [Val] there is a type
     transport, not a mere retyping. *)
  have VNv' : Val (S RB) Δ (Core.mkpair M0 N0)[σ'] (Core.tsig A B)[σ'] WT.
  { eapply st_mkpair_Val_edge with (σ' := σ'); try eassumption.
    - exact (ConvSub_refl TS').
    - exact (ValSub_EqValSub VS'). }
  have EqTyS : EqVal (S (S RB)) Δ (Core.tsig A B)[σ] (Core.tsig A B)[σ']
                 Core.tuniv[σ] (wt_mkpair_ty WT).
  { eapply st_tsig_EqVal_edge;
      [ exact TA | exact TB | exact STA | exact STB
      | exact TS | exact TS' | exact CS | exact Fρ | exact VS | exact VS'
      | exact EVS | exact CΔ | exact evS0 | exact evU
      | cbn in Hrank |- *; lia ]. }
  have ETy : EqValTy (S RB) Δ (Core.tsig A B)[σ'] (Core.tsig A B)[σ]
               (wt_mkpair_ty WT).
  { eapply EqValTy_sym; [ cbn in Hrank |- *; lia | ].
    eapply EqVal_EqValTy. exact EqTyS. }
  have VNv0 : Val (S RB) Δ (Core.mkpair M0 N0)[σ'] (Core.tsig A B)[σ] WT.
  { eapply Val_EqVal_fwd;
      [ cbn in Hrank |- *; lia | cbn in Hrank |- *; lia
      | apply c_sym; exact convSS' | exact VNv' | exact ETy ]. }
  rewrite Val_mkpair in VNv0. move: VNv0 => [_ VPrN].
  rewrite EqVal_mkpair.
  split; [ exact VTyd | ]. split; [ exact VPrM | ]. split; [ exact VPrN | ].
  (* the [EqValPair] record: no second-component equality, by design *)
  split; [ exact VPrM | ]. split; [ exact VPrN | ].
  exists A[σ]. exists B[⇑ σ]. split; [ apply ms_refl | ].
  exists M0[σ]. exists N0[σ]. exists M0[σ']. exists N0[σ'].
  split; [ apply ms_refl | ]. split; [ apply ms_refl | ].
  split; [ exact convMM' | ]. split; [ exact convNN' | ].
  split; [ exact EM1 | exact EM2 ].
Qed.

(** Σ-introduction rule (Agda [adequacyV2-ty-MkPair]). *)
Lemma st_mkpair A B M0 N0 :
  typing Γ A Core.tuniv ->
  typing (Γ ++ A) B Core.tuniv ->
  typing Γ M0 A ->
  typing Γ N0 B[M0..] ->
  semantic_typing Γ A Core.tuniv ->
  semantic_typing (Γ ++ A) B Core.tuniv ->
  semantic_typing Γ M0 A ->
  semantic_typing Γ N0 B[M0..] ->
(* ------------------------- *)
  semantic_typing Γ (Core.mkpair M0 N0) (Core.tsig A B).
Proof.
  move=> TA TB TM TN STA STB STM STN.
  move=> ρ m Δ σ σ' TS TS' CS Fρ VS VS' EVS CΔ u a WT evP evS.
  split.
  - eapply st_mkpair_Val_edge; eassumption.
  - eapply st_mkpair_EqVal_edge; eassumption.
Qed.

(* ------------------------------------------------------------------
   First projection.  [EvalRel (pfst M) ρ u] hands us a pair evaluation
   [EvalRel M ρ (mkpair u y)] directly, so no guessing of the pair's code is
   needed -- but that code is not well-typed, so we enlarge it by soundness
   ([typing_EvalRel]), read the record there at a fuel above the enlarged
   ranks, and come back with [Val_app_transport] (element code down by
   [le u u1], type code across the join [lub a b]) and [Val_fuel_any].  This
   is [st_app]'s shape exactly.
   ------------------------------------------------------------------ *)
Lemma st_pfst_Val_edge (A : Tm n) (B : Tm (S n)) (M0 : Tm n)
  (TA : typing Γ A Core.tuniv) (TB : typing (Γ ++ A) B Core.tuniv)
  (TM : typing Γ M0 (Core.tsig A B))
  (STA : semantic_typing Γ A Core.tuniv)
  (STM : semantic_typing Γ M0 (Core.tsig A B))
  ρ m (Δ : Ctx m) (σ σ' : Sub n m)
  (TS : typing_subst Δ σ Γ) (TS' : typing_subst Δ σ' Γ) (CS : ConvSub Δ Γ σ σ')
  (Fρ : fits Γ ρ) (VS : ValSub Δ Γ σ ρ) (VS' : ValSub Δ Γ σ' ρ)
  (EVS : EqValSub Δ Γ σ σ' ρ) (CΔ : ctx Δ) u a (WT : wt u a)
  (evF : EvalRel (Core.pfst M0) ρ u) (evA : EvalRel A ρ a) :
  forall RB, max (rk u) (rk a) < RB -> Val RB Δ (Core.pfst M0)[σ] A[σ] WT.
Proof.
  have Vρ : valid_env ρ := fits_valid_env Fρ.
  have TAs : typing Δ A[σ] Core.tuniv
    by (move: (substitution_tm _ _ _ _ _ TA TS CΔ) => hh; cbn in hh; exact hh).
  have CE : ctx (Δ ++ A[σ]) by (eapply c_cons; eauto).
  have TSE : typing_subst (Δ ++ A[σ]) (⇑ σ) (Γ ++ A) by (eapply typing_subst_lift; eauto).
  have TBs : typing (Δ ++ A[σ]) B[⇑ σ] Core.tuniv.
  { have CC : typing (Δ ++ A[σ]) B[⇑ σ] Core.tuniv[⇑ σ] by (eapply substitution_tm; eauto).
    cbn in CC. exact CC. }
  have evU : EvalRel Core.tuniv ρ tuniv by (cbn; apply le_refl).
  move=> RB Hrank.
  destruct (is_bot u) eqn:Hu.
  { have Eu : u = bot by (apply is_bot_eq; rewrite Hu). subst u. apply Val_Bot. }
  cbn in evF. rewrite Hu in evF. move: evF => [y evMk].
  have IT : InvTyped Γ M0 (Core.tsig A B) ρ := typing_EvalRel TM Fρ.
  have [ubig [abig [WTbig [LEbig [evMbig evSig]]]]] := IT (mkpair u y) evMk.
  have [u1 [y1 [Eub [LEu1 LEy1]]]] := le_mkpair_inv LEbig. subst ubig.
  destruct abig as [ | | | | | | | | | b f | | ];
    try solve [ exfalso; clear -WTbig; inversion WTbig ].
  have evSigC := evSig. cbn in evSigC. move: evSigC => [Vb [Vf [evA_b _]]].
  pose RBf := S (max (max (rk (mkpair u1 y1)) (rk (tsig b f))) (max (rk u) (rk a))).
  have HfM : max (rk (mkpair u1 y1)) (rk (tsig b f)) < S RBf by (unfold RBf; lia).
  have [valMbig _] :=
    STM ρ m Δ σ σ' TS TS' CS Fρ VS VS' EVS CΔ (mkpair u1 y1) (tsig b f) WTbig evMbig evSig.
  have VM := valMbig (S RBf) HfM. rewrite Val_mkpair in VM. move: VM => [_ VPr].
  move: VPr => [A0 [B0 [HRs [CTs [M1 [M2 [HRp [CTp [T1 [T2 [V1 V2]]]]]]]]]]].
  asimpl in HRs. have [EA0 EB0] := HeadRed_tsig_eq HRs. subst A0 B0.
  have HRf : HeadRed (Core.pfst M0[σ]) M1.
  { eapply relations.ms_app;
      [ eapply HeadRed_pfst; exact HRp
      | eapply ms_trans; [ apply hr_pfst | apply ms_refl ] ]. }
  have cvF : conv Δ (Core.pfst M0[σ]) M1 A[σ].
  { eapply c_trans.
    - eapply c_pfst; [ exact TAs | exact TBs | exact CTp ].
    - eapply c_beta_fst; [ exact TAs | exact TBs | exact T1 | exact T2 ]. }
  have V1e : Val RBf Δ (Core.pfst M0[σ]) A[σ] (wt_mkpair_fst WTbig)
    by (eapply Val_beta_expand; [ exact HRf | exact cvF | exact V1 ]).
  have Ca : compatible a b
    by (eapply EvalRel_compatible; [ exact Vρ | exact evA | exact evA_b ]).
  have Wa : wt a tuniv := wt_ty_tuniv WT.
  have Wb : wt b tuniv := wt_ty_tuniv (wt_mkpair_fst WTbig).
  have hUc : wt (lub a b) tuniv := wt_lub Wa Ca Wb.
  have ELub : EvalRel A ρ (lub a b)
    := proj2 (EvalRel_compatible_lub Vρ evA evA_b) _ erefl.
  have [valAj _] :=
    STA ρ m Δ σ σ' TS TS' CS Fρ VS VS' EVS CΔ (lub a b) tuniv hUc ELub evU.
  have VTc : Val RBf Δ A[σ] Core.tuniv hUc.
  { eapply valAj.
    have L := rk_lub a b.
    have Hb : rk b < rk (tsig b f) by (cbn; lia).
    have Htu : rk tuniv <= rk (tsig b f) by (cbn; lia).
    unfold RBf; lia. }
  have Vres : Val RBf Δ (Core.pfst M0[σ]) A[σ] WT.
  { eapply Val_app_transport; [ exact Ca | exact LEu1 | exact VTc | exact V1e ]. }
  eapply (Val_fuel_any (k := RBf) (k' := RB));
    [ unfold RBf; lia | unfold RBf; lia | lia | lia | exact Vres ].
Qed.

Lemma st_pfst_EqVal_edge (A : Tm n) (B : Tm (S n)) (M0 : Tm n)
  (TA : typing Γ A Core.tuniv) (TB : typing (Γ ++ A) B Core.tuniv)
  (TM : typing Γ M0 (Core.tsig A B))
  (STA : semantic_typing Γ A Core.tuniv)
  (STM : semantic_typing Γ M0 (Core.tsig A B))
  ρ m (Δ : Ctx m) (σ σ' : Sub n m)
  (TS : typing_subst Δ σ Γ) (TS' : typing_subst Δ σ' Γ) (CS : ConvSub Δ Γ σ σ')
  (Fρ : fits Γ ρ) (VS : ValSub Δ Γ σ ρ) (VS' : ValSub Δ Γ σ' ρ)
  (EVS : EqValSub Δ Γ σ σ' ρ) (CΔ : ctx Δ) u a (WT : wt u a)
  (evF : EvalRel (Core.pfst M0) ρ u) (evA : EvalRel A ρ a) :
  forall RB, max (rk u) (rk a) < RB ->
    EqVal RB Δ (Core.pfst M0)[σ] (Core.pfst M0)[σ'] A[σ] WT.
Proof.
  have Vρ : valid_env ρ := fits_valid_env Fρ.
  have TAs : typing Δ A[σ] Core.tuniv
    by (move: (substitution_tm _ _ _ _ _ TA TS CΔ) => hh; cbn in hh; exact hh).
  have CE : ctx (Δ ++ A[σ]) by (eapply c_cons; eauto).
  have TSE : typing_subst (Δ ++ A[σ]) (⇑ σ) (Γ ++ A) by (eapply typing_subst_lift; eauto).
  have TBs : typing (Δ ++ A[σ]) B[⇑ σ] Core.tuniv.
  { have CC : typing (Δ ++ A[σ]) B[⇑ σ] Core.tuniv[⇑ σ] by (eapply substitution_tm; eauto).
    cbn in CC. exact CC. }
  have evU : EvalRel Core.tuniv ρ tuniv by (cbn; apply le_refl).
  move=> RB Hrank.
  destruct (is_bot u) eqn:Hu.
  { have Eu : u = bot by (apply is_bot_eq; rewrite Hu). subst u. apply EqVal_Bot. }
  cbn in evF. rewrite Hu in evF. move: evF => [y evMk].
  have IT : InvTyped Γ M0 (Core.tsig A B) ρ := typing_EvalRel TM Fρ.
  have [ubig [abig [WTbig [LEbig [evMbig evSig]]]]] := IT (mkpair u y) evMk.
  have [u1 [y1 [Eub [LEu1 LEy1]]]] := le_mkpair_inv LEbig. subst ubig.
  destruct abig as [ | | | | | | | | | b f | | ];
    try solve [ exfalso; clear -WTbig; inversion WTbig ].
  have evSigC := evSig. cbn in evSigC. move: evSigC => [Vb [Vf [evA_b _]]].
  pose RBf := S (max (max (rk (mkpair u1 y1)) (rk (tsig b f))) (max (rk u) (rk a))).
  have HfM : max (rk (mkpair u1 y1)) (rk (tsig b f)) < S RBf by (unfold RBf; lia).
  have [_ eqMbig] :=
    STM ρ m Δ σ σ' TS TS' CS Fρ VS VS' EVS CΔ (mkpair u1 y1) (tsig b f) WTbig evMbig evSig.
  have EM := eqMbig (S RBf) HfM. rewrite EqVal_mkpair in EM.
  move: EM => [_ [VPrM [VPrN EPr]]].
  (* the unprimed side's components and typings *)
  move: (VPrM) => [A0 [B0 [HRs [CTs [M1 [M2 [HRp [CTp [T1 [T2 [V1 V2]]]]]]]]]]].
  asimpl in HRs. have [EA0 EB0] := HeadRed_tsig_eq HRs. subst A0 B0.
  (* the primed side's *)
  move: (VPrN) => [A1 [B1 [HRs1 [CTs1 [N1 [N2 [HRp1 [CTp1 [T1' [T2' [V1' V2']]]]]]]]]]].
  asimpl in HRs1. have [EA1 EB1] := HeadRed_tsig_eq HRs1. subst A1 B1.
  (* the [eqFst] field, with its components identified with the above *)
  move: EPr => [_ [_ [A2 [B2 [HRs2 [P1 [P2 [Q1 [Q2
                 [HRpM [HRpN [C1 [C2 [EF EFs]]]]]]]]]]]]]].
  asimpl in HRs2. have [EA2 EB2] := HeadRed_tsig_eq HRs2. subst A2 B2.
  have [ep1 ep2] := HeadRed_mkpair_det HRpM HRp. subst P1 P2.
  have [eq1 eq2] := HeadRed_mkpair_det HRpN HRp1. subst Q1 Q2.
  (* both projections head-reduce to, and are convertible to, the components *)
  have HRf : HeadRed (Core.pfst M0[σ]) M1.
  { eapply relations.ms_app;
      [ eapply HeadRed_pfst; exact HRp
      | eapply ms_trans; [ apply hr_pfst | apply ms_refl ] ]. }
  have HRf' : HeadRed (Core.pfst M0[σ']) N1.
  { eapply relations.ms_app;
      [ eapply HeadRed_pfst; exact HRp1
      | eapply ms_trans; [ apply hr_pfst | apply ms_refl ] ]. }
  have cvF : conv Δ (Core.pfst M0[σ]) M1 A[σ].
  { eapply c_trans.
    - eapply c_pfst; [ exact TAs | exact TBs | exact CTp ].
    - eapply c_beta_fst; [ exact TAs | exact TBs | exact T1 | exact T2 ]. }
  have cvF' : conv Δ (Core.pfst M0[σ']) N1 A[σ].
  { eapply c_trans.
    - eapply c_pfst; [ exact TAs | exact TBs | exact CTp1 ].
    - eapply c_beta_fst; [ exact TAs | exact TBs | exact T1' | exact T2' ]. }
  have EFe : EqVal RBf Δ (Core.pfst M0[σ]) (Core.pfst M0[σ']) A[σ]
               (wt_mkpair_fst WTbig)
    by (eapply EqVal_headred_expand;
          [ exact HRf | exact HRf' | exact cvF | exact cvF' | exact EF ]).
  have Ca : compatible a b
    by (eapply EvalRel_compatible; [ exact Vρ | exact evA | exact evA_b ]).
  have Wa : wt a tuniv := wt_ty_tuniv WT.
  have Wb : wt b tuniv := wt_ty_tuniv (wt_mkpair_fst WTbig).
  have hUc : wt (lub a b) tuniv := wt_lub Wa Ca Wb.
  have ELub : EvalRel A ρ (lub a b)
    := proj2 (EvalRel_compatible_lub Vρ evA evA_b) _ erefl.
  have [valAj _] :=
    STA ρ m Δ σ σ' TS TS' CS Fρ VS VS' EVS CΔ (lub a b) tuniv hUc ELub evU.
  have VTc : Val RBf Δ A[σ] Core.tuniv hUc.
  { eapply valAj.
    have L := rk_lub a b.
    have Hb : rk b < rk (tsig b f) by (cbn; lia).
    have Htu : rk tuniv <= rk (tsig b f) by (cbn; lia).
    unfold RBf; lia. }
  have Eres : EqVal RBf Δ (Core.pfst M0[σ]) (Core.pfst M0[σ']) A[σ] WT.
  { eapply EqVal_app_transport; [ exact Ca | exact LEu1 | exact VTc | exact EFe ]. }
  eapply (EqVal_fuel_any (k := RBf) (k' := RB));
    [ unfold RBf; lia | unfold RBf; lia | lia | lia | exact Eres ].
Qed.

(** Σ first projection (Agda [adequacyV2-ty-Fst]). *)
Lemma st_pfst A B M0 :
  typing Γ A Core.tuniv ->
  typing (Γ ++ A) B Core.tuniv ->
  typing Γ M0 (Core.tsig A B) ->
  semantic_typing Γ A Core.tuniv ->
  semantic_typing Γ M0 (Core.tsig A B) ->
(* ------------------------- *)
  semantic_typing Γ (Core.pfst M0) A.
Proof.
  move=> TA TB TM STA STM.
  move=> ρ m Δ σ σ' TS TS' CS Fρ VS VS' EVS CΔ u a WT evF evA.
  split.
  - eapply st_pfst_Val_edge; eassumption.
  - eapply st_pfst_EqVal_edge; eassumption.
Qed.

(* ------------------------------------------------------------------
   Second projection.  Same enlargement as [st_pfst], plus one extra move
   the first projection does not need: the record's second component sits at
   the type term [B[⇑ σ][M1..]] while the goal wants [B[⇑ σ][(pfst M0[σ])..]].
   Those are convertible, and the [EqValTy] licensing the transport is the
   type record's own [PiEdgeEq] ("related arguments give equal codomains")
   instantiated at the canonical selection below [u1] with the first
   components' equality.  The type validity at the join comes from
   [codomain_type_ValTy] with [N := pfst M0], whose argument obligation is
   [st_pfst] itself.
   ------------------------------------------------------------------ *)
Lemma st_psnd_Val_edge (A : Tm n) (B : Tm (S n)) (M0 : Tm n)
  (TA : typing Γ A Core.tuniv) (TB : typing (Γ ++ A) B Core.tuniv)
  (TM : typing Γ M0 (Core.tsig A B))
  (STA : semantic_typing Γ A Core.tuniv)
  (STB : semantic_typing (Γ ++ A) B Core.tuniv)
  (STM : semantic_typing Γ M0 (Core.tsig A B))
  ρ m (Δ : Ctx m) (σ σ' : Sub n m)
  (TS : typing_subst Δ σ Γ) (TS' : typing_subst Δ σ' Γ) (CS : ConvSub Δ Γ σ σ')
  (Fρ : fits Γ ρ) (VS : ValSub Δ Γ σ ρ) (VS' : ValSub Δ Γ σ' ρ)
  (EVS : EqValSub Δ Γ σ σ' ρ) (CΔ : ctx Δ) u a (WT : wt u a)
  (evS : EvalRel (Core.psnd M0) ρ u) (evB : EvalRel B[(Core.pfst M0)..] ρ a) :
  forall RB, max (rk u) (rk a) < RB ->
    Val RB Δ (Core.psnd M0)[σ] (B[(Core.pfst M0)..])[σ] WT.
Proof.
  have Vρ : valid_env ρ := fits_valid_env Fρ.
  have TAs : typing Δ A[σ] Core.tuniv
    by (move: (substitution_tm _ _ _ _ _ TA TS CΔ) => hh; cbn in hh; exact hh).
  have CE : ctx (Δ ++ A[σ]) by (eapply c_cons; eauto).
  have TSE : typing_subst (Δ ++ A[σ]) (⇑ σ) (Γ ++ A) by (eapply typing_subst_lift; eauto).
  have TBs : typing (Δ ++ A[σ]) B[⇑ σ] Core.tuniv.
  { have CC : typing (Δ ++ A[σ]) B[⇑ σ] Core.tuniv[⇑ σ] by (eapply substitution_tm; eauto).
    cbn in CC. exact CC. }
  have TMσ : typing Δ M0[σ] (Core.tsig A[σ] B[⇑ σ])
    by (move: (substitution_tm _ _ _ _ _ TM TS CΔ) => hh; cbn in hh; exact hh).
  have TFσ : typing Δ (Core.pfst M0[σ]) A[σ]
    by (eapply t_pfst; [ exact TAs | exact TBs | exact TMσ ]).
  have TFΓ : typing Γ (Core.pfst M0) A
    by (eapply t_pfst; [ exact TA | exact TB | exact TM ]).
  have evU : EvalRel Core.tuniv ρ tuniv by (cbn; apply le_refl).
  (* the goal's type term, in the form the records use *)
  rewrite subst1_subst_comm. cbn.
  move=> RB Hrank.
  destruct (is_bot u) eqn:Hu.
  { have Eu : u = bot by (apply is_bot_eq; rewrite Hu). subst u. apply Val_Bot. }
  cbn in evS. rewrite Hu in evS. move: evS => [x evMk].
  have IT : InvTyped Γ M0 (Core.tsig A B) ρ := typing_EvalRel TM Fρ.
  have [ubig [abig [WTbig [LEbig [evMbig evSig]]]]] := IT (mkpair x u) evMk.
  have [u1 [y1 [Eub [LEx1 LEu1]]]] := le_mkpair_inv LEbig. subst ubig.
  destruct abig as [ | | | | | | | | | b f | | ];
    try solve [ exfalso; clear -WTbig; inversion WTbig ].
  have evSigC := evSig. cbn in evSigC. move: evSigC => [Vb [Vf [evA_b _]]].
  pose RBf := S (max (max (rk (mkpair u1 y1)) (rk (tsig b f))) (max (rk u) (rk a))).
  have HfM : max (rk (mkpair u1 y1)) (rk (tsig b f)) < S (S RBf) by (unfold RBf; lia).
  have [valMbig _] :=
    STM ρ m Δ σ σ' TS TS' CS Fρ VS VS' EVS CΔ (mkpair u1 y1) (tsig b f) WTbig evMbig evSig.
  have VM := valMbig (S (S RBf)) HfM. rewrite Val_mkpair in VM.
  move: VM => [VTyS VPr].
  move: VPr => [A0 [B0 [HRs [CTs [M1 [M2 [HRp [CTp [T1 [T2 [V1 V2]]]]]]]]]]].
  asimpl in HRs. have [EA0 EB0] := HeadRed_tsig_eq HRs. subst A0 B0.
  (* the first projection, as in [st_pfst] *)
  have HRf : HeadRed (Core.pfst M0[σ]) M1.
  { eapply relations.ms_app;
      [ eapply HeadRed_pfst; exact HRp
      | eapply ms_trans; [ apply hr_pfst | apply ms_refl ] ]. }
  have cvF : conv Δ (Core.pfst M0[σ]) M1 A[σ].
  { eapply c_trans.
    - eapply c_pfst; [ exact TAs | exact TBs | exact CTp ].
    - eapply c_beta_fst; [ exact TAs | exact TBs | exact T1 | exact T2 ]. }
  have cvTy : conv Δ B[⇑ σ][M1..] B[⇑ σ][(Core.pfst M0[σ])..] Core.tuniv
    := conv_subst_arg Δ A[σ] B[⇑ σ] M1 (Core.pfst M0[σ]) TAs TBs T1 TFσ
         (c_sym _ _ _ _ _ cvF).
  (* the second projection reduces to [M2] *)
  have HRsnd : HeadRed (Core.psnd M0[σ]) M2.
  { eapply relations.ms_app;
      [ eapply HeadRed_psnd; exact HRp
      | eapply ms_trans; [ apply hr_psnd | apply ms_refl ] ]. }
  have cvSnd : conv Δ (Core.psnd M0[σ]) M2 B[⇑ σ][M1..].
  { eapply c_trans.
    - eapply c_conv;
        [ eapply c_psnd; [ exact TAs | exact TBs | exact CTp ]
        | apply c_sym; exact cvTy ].
    - eapply c_beta_snd; [ exact TAs | exact TBs | exact T1 | exact T2 ]. }
  have V2e : Val (S RBf) Δ (Core.psnd M0[σ]) B[⇑ σ][M1..] (wt_mkpair_snd WTbig)
    by (eapply Val_beta_expand; [ exact HRsnd | exact cvSnd | exact V2 ]).
  (* the codomain type equality, from the type record's [PiEdgeEq] *)
  rewrite ValTy_tsig in VTyS.
  move: (VTyS) => [A3 [B3 [HRs3 [TA3 [TB3 [vld3 [VDom3 [PEV3 PEE3]]]]]]]].
  asimpl in HRs3. have [E3 E4] := HeadRed_tsig_eq HRs3. subst A3 B3.
  have hpi : wt (tpi b f) tuniv := wt_tsig_tpi (wt_mkpair_ty WTbig).
  have Vu1 : valid u1 := wt_valid_tm (wt_mkpair_fst WTbig).
  have [uf [vf [Selg [Leuf Eqvf]]]] := selectionBelow Vf Vu1.
  have WTuf : wt uf b := wt_Selection (wt_tpi_dom hpi) Vf (wt_tpi_keys hpi) Selg.
  have EFst : EqVal (S RBf) Δ M1 (Core.pfst M0[σ]) A[σ] (wt_mkpair_fst WTbig).
  { eapply EqVal_headred_expand;
      [ apply ms_refl | exact HRf | apply c_refl; exact T1 | exact cvF | ].
    eapply Val_EqVal. exact V1. }
  have EFstS : EqVal (S RBf) Δ M1 (Core.pfst M0[σ]) A[σ] WTuf
    by (eapply restrictEqVal; [ exact Leuf | exact EFst ]).
  have Ecod := PEE3 uf vf Selg WTuf M1 (Core.pfst M0[σ])
                 (c_sym _ _ _ _ _ cvF) EFstS.
  subst vf.
  have ETy : EqValTy (S RBf) Δ B[⇑ σ][M1..] B[⇑ σ][(Core.pfst M0[σ])..]
               (wt_Selection_codU (wt_tsig_tpi (wt_mkpair_ty WTbig)) Selg).
  { eapply EqValTy_fuel_up_le; [ | eapply EqVal_EqValTy; exact Ecod ].
    have Hfa := rk_app f u1.
    have Hff : rk_fun f < rk (tsig b f) by (cbn; lia).
    unfold RBf; lia. }
  have V2t : Val (S RBf) Δ (Core.psnd M0[σ]) B[⇑ σ][(Core.pfst M0[σ])..]
               (wt_mkpair_snd WTbig).
  { eapply Val_EqVal_fwd;
      [ | | exact cvTy | exact V2e | exact ETy ].
    - have Hy : rk y1 <= rk (mkpair u1 y1) by (cbn; lia).
      unfold RBf; lia.
    - have Hfa := rk_app f u1.
      have Hff : rk_fun f < rk (tsig b f) by (cbn; lia).
      unfold RBf; lia. }
  (* transport the codes back to [(u, a)] *)
  have evFu1 : EvalRel (Core.pfst M0) ρ u1.
  { cbn. destruct (is_bot u1) eqn:Hu1; [ exact I | ]. exists y1. exact evMbig. }
  have EBapp : EvalRel B[(Core.pfst M0)..] ρ (app f u1)
    := sigma_cod_eval Vρ Vu1 evSig evFu1.
  have Ca : compatible a (app f u1)
    by (eapply EvalRel_compatible; [ exact Vρ | exact evB | exact EBapp ]).
  have Wa : wt a tuniv := wt_ty_tuniv WT.
  have Waf : wt (app f u1) tuniv := wt_ty_tuniv (wt_mkpair_snd WTbig).
  have hUc : wt (lub a (app f u1)) tuniv := wt_lub Wa Ca Waf.
  have ELub : EvalRel B[(Core.pfst M0)..] ρ (lub a (app f u1))
    := proj2 (EvalRel_compatible_lub Vρ evB EBapp) _ erefl.
  have STF : semantic_typing Γ (Core.pfst M0) A
    by (eapply st_pfst; [ exact TA | exact TB | exact TM | exact STA | exact STM ]).
  have VNarg : forall v c0 (h : wt v c0), EvalRel (Core.pfst M0) ρ v -> EvalRel A ρ c0 ->
      forall RB0, max (rk v) (rk c0) < RB0 -> Val RB0 Δ (Core.pfst M0)[σ] A[σ] h
    by (move=> v c0 h ev ea;
        exact (proj1 (STF ρ m Δ σ σ TS TS (ConvSub_refl TS)
                        Fρ VS VS (ValSub_EqValSub VS) CΔ v c0 h ev ea))).
  have VTc : Val (S RBf) Δ (B[⇑ σ][(Core.pfst M0)[σ] .: var]) Core.tuniv hUc.
  { eapply codomain_type_ValTy;
      [ exact TA | exact TFΓ | exact STA | exact STB | exact Fρ | exact TS
      | exact VS | exact CΔ | exact VNarg | exact ELub | ].
    have L := rk_lub a (app f u1).
    have Hfa := rk_app f u1.
    have Hff : rk_fun f < rk (tsig b f) by (cbn; lia).
    have Htu : rk tuniv <= rk (tsig b f) by (cbn; lia).
    unfold RBf; lia. }
  have Vres : Val (S RBf) Δ (Core.psnd M0[σ]) B[⇑ σ][(Core.pfst M0[σ])..] WT.
  { eapply Val_app_transport; [ exact Ca | exact LEu1 | cbn in VTc; exact VTc | exact V2t ]. }
  eapply (Val_fuel_any (k := S RBf) (k' := RB));
    [ unfold RBf; lia | unfold RBf; lia | lia | lia | exact Vres ].
Qed.

Lemma st_psnd_EqVal_edge (A : Tm n) (B : Tm (S n)) (M0 : Tm n)
  (TA : typing Γ A Core.tuniv) (TB : typing (Γ ++ A) B Core.tuniv)
  (TM : typing Γ M0 (Core.tsig A B))
  (STA : semantic_typing Γ A Core.tuniv)
  (STB : semantic_typing (Γ ++ A) B Core.tuniv)
  (STM : semantic_typing Γ M0 (Core.tsig A B))
  ρ m (Δ : Ctx m) (σ σ' : Sub n m)
  (TS : typing_subst Δ σ Γ) (TS' : typing_subst Δ σ' Γ) (CS : ConvSub Δ Γ σ σ')
  (Fρ : fits Γ ρ) (VS : ValSub Δ Γ σ ρ) (VS' : ValSub Δ Γ σ' ρ)
  (EVS : EqValSub Δ Γ σ σ' ρ) (CΔ : ctx Δ) u a (WT : wt u a)
  (evS : EvalRel (Core.psnd M0) ρ u) (evB : EvalRel B[(Core.pfst M0)..] ρ a) :
  forall RB, max (rk u) (rk a) < RB ->
    EqVal RB Δ (Core.psnd M0)[σ] (Core.psnd M0)[σ'] (B[(Core.pfst M0)..])[σ] WT.
Proof.
  have Vρ : valid_env ρ := fits_valid_env Fρ.
  have TAs : typing Δ A[σ] Core.tuniv
    by (move: (substitution_tm _ _ _ _ _ TA TS CΔ) => hh; cbn in hh; exact hh).
  have CE : ctx (Δ ++ A[σ]) by (eapply c_cons; eauto).
  have TSE : typing_subst (Δ ++ A[σ]) (⇑ σ) (Γ ++ A) by (eapply typing_subst_lift; eauto).
  have TBs : typing (Δ ++ A[σ]) B[⇑ σ] Core.tuniv.
  { have CC : typing (Δ ++ A[σ]) B[⇑ σ] Core.tuniv[⇑ σ] by (eapply substitution_tm; eauto).
    cbn in CC. exact CC. }
  have TMσ : typing Δ M0[σ] (Core.tsig A[σ] B[⇑ σ])
    by (move: (substitution_tm _ _ _ _ _ TM TS CΔ) => hh; cbn in hh; exact hh).
  have TFσ : typing Δ (Core.pfst M0[σ]) A[σ]
    by (eapply t_pfst; [ exact TAs | exact TBs | exact TMσ ]).
  have TFΓ : typing Γ (Core.pfst M0) A
    by (eapply t_pfst; [ exact TA | exact TB | exact TM ]).
  have evU : EvalRel Core.tuniv ρ tuniv by (cbn; apply le_refl).
  rewrite subst1_subst_comm. cbn.
  move=> RB Hrank.
  destruct (is_bot u) eqn:Hu.
  { have Eu : u = bot by (apply is_bot_eq; rewrite Hu). subst u. apply EqVal_Bot. }
  cbn in evS. rewrite Hu in evS. move: evS => [x evMk].
  have IT : InvTyped Γ M0 (Core.tsig A B) ρ := typing_EvalRel TM Fρ.
  have [ubig [abig [WTbig [LEbig [evMbig evSig]]]]] := IT (mkpair x u) evMk.
  have [u1 [y1 [Eub [LEx1 LEu1]]]] := le_mkpair_inv LEbig. subst ubig.
  destruct abig as [ | | | | | | | | | b f | | ];
    try solve [ exfalso; clear -WTbig; inversion WTbig ].
  have evSigC := evSig. cbn in evSigC. move: evSigC => [Vb [Vf [evA_b _]]].
  pose RBf := S (max (max (rk (mkpair u1 y1)) (rk (tsig b f))) (max (rk u) (rk a))).
  have HfM : max (rk (mkpair u1 y1)) (rk (tsig b f)) < S (S RBf) by (unfold RBf; lia).
  have [_ eqMbig] :=
    STM ρ m Δ σ σ' TS TS' CS Fρ VS VS' EVS CΔ (mkpair u1 y1) (tsig b f) WTbig evMbig evSig.
  have EM := eqMbig (S (S RBf)) HfM. rewrite EqVal_mkpair in EM.
  move: EM => [VTyS [VPrM [VPrN EPr]]].
  move: (VPrM) => [A0 [B0 [HRs [CTs [M1 [M2 [HRp [CTp [T1 [T2 [V1 V2]]]]]]]]]]].
  asimpl in HRs. have [EA0 EB0] := HeadRed_tsig_eq HRs. subst A0 B0.
  move: (VPrN) => [A1 [B1 [HRs1 [CTs1 [N1 [N2 [HRp1 [CTp1 [T1' [T2' [V1' V2']]]]]]]]]]].
  asimpl in HRs1. have [EA1 EB1] := HeadRed_tsig_eq HRs1. subst A1 B1.
  move: EPr => [_ [_ [A2 [B2 [HRs2 [P1 [P2 [Q1 [Q2
                 [HRpM [HRpN [C1 [C2 [EF EFs]]]]]]]]]]]]]].
  asimpl in HRs2. have [EA2 EB2] := HeadRed_tsig_eq HRs2. subst A2 B2.
  have [ep1 ep2] := HeadRed_mkpair_det HRpM HRp. subst P1 P2.
  have [eq1 eq2] := HeadRed_mkpair_det HRpN HRp1. subst Q1 Q2.
  (* the first projections, on both sides *)
  have HRf : HeadRed (Core.pfst M0[σ]) M1.
  { eapply relations.ms_app;
      [ eapply HeadRed_pfst; exact HRp
      | eapply ms_trans; [ apply hr_pfst | apply ms_refl ] ]. }
  have HRf' : HeadRed (Core.pfst M0[σ']) N1.
  { eapply relations.ms_app;
      [ eapply HeadRed_pfst; exact HRp1
      | eapply ms_trans; [ apply hr_pfst | apply ms_refl ] ]. }
  have cvF : conv Δ (Core.pfst M0[σ]) M1 A[σ].
  { eapply c_trans.
    - eapply c_pfst; [ exact TAs | exact TBs | exact CTp ].
    - eapply c_beta_fst; [ exact TAs | exact TBs | exact T1 | exact T2 ]. }
  have TMσ' : typing Δ M0[σ'] (Core.tsig A[σ] B[⇑ σ]) := proj1 (conv_typing CTp1).
  have TFσ' : typing Δ (Core.pfst M0[σ']) A[σ]
    by (eapply t_pfst; [ exact TAs | exact TBs | exact TMσ' ]).
  have cvF' : conv Δ (Core.pfst M0[σ']) N1 A[σ].
  { eapply c_trans.
    - eapply c_pfst; [ exact TAs | exact TBs | exact CTp1 ].
    - eapply c_beta_fst; [ exact TAs | exact TBs | exact T1' | exact T2' ]. }
  (* the three codomain-type conversions we need *)
  have cvTy : conv Δ B[⇑ σ][M1..] B[⇑ σ][(Core.pfst M0[σ])..] Core.tuniv
    := conv_subst_arg Δ A[σ] B[⇑ σ] M1 (Core.pfst M0[σ]) TAs TBs T1 TFσ
         (c_sym _ _ _ _ _ cvF).
  have cvB_MN : conv Δ B[⇑ σ][M1..] B[⇑ σ][N1..] Core.tuniv
    := conv_subst_arg Δ A[σ] B[⇑ σ] M1 N1 TAs TBs T1 T1' C1.
  have cvB_FN : conv Δ B[⇑ σ][(Core.pfst M0[σ'])..] B[⇑ σ][N1..] Core.tuniv
    := conv_subst_arg Δ A[σ] B[⇑ σ] (Core.pfst M0[σ']) N1 TAs TBs TFσ' T1' cvF'.
  (* the second projections, on both sides, at the LEFT type term *)
  have HRsnd : HeadRed (Core.psnd M0[σ]) M2.
  { eapply relations.ms_app;
      [ eapply HeadRed_psnd; exact HRp
      | eapply ms_trans; [ apply hr_psnd | apply ms_refl ] ]. }
  have HRsnd' : HeadRed (Core.psnd M0[σ']) N2.
  { eapply relations.ms_app;
      [ eapply HeadRed_psnd; exact HRp1
      | eapply ms_trans; [ apply hr_psnd | apply ms_refl ] ]. }
  have cvSnd : conv Δ (Core.psnd M0[σ]) M2 B[⇑ σ][M1..].
  { eapply c_trans.
    - eapply c_conv;
        [ eapply c_psnd; [ exact TAs | exact TBs | exact CTp ]
        | apply c_sym; exact cvTy ].
    - eapply c_beta_snd; [ exact TAs | exact TBs | exact T1 | exact T2 ]. }
  have cvSnd' : conv Δ (Core.psnd M0[σ']) N2 B[⇑ σ][M1..].
  { eapply c_conv; [ | apply c_sym; exact cvB_MN ].
    eapply c_trans.
    - eapply c_conv;
        [ eapply c_psnd; [ exact TAs | exact TBs | exact CTp1 ]
        | exact cvB_FN ].
    - eapply c_beta_snd; [ exact TAs | exact TBs | exact T1' | exact T2' ]. }
  have E2e : EqVal (S RBf) Δ (Core.psnd M0[σ]) (Core.psnd M0[σ']) B[⇑ σ][M1..]
               (wt_mkpair_snd WTbig)
    by (eapply EqVal_headred_expand;
          [ exact HRsnd | exact HRsnd' | exact cvSnd | exact cvSnd' | exact EFs ]).
  (* the codomain type equality, from the type record's [PiEdgeEq] *)
  rewrite ValTy_tsig in VTyS.
  move: (VTyS) => [A3 [B3 [HRs3 [TA3 [TB3 [vld3 [VDom3 [PEV3 PEE3]]]]]]]].
  asimpl in HRs3. have [E3 E4] := HeadRed_tsig_eq HRs3. subst A3 B3.
  have hpi : wt (tpi b f) tuniv := wt_tsig_tpi (wt_mkpair_ty WTbig).
  have Vu1 : valid u1 := wt_valid_tm (wt_mkpair_fst WTbig).
  have [uf [vf [Selg [Leuf Eqvf]]]] := selectionBelow Vf Vu1.
  have WTuf : wt uf b := wt_Selection (wt_tpi_dom hpi) Vf (wt_tpi_keys hpi) Selg.
  have EFst : EqVal (S RBf) Δ M1 (Core.pfst M0[σ]) A[σ] (wt_mkpair_fst WTbig).
  { eapply EqVal_headred_expand;
      [ apply ms_refl | exact HRf | apply c_refl; exact T1 | exact cvF | ].
    eapply Val_EqVal. exact V1. }
  have EFstS : EqVal (S RBf) Δ M1 (Core.pfst M0[σ]) A[σ] WTuf
    by (eapply restrictEqVal; [ exact Leuf | exact EFst ]).
  have Ecod := PEE3 uf vf Selg WTuf M1 (Core.pfst M0[σ])
                 (c_sym _ _ _ _ _ cvF) EFstS.
  subst vf.
  have ETy : EqValTy (S RBf) Δ B[⇑ σ][M1..] B[⇑ σ][(Core.pfst M0[σ])..]
               (wt_Selection_codU (wt_tsig_tpi (wt_mkpair_ty WTbig)) Selg).
  { eapply EqValTy_fuel_up_le; [ | eapply EqVal_EqValTy; exact Ecod ].
    have Hfa := rk_app f u1.
    have Hff : rk_fun f < rk (tsig b f) by (cbn; lia).
    unfold RBf; lia. }
  have E2t : EqVal (S RBf) Δ (Core.psnd M0[σ]) (Core.psnd M0[σ'])
               B[⇑ σ][(Core.pfst M0[σ])..] (wt_mkpair_snd WTbig).
  { eapply EqVal_EqVal_fwd;
      [ | | exact cvTy | exact E2e | exact ETy ].
    - have Hy : rk y1 <= rk (mkpair u1 y1) by (cbn; lia).
      unfold RBf; lia.
    - have Hfa := rk_app f u1.
      have Hff : rk_fun f < rk (tsig b f) by (cbn; lia).
      unfold RBf; lia. }
  (* transport the codes back to [(u, a)] *)
  have evFu1 : EvalRel (Core.pfst M0) ρ u1.
  { cbn. destruct (is_bot u1) eqn:Hu1; [ exact I | ]. exists y1. exact evMbig. }
  have EBapp : EvalRel B[(Core.pfst M0)..] ρ (app f u1)
    := sigma_cod_eval Vρ Vu1 evSig evFu1.
  have Ca : compatible a (app f u1)
    by (eapply EvalRel_compatible; [ exact Vρ | exact evB | exact EBapp ]).
  have Wa : wt a tuniv := wt_ty_tuniv WT.
  have Waf : wt (app f u1) tuniv := wt_ty_tuniv (wt_mkpair_snd WTbig).
  have hUc : wt (lub a (app f u1)) tuniv := wt_lub Wa Ca Waf.
  have ELub : EvalRel B[(Core.pfst M0)..] ρ (lub a (app f u1))
    := proj2 (EvalRel_compatible_lub Vρ evB EBapp) _ erefl.
  have STF : semantic_typing Γ (Core.pfst M0) A
    by (eapply st_pfst; [ exact TA | exact TB | exact TM | exact STA | exact STM ]).
  have VNarg : forall v c0 (h : wt v c0), EvalRel (Core.pfst M0) ρ v -> EvalRel A ρ c0 ->
      forall RB0, max (rk v) (rk c0) < RB0 -> Val RB0 Δ (Core.pfst M0)[σ] A[σ] h
    by (move=> v c0 h ev ea;
        exact (proj1 (STF ρ m Δ σ σ TS TS (ConvSub_refl TS)
                        Fρ VS VS (ValSub_EqValSub VS) CΔ v c0 h ev ea))).
  have VTc : Val (S RBf) Δ (B[⇑ σ][(Core.pfst M0)[σ] .: var]) Core.tuniv hUc.
  { eapply codomain_type_ValTy;
      [ exact TA | exact TFΓ | exact STA | exact STB | exact Fρ | exact TS
      | exact VS | exact CΔ | exact VNarg | exact ELub | ].
    have L := rk_lub a (app f u1).
    have Hfa := rk_app f u1.
    have Hff : rk_fun f < rk (tsig b f) by (cbn; lia).
    have Htu : rk tuniv <= rk (tsig b f) by (cbn; lia).
    unfold RBf; lia. }
  have Eres : EqVal (S RBf) Δ (Core.psnd M0[σ]) (Core.psnd M0[σ'])
                B[⇑ σ][(Core.pfst M0[σ])..] WT.
  { eapply EqVal_app_transport;
      [ exact Ca | exact LEu1 | cbn in VTc; exact VTc | exact E2t ]. }
  eapply (EqVal_fuel_any (k := S RBf) (k' := RB));
    [ unfold RBf; lia | unfold RBf; lia | lia | lia | exact Eres ].
Qed.

(** Σ second projection (Agda [adequacyV2-ty-Snd]). *)
Lemma st_psnd A B M0 :
  typing Γ A Core.tuniv ->
  typing (Γ ++ A) B Core.tuniv ->
  typing Γ M0 (Core.tsig A B) ->
  semantic_typing Γ A Core.tuniv ->
  semantic_typing (Γ ++ A) B Core.tuniv ->
  semantic_typing Γ M0 (Core.tsig A B) ->
(* ------------------------- *)
  semantic_typing Γ (Core.psnd M0) B[(Core.pfst M0)..].
Proof.
  move=> TA TB TM STA STB STM.
  move=> ρ m Δ σ σ' TS TS' CS Fρ VS VS' EVS CΔ u a WT evS evB.
  split.
  - eapply st_psnd_Val_edge; eassumption.
  - eapply st_psnd_EqVal_edge; eassumption.
Qed.

(** Σ-formation rule (Agda [adequacyV2-ty-Sigma]). *)
Lemma st_tsig A B :
  typing Γ A Core.tuniv ->
  typing (Γ ++ A) B Core.tuniv ->
  semantic_typing Γ A Core.tuniv ->
  semantic_typing (Γ ++ A) B Core.tuniv ->
(* ------------------------- *)
  semantic_typing Γ (Core.tsig A B) Core.tuniv.
Proof.
  move=> TA TB STA STB.
  move=> ρ m Δ σ σ' TS TS' CS Fρ VS VS' EVS CΔ u a WT evAN evAB.
  split.
  - eapply st_tsig_Val_edge; eassumption.
  - eapply st_tsig_EqVal_edge; eassumption.
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
  destruct u as [ | | | | | | g_val | | | | | ]; try done.
  - (* u = bot *) apply Val_Bot.
  - (* u = abs g_val *)
    destruct a as [ | | | | | b f_ty | | | | | | ];
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
  destruct u as [ | | | | | | g_val | | | | | ]; try done.
  - (* u = bot *) apply EqVal_Bot.
  - (* u = abs g_val *)
    destruct a as [ | | | | | b f_ty | | | | | | ];
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
  move=> RB Hrank.
  eapply EqVal_sym;
    [ cbn in Hrank; lia | cbn in Hrank; lia | exact (h RB Hrank) ].
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
  move=> RB Hrank.
  eapply EqVal_trans;
    [ cbn in Hrank; lia | cbn in Hrank; lia
    | exact (e1 RB Hrank) | exact (e2 RB Hrank) ].
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
  destruct abig as [ | | | | | b f | | | | | | ]; try solve [ exfalso; clear -WTbig; inversion WTbig ].
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
  destruct abig as [ | | | | | b f | | | | | | ]; try solve [ exfalso; clear -WTbig; inversion WTbig ].
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
  destruct a as [ | | | | | b f_ty | | | | | | ];
    try solve [ exfalso; clear -evTpi; cbn in evTpi; done ].
  - (* a = bot: the type value is [bot], so [u = bot] *)
    have Eu := wt_bot_inv WT. subst u. apply EqVal_Bot.
  - (* a = tpi b f_ty *)
    move: evTpi => [Vb [Vf_ty [ERA_b [a'_T [ERA_aT EFunB]]]]].
    destruct u as [ | | | | | | g_val | | | | | ];
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
  destruct u as [ | | | | w | b f | g | | | | | ];
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
  destruct u as [ | | | | | b f | | | | | | ]; try done.
  - (* u = bot *) apply EqVal_Bot.
  - (* u = tpi b f *)
    move: evM => [Vb [Vf [evAdom [a' [evAdom' EFun]]]]].
    have Eatu : a = tuniv by (eapply wt_tpi_ty_tuniv; [ exact WT | exact evA ]). subst a.
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
(** Σ-congruence: the [sc_tpi] script verbatim, at [wt_tsig_dom] /
    [wt_tsig_tpi]. *)
Lemma sc_tsig A0 A1 (B0 B1 : Tm (S n)) :
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
  semantic_conv2 Γ (Core.tsig A0 B0) (Core.tsig A1 B1) Core.tuniv.
Proof.
  move=> TA0 TA1 TB0 TB1 CA CB STA0 STA1 STB0 STB1 SCA SCB.
  move=> ρ m Δ σ TS FR VS CD u a WT evM evA.
  have Vρ : valid_env ρ := fits_valid_env FR.
  have evU : EvalRel Core.tuniv ρ tuniv by (cbn; apply le_refl).
  have CSIG : conv Γ (Core.tsig A0 B0) (Core.tsig A1 B1) Core.tuniv
    by (eapply c_tsig;
          [ exact TA0 | exact TA1 | exact TB0 | exact TB1 | exact CA | exact CB ]).
  move: (conv_EvalRel CSIG FR) => [_ [_ [fwd _]]].
  have evN : EvalRel (Core.tsig A1 B1) ρ u := fwd u evM.
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
  destruct u as [ | | | | | | | | | b f | | ]; try done.
  - (* u = bot *) apply EqVal_Bot.
  - (* u = tsig b f *)
    move: evM => [Vb [Vf [evAdom [a' [evAdom' EFun]]]]].
    have Eatu : a = tuniv by (inversion WT; auto). subst a.
    have evANpi : EvalRel (Core.tpi A0 B0) ρ (tpi b f) := EvalRel_tsig_tpi evM0.
    have VMv : Val (S RB) Δ (Core.tsig A0 B0)[σ] Core.tuniv[σ] WT.
    { eapply st_tsig_Val_edge with (σ' := σ); try eassumption.
      - exact (ConvSub_refl TS).
      - exact (ValSub_EqValSub VS). }
    have VNv : Val (S RB) Δ (Core.tsig A1 B1)[σ] Core.tuniv[σ] WT.
    { eapply st_tsig_Val_edge with (σ' := σ); try eassumption.
      - exact (ConvSub_refl TS).
      - exact (ValSub_EqValSub VS). }
    rewrite Val_tuniv in VMv. rewrite Val_tuniv in VNv.
    have eqA := SCA ρ m Δ σ TS FR VS CD b tuniv (wt_tsig_dom WT) evAdom evU.
    have eqDom : EqVal RB Δ A0[σ] A1[σ] Core.tuniv (wt_tsig_dom WT).
    { destruct (le_lt_dec 2 RB) as [HRB|HRB].
      - eapply EqVal_irr; eapply eqA; cbn in Hrank |- *; lia.
      - have Eb : b = bot by (apply rk_bot_inv; cbn in Hrank; lia).
        move: (wt_tsig_dom WT). rewrite Eb. move=> w. apply EqVal_Bot. }
    rewrite EqVal_tuniv.
    split; [ exact VMv | ]. split; [ exact VNv | ].
    rewrite EqValTy_tsig. cbn [Rec.EqValTySig].
    split; [ exact VMv | ]. split; [ exact VNv | ].
    exists A0[σ], B0[⇑ σ]. split; [ apply ms_refl | ].
    exists A1[σ], B1[⇑ σ]. split; [ apply ms_refl | ].
    split; [ exact convA0A1 | ].
    split; [ exact convB0B1 | ].
    split; [ exact (wt_valid_tm WT) | ].
    split; [ exact eqDom | ].
    eapply tpi_PiEdgeEqTy_cross; (try eassumption); exact Hrank.
Qed.

(** The two Σ betas.  Both sides of the equation head-reduce to the same term,
    so these are head-expansions of the diagonal [EqVal] ([Val_EqVal] applied
    to the component's own semantic typing), exactly like [sc_beta]. *)
Lemma sc_beta_fst A (B : Tm (S n)) M0 N0 :
  typing Γ A Core.tuniv ->
  typing (Γ ++ A) B Core.tuniv ->
  typing Γ M0 A ->
  typing Γ N0 B[M0..] ->
  semantic_typing Γ M0 A ->
(* ------------------------- *)
  semantic_conv2 Γ (Core.pfst (Core.mkpair M0 N0)) M0 A.
Proof.
  move=> TA TB TM TN STM.
  move=> ρ m Δ σ TS FR VS CD u a WT evP evA.
  have TAs : typing Δ A[σ] Core.tuniv
    by (move: (substitution_tm _ _ _ _ _ TA TS CD) => hh; cbn in hh; exact hh).
  have CE : ctx (Δ ++ A[σ]) by (eapply c_cons; eauto).
  have TSE : typing_subst (Δ ++ A[σ]) (⇑ σ) (Γ ++ A) by (eapply typing_subst_lift; eauto).
  have TBs : typing (Δ ++ A[σ]) B[⇑ σ] Core.tuniv.
  { have CC : typing (Δ ++ A[σ]) B[⇑ σ] Core.tuniv[⇑ σ] by (eapply substitution_tm; eauto).
    cbn in CC. exact CC. }
  have TMs : typing Δ M0[σ] A[σ]
    by (eapply substitution_tm; [ exact TM | exact TS | exact CD ]).
  have TNs : typing Δ N0[σ] B[⇑ σ][M0[σ]..].
  { have hh : typing Δ (N0[σ]) (B[M0..][σ])
      by (eapply substitution_tm; [ exact TN | exact TS | exact CD ]).
    rewrite subst1_subst_comm in hh. exact hh. }
  move=> RB Hrank.
  destruct (is_bot u) eqn:Hu.
  { have Eu : u = bot by (apply is_bot_eq; rewrite Hu). subst u. apply EqVal_Bot. }
  cbn in evP. rewrite Hu in evP. move: evP => [y [Vxy [EM EN]]].
  have [valM _] :=
    STM ρ m Δ σ σ TS TS (ConvSub_refl TS) FR VS VS (ValSub_EqValSub VS) CD u a WT EM evA.
  have VM : Val RB Δ M0[σ] A[σ] WT := valM RB Hrank.
  eapply EqVal_headred_expand;
    [ eapply ms_trans; [ apply hr_pfst | apply ms_refl ]
    | apply ms_refl
    | eapply c_beta_fst; [ exact TAs | exact TBs | exact TMs | exact TNs ]
    | apply c_refl; exact TMs
    | eapply Val_EqVal; exact VM ].
Qed.

Lemma sc_beta_snd A (B : Tm (S n)) M0 N0 :
  typing Γ A Core.tuniv ->
  typing (Γ ++ A) B Core.tuniv ->
  typing Γ M0 A ->
  typing Γ N0 B[M0..] ->
  semantic_typing Γ N0 B[M0..] ->
(* ------------------------- *)
  semantic_conv2 Γ (Core.psnd (Core.mkpair M0 N0)) N0 B[M0..].
Proof.
  move=> TA TB TM TN STN.
  move=> ρ m Δ σ TS FR VS CD u a WT evP evA.
  have TAs : typing Δ A[σ] Core.tuniv
    by (move: (substitution_tm _ _ _ _ _ TA TS CD) => hh; cbn in hh; exact hh).
  have CE : ctx (Δ ++ A[σ]) by (eapply c_cons; eauto).
  have TSE : typing_subst (Δ ++ A[σ]) (⇑ σ) (Γ ++ A) by (eapply typing_subst_lift; eauto).
  have TBs : typing (Δ ++ A[σ]) B[⇑ σ] Core.tuniv.
  { have CC : typing (Δ ++ A[σ]) B[⇑ σ] Core.tuniv[⇑ σ] by (eapply substitution_tm; eauto).
    cbn in CC. exact CC. }
  have TMs : typing Δ M0[σ] A[σ]
    by (eapply substitution_tm; [ exact TM | exact TS | exact CD ]).
  have TNs : typing Δ N0[σ] B[⇑ σ][M0[σ]..].
  { have hh : typing Δ (N0[σ]) (B[M0..][σ])
      by (eapply substitution_tm; [ exact TN | exact TS | exact CD ]).
    rewrite subst1_subst_comm in hh. exact hh. }
  move=> RB Hrank.
  destruct (is_bot u) eqn:Hu.
  { have Eu : u = bot by (apply is_bot_eq; rewrite Hu). subst u. apply EqVal_Bot. }
  cbn in evP. rewrite Hu in evP. move: evP => [x [Vxy [EM EN]]].
  have [valN _] :=
    STN ρ m Δ σ σ TS TS (ConvSub_refl TS) FR VS VS (ValSub_EqValSub VS) CD u a WT EN evA.
  have VN : Val RB Δ N0[σ] (B[M0..])[σ] WT := valN RB Hrank.
  rewrite subst1_subst_comm in VN. rewrite subst1_subst_comm.
  eapply EqVal_headred_expand;
    [ eapply ms_trans; [ apply hr_psnd | apply ms_refl ]
    | apply ms_refl
    | eapply c_beta_snd; [ exact TAs | exact TBs | exact TMs | exact TNs ]
    | apply c_refl; exact TNs
    | eapply Val_EqVal; exact VN ].
Qed.

(** The two Σ projection congruences.  [st_pfst_EqVal_edge] /
    [st_psnd_EqVal_edge] with the primed side [M0[σ']] replaced by a second
    term [M0'[σ]]; the pair record now comes from the conversion's own
    [semantic_conv2] rather than from [semantic_typing]'s second conjunct. *)
Lemma sc_pfst A (B : Tm (S n)) M0 M0' :
  typing Γ A Core.tuniv ->
  typing (Γ ++ A) B Core.tuniv ->
  conv Γ M0 M0' (Core.tsig A B) ->
  semantic_typing Γ A Core.tuniv ->
  semantic_conv2 Γ M0 M0' (Core.tsig A B) ->
(* ------------------------- *)
  semantic_conv2 Γ (Core.pfst M0) (Core.pfst M0') A.
Proof.
  move=> TA TB CM STA SCM.
  have TM : typing Γ M0 (Core.tsig A B) := proj1 (conv_typing CM).
  move=> ρ m Δ σ TS FR VS CD u a WT evF evA.
  have Vρ : valid_env ρ := fits_valid_env FR.
  have TAs : typing Δ A[σ] Core.tuniv
    by (move: (substitution_tm _ _ _ _ _ TA TS CD) => hh; cbn in hh; exact hh).
  have CE : ctx (Δ ++ A[σ]) by (eapply c_cons; eauto).
  have TSE : typing_subst (Δ ++ A[σ]) (⇑ σ) (Γ ++ A) by (eapply typing_subst_lift; eauto).
  have TBs : typing (Δ ++ A[σ]) B[⇑ σ] Core.tuniv.
  { have CC : typing (Δ ++ A[σ]) B[⇑ σ] Core.tuniv[⇑ σ] by (eapply substitution_tm; eauto).
    cbn in CC. exact CC. }
  have evU : EvalRel Core.tuniv ρ tuniv by (cbn; apply le_refl).
  move=> RB Hrank.
  destruct (is_bot u) eqn:Hu.
  { have Eu : u = bot by (apply is_bot_eq; rewrite Hu). subst u. apply EqVal_Bot. }
  cbn in evF. rewrite Hu in evF. move: evF => [y evMk].
  have IT : InvTyped Γ M0 (Core.tsig A B) ρ := typing_EvalRel TM FR.
  have [ubig [abig [WTbig [LEbig [evMbig evSig]]]]] := IT (mkpair u y) evMk.
  have [u1 [y1 [Eub [LEu1 LEy1]]]] := le_mkpair_inv LEbig. subst ubig.
  destruct abig as [ | | | | | | | | | b f | | ];
    try solve [ exfalso; clear -WTbig; inversion WTbig ].
  have evSigC := evSig. cbn in evSigC. move: evSigC => [Vb [Vf [evA_b _]]].
  pose RBf := S (max (max (rk (mkpair u1 y1)) (rk (tsig b f))) (max (rk u) (rk a))).
  have HfM : max (rk (mkpair u1 y1)) (rk (tsig b f)) < S RBf by (unfold RBf; lia).
  have EM := SCM ρ m Δ σ TS FR VS CD (mkpair u1 y1) (tsig b f) WTbig evMbig evSig
               (S RBf) HfM.
  rewrite EqVal_mkpair in EM.
  move: EM => [_ [VPrM [VPrN EPr]]].
  move: (VPrM) => [A0 [B0 [HRs [CTs [M1 [M2 [HRp [CTp [T1 [T2 [V1 V2]]]]]]]]]]].
  asimpl in HRs. have [EA0 EB0] := HeadRed_tsig_eq HRs. subst A0 B0.
  move: (VPrN) => [A1 [B1 [HRs1 [CTs1 [N1 [N2 [HRp1 [CTp1 [T1' [T2' [V1' V2']]]]]]]]]]].
  asimpl in HRs1. have [EA1 EB1] := HeadRed_tsig_eq HRs1. subst A1 B1.
  move: EPr => [_ [_ [A2 [B2 [HRs2 [P1 [P2 [Q1 [Q2
                 [HRpM [HRpN [C1 [C2 [EF EFs]]]]]]]]]]]]]].
  asimpl in HRs2. have [EA2 EB2] := HeadRed_tsig_eq HRs2. subst A2 B2.
  have [ep1 ep2] := HeadRed_mkpair_det HRpM HRp. subst P1 P2.
  have [eq1 eq2] := HeadRed_mkpair_det HRpN HRp1. subst Q1 Q2.
  have HRf : HeadRed (Core.pfst M0[σ]) M1.
  { eapply relations.ms_app;
      [ eapply HeadRed_pfst; exact HRp
      | eapply ms_trans; [ apply hr_pfst | apply ms_refl ] ]. }
  have HRf' : HeadRed (Core.pfst M0'[σ]) N1.
  { eapply relations.ms_app;
      [ eapply HeadRed_pfst; exact HRp1
      | eapply ms_trans; [ apply hr_pfst | apply ms_refl ] ]. }
  have cvF : conv Δ (Core.pfst M0[σ]) M1 A[σ].
  { eapply c_trans.
    - eapply c_pfst; [ exact TAs | exact TBs | exact CTp ].
    - eapply c_beta_fst; [ exact TAs | exact TBs | exact T1 | exact T2 ]. }
  have cvF' : conv Δ (Core.pfst M0'[σ]) N1 A[σ].
  { eapply c_trans.
    - eapply c_pfst; [ exact TAs | exact TBs | exact CTp1 ].
    - eapply c_beta_fst; [ exact TAs | exact TBs | exact T1' | exact T2' ]. }
  have EFe : EqVal RBf Δ (Core.pfst M0[σ]) (Core.pfst M0'[σ]) A[σ]
               (wt_mkpair_fst WTbig)
    by (eapply EqVal_headred_expand;
          [ exact HRf | exact HRf' | exact cvF | exact cvF' | exact EF ]).
  have Ca : compatible a b
    by (eapply EvalRel_compatible; [ exact Vρ | exact evA | exact evA_b ]).
  have Wa : wt a tuniv := wt_ty_tuniv WT.
  have Wb : wt b tuniv := wt_ty_tuniv (wt_mkpair_fst WTbig).
  have hUc : wt (lub a b) tuniv := wt_lub Wa Ca Wb.
  have ELub : EvalRel A ρ (lub a b)
    := proj2 (EvalRel_compatible_lub Vρ evA evA_b) _ erefl.
  have [valAj _] :=
    STA ρ m Δ σ σ TS TS (ConvSub_refl TS) FR VS VS (ValSub_EqValSub VS) CD
        (lub a b) tuniv hUc ELub evU.
  have VTc : Val RBf Δ A[σ] Core.tuniv hUc.
  { eapply valAj.
    have L := rk_lub a b.
    have Hb : rk b < rk (tsig b f) by (cbn; lia).
    have Htu : rk tuniv <= rk (tsig b f) by (cbn; lia).
    unfold RBf; lia. }
  have Eres : EqVal RBf Δ (Core.pfst M0[σ]) (Core.pfst M0'[σ]) A[σ] WT.
  { eapply EqVal_app_transport; [ exact Ca | exact LEu1 | exact VTc | exact EFe ]. }
  eapply (EqVal_fuel_any (k := RBf) (k' := RB));
    [ unfold RBf; lia | unfold RBf; lia | lia | lia | exact Eres ].
Qed.

Lemma sc_psnd A (B : Tm (S n)) M0 M0' :
  typing Γ A Core.tuniv ->
  typing (Γ ++ A) B Core.tuniv ->
  conv Γ M0 M0' (Core.tsig A B) ->
  semantic_typing Γ A Core.tuniv ->
  semantic_typing (Γ ++ A) B Core.tuniv ->
  semantic_conv2 Γ M0 M0' (Core.tsig A B) ->
(* ------------------------- *)
  semantic_conv2 Γ (Core.psnd M0) (Core.psnd M0') B[(Core.pfst M0)..].
Proof.
  move=> TA TB CM STA STB SCM.
  have TM : typing Γ M0 (Core.tsig A B) := proj1 (conv_typing CM).
  move=> ρ m Δ σ TS FR VS CD u a WT evS evB.
  have Vρ : valid_env ρ := fits_valid_env FR.
  have TAs : typing Δ A[σ] Core.tuniv
    by (move: (substitution_tm _ _ _ _ _ TA TS CD) => hh; cbn in hh; exact hh).
  have CE : ctx (Δ ++ A[σ]) by (eapply c_cons; eauto).
  have TSE : typing_subst (Δ ++ A[σ]) (⇑ σ) (Γ ++ A) by (eapply typing_subst_lift; eauto).
  have TBs : typing (Δ ++ A[σ]) B[⇑ σ] Core.tuniv.
  { have CC : typing (Δ ++ A[σ]) B[⇑ σ] Core.tuniv[⇑ σ] by (eapply substitution_tm; eauto).
    cbn in CC. exact CC. }
  have TMσ : typing Δ M0[σ] (Core.tsig A[σ] B[⇑ σ])
    by (move: (substitution_tm _ _ _ _ _ TM TS CD) => hh; cbn in hh; exact hh).
  have TFσ : typing Δ (Core.pfst M0[σ]) A[σ]
    by (eapply t_pfst; [ exact TAs | exact TBs | exact TMσ ]).
  have TFΓ : typing Γ (Core.pfst M0) A
    by (eapply t_pfst; [ exact TA | exact TB | exact TM ]).
  have evU : EvalRel Core.tuniv ρ tuniv by (cbn; apply le_refl).
  rewrite subst1_subst_comm. cbn.
  move=> RB Hrank.
  destruct (is_bot u) eqn:Hu.
  { have Eu : u = bot by (apply is_bot_eq; rewrite Hu). subst u. apply EqVal_Bot. }
  cbn in evS. rewrite Hu in evS. move: evS => [x evMk].
  have IT : InvTyped Γ M0 (Core.tsig A B) ρ := typing_EvalRel TM FR.
  have [ubig [abig [WTbig [LEbig [evMbig evSig]]]]] := IT (mkpair x u) evMk.
  have [u1 [y1 [Eub [LEx1 LEu1]]]] := le_mkpair_inv LEbig. subst ubig.
  destruct abig as [ | | | | | | | | | b f | | ];
    try solve [ exfalso; clear -WTbig; inversion WTbig ].
  have evSigC := evSig. cbn in evSigC. move: evSigC => [Vb [Vf [evA_b _]]].
  pose RBf := S (max (max (rk (mkpair u1 y1)) (rk (tsig b f))) (max (rk u) (rk a))).
  have HfM : max (rk (mkpair u1 y1)) (rk (tsig b f)) < S (S RBf) by (unfold RBf; lia).
  have EM := SCM ρ m Δ σ TS FR VS CD (mkpair u1 y1) (tsig b f) WTbig evMbig evSig
               (S (S RBf)) HfM.
  rewrite EqVal_mkpair in EM.
  move: EM => [VTyS [VPrM [VPrN EPr]]].
  move: (VPrM) => [A0 [B0 [HRs [CTs [M1 [M2 [HRp [CTp [T1 [T2 [V1 V2]]]]]]]]]]].
  asimpl in HRs. have [EA0 EB0] := HeadRed_tsig_eq HRs. subst A0 B0.
  move: (VPrN) => [A1 [B1 [HRs1 [CTs1 [N1 [N2 [HRp1 [CTp1 [T1' [T2' [V1' V2']]]]]]]]]]].
  asimpl in HRs1. have [EA1 EB1] := HeadRed_tsig_eq HRs1. subst A1 B1.
  move: EPr => [_ [_ [A2 [B2 [HRs2 [P1 [P2 [Q1 [Q2
                 [HRpM [HRpN [C1 [C2 [EF EFs]]]]]]]]]]]]]].
  asimpl in HRs2. have [EA2 EB2] := HeadRed_tsig_eq HRs2. subst A2 B2.
  have [ep1 ep2] := HeadRed_mkpair_det HRpM HRp. subst P1 P2.
  have [eq1 eq2] := HeadRed_mkpair_det HRpN HRp1. subst Q1 Q2.
  have HRf : HeadRed (Core.pfst M0[σ]) M1.
  { eapply relations.ms_app;
      [ eapply HeadRed_pfst; exact HRp
      | eapply ms_trans; [ apply hr_pfst | apply ms_refl ] ]. }
  have HRf' : HeadRed (Core.pfst M0'[σ]) N1.
  { eapply relations.ms_app;
      [ eapply HeadRed_pfst; exact HRp1
      | eapply ms_trans; [ apply hr_pfst | apply ms_refl ] ]. }
  have cvF : conv Δ (Core.pfst M0[σ]) M1 A[σ].
  { eapply c_trans.
    - eapply c_pfst; [ exact TAs | exact TBs | exact CTp ].
    - eapply c_beta_fst; [ exact TAs | exact TBs | exact T1 | exact T2 ]. }
  have TMσ' : typing Δ M0'[σ] (Core.tsig A[σ] B[⇑ σ]) := proj1 (conv_typing CTp1).
  have TFσ' : typing Δ (Core.pfst M0'[σ]) A[σ]
    by (eapply t_pfst; [ exact TAs | exact TBs | exact TMσ' ]).
  have cvF' : conv Δ (Core.pfst M0'[σ]) N1 A[σ].
  { eapply c_trans.
    - eapply c_pfst; [ exact TAs | exact TBs | exact CTp1 ].
    - eapply c_beta_fst; [ exact TAs | exact TBs | exact T1' | exact T2' ]. }
  have cvTy : conv Δ B[⇑ σ][M1..] B[⇑ σ][(Core.pfst M0[σ])..] Core.tuniv
    := conv_subst_arg Δ A[σ] B[⇑ σ] M1 (Core.pfst M0[σ]) TAs TBs T1 TFσ
         (c_sym _ _ _ _ _ cvF).
  have cvB_MN : conv Δ B[⇑ σ][M1..] B[⇑ σ][N1..] Core.tuniv
    := conv_subst_arg Δ A[σ] B[⇑ σ] M1 N1 TAs TBs T1 T1' C1.
  have cvB_FN : conv Δ B[⇑ σ][(Core.pfst M0'[σ])..] B[⇑ σ][N1..] Core.tuniv
    := conv_subst_arg Δ A[σ] B[⇑ σ] (Core.pfst M0'[σ]) N1 TAs TBs TFσ' T1' cvF'.
  have HRsnd : HeadRed (Core.psnd M0[σ]) M2.
  { eapply relations.ms_app;
      [ eapply HeadRed_psnd; exact HRp
      | eapply ms_trans; [ apply hr_psnd | apply ms_refl ] ]. }
  have HRsnd' : HeadRed (Core.psnd M0'[σ]) N2.
  { eapply relations.ms_app;
      [ eapply HeadRed_psnd; exact HRp1
      | eapply ms_trans; [ apply hr_psnd | apply ms_refl ] ]. }
  have cvSnd : conv Δ (Core.psnd M0[σ]) M2 B[⇑ σ][M1..].
  { eapply c_trans.
    - eapply c_conv;
        [ eapply c_psnd; [ exact TAs | exact TBs | exact CTp ]
        | apply c_sym; exact cvTy ].
    - eapply c_beta_snd; [ exact TAs | exact TBs | exact T1 | exact T2 ]. }
  have cvSnd' : conv Δ (Core.psnd M0'[σ]) N2 B[⇑ σ][M1..].
  { eapply c_conv; [ | apply c_sym; exact cvB_MN ].
    eapply c_trans.
    - eapply c_conv;
        [ eapply c_psnd; [ exact TAs | exact TBs | exact CTp1 ]
        | exact cvB_FN ].
    - eapply c_beta_snd; [ exact TAs | exact TBs | exact T1' | exact T2' ]. }
  have E2e : EqVal (S RBf) Δ (Core.psnd M0[σ]) (Core.psnd M0'[σ]) B[⇑ σ][M1..]
               (wt_mkpair_snd WTbig)
    by (eapply EqVal_headred_expand;
          [ exact HRsnd | exact HRsnd' | exact cvSnd | exact cvSnd' | exact EFs ]).
  rewrite ValTy_tsig in VTyS.
  move: (VTyS) => [A3 [B3 [HRs3 [TA3 [TB3 [vld3 [VDom3 [PEV3 PEE3]]]]]]]].
  asimpl in HRs3. have [E3 E4] := HeadRed_tsig_eq HRs3. subst A3 B3.
  have hpi : wt (tpi b f) tuniv := wt_tsig_tpi (wt_mkpair_ty WTbig).
  have Vu1 : valid u1 := wt_valid_tm (wt_mkpair_fst WTbig).
  have [uf [vf [Selg [Leuf Eqvf]]]] := selectionBelow Vf Vu1.
  have WTuf : wt uf b := wt_Selection (wt_tpi_dom hpi) Vf (wt_tpi_keys hpi) Selg.
  have EFst : EqVal (S RBf) Δ M1 (Core.pfst M0[σ]) A[σ] (wt_mkpair_fst WTbig).
  { eapply EqVal_headred_expand;
      [ apply ms_refl | exact HRf | apply c_refl; exact T1 | exact cvF | ].
    eapply Val_EqVal. exact V1. }
  have EFstS : EqVal (S RBf) Δ M1 (Core.pfst M0[σ]) A[σ] WTuf
    by (eapply restrictEqVal; [ exact Leuf | exact EFst ]).
  have Ecod := PEE3 uf vf Selg WTuf M1 (Core.pfst M0[σ])
                 (c_sym _ _ _ _ _ cvF) EFstS.
  subst vf.
  have ETy : EqValTy (S RBf) Δ B[⇑ σ][M1..] B[⇑ σ][(Core.pfst M0[σ])..]
               (wt_Selection_codU (wt_tsig_tpi (wt_mkpair_ty WTbig)) Selg).
  { eapply EqValTy_fuel_up_le; [ | eapply EqVal_EqValTy; exact Ecod ].
    have Hfa := rk_app f u1.
    have Hff : rk_fun f < rk (tsig b f) by (cbn; lia).
    unfold RBf; lia. }
  have E2t : EqVal (S RBf) Δ (Core.psnd M0[σ]) (Core.psnd M0'[σ])
               B[⇑ σ][(Core.pfst M0[σ])..] (wt_mkpair_snd WTbig).
  { eapply EqVal_EqVal_fwd;
      [ | | exact cvTy | exact E2e | exact ETy ].
    - have Hy : rk y1 <= rk (mkpair u1 y1) by (cbn; lia).
      unfold RBf; lia.
    - have Hfa := rk_app f u1.
      have Hff : rk_fun f < rk (tsig b f) by (cbn; lia).
      unfold RBf; lia. }
  have evFu1 : EvalRel (Core.pfst M0) ρ u1.
  { cbn. destruct (is_bot u1) eqn:Hu1; [ exact I | ]. exists y1. exact evMbig. }
  have EBapp : EvalRel B[(Core.pfst M0)..] ρ (app f u1)
    := sigma_cod_eval Vρ Vu1 evSig evFu1.
  have Ca : compatible a (app f u1)
    by (eapply EvalRel_compatible; [ exact Vρ | exact evB | exact EBapp ]).
  have Wa : wt a tuniv := wt_ty_tuniv WT.
  have Waf : wt (app f u1) tuniv := wt_ty_tuniv (wt_mkpair_snd WTbig).
  have hUc : wt (lub a (app f u1)) tuniv := wt_lub Wa Ca Waf.
  have ELub : EvalRel B[(Core.pfst M0)..] ρ (lub a (app f u1))
    := proj2 (EvalRel_compatible_lub Vρ evB EBapp) _ erefl.
  (* the argument obligation comes from [sc_pfst]'s [EqVal] (its left [Val]),
     so no [semantic_typing] of [M0] is needed here *)
  have SCF : semantic_conv2 Γ (Core.pfst M0) (Core.pfst M0') A
    by (eapply sc_pfst; [ exact TA | exact TB | exact CM | exact STA | exact SCM ]).
  have VNarg : forall v c0 (h : wt v c0), EvalRel (Core.pfst M0) ρ v -> EvalRel A ρ c0 ->
      forall RB0, max (rk v) (rk c0) < RB0 -> Val RB0 Δ (Core.pfst M0)[σ] A[σ] h
    by (move=> v c0 h ev ea RB0 Hr0;
        exact (EqVal_Val1 (SCF ρ m Δ σ TS FR VS CD v c0 h ev ea RB0 Hr0))).
  have VTc : Val (S RBf) Δ (B[⇑ σ][(Core.pfst M0)[σ] .: var]) Core.tuniv hUc.
  { eapply codomain_type_ValTy;
      [ exact TA | exact TFΓ | exact STA | exact STB | exact FR | exact TS
      | exact VS | exact CD | exact VNarg | exact ELub | ].
    have L := rk_lub a (app f u1).
    have Hfa := rk_app f u1.
    have Hff : rk_fun f < rk (tsig b f) by (cbn; lia).
    have Htu : rk tuniv <= rk (tsig b f) by (cbn; lia).
    unfold RBf; lia. }
  have Eres : EqVal (S RBf) Δ (Core.psnd M0[σ]) (Core.psnd M0'[σ])
                B[⇑ σ][(Core.pfst M0[σ])..] WT.
  { eapply EqVal_app_transport;
      [ exact Ca | exact LEu1 | cbn in VTc; exact VTc | exact E2t ]. }
  eapply (EqVal_fuel_any (k := S RBf) (k' := RB));
    [ unfold RBf; lia | unfold RBf; lia | lia | lia | exact Eres ].
Qed.

(** Pair congruence in the second component.  Both records live at the SAME
    type term [B[⇑ σ][M0[σ]..]] (the first components are literally equal), so
    no type transport is needed: the second side's record is built by hand from
    the conversion's own [EqVal], and the pair equality's first component is
    the diagonal. *)
Lemma sc_mkpair2 A (B : Tm (S n)) M0 N0 N0' :
  typing Γ A Core.tuniv ->
  typing (Γ ++ A) B Core.tuniv ->
  typing Γ M0 A ->
  conv Γ N0 N0' B[M0..] ->
  semantic_typing Γ A Core.tuniv ->
  semantic_typing (Γ ++ A) B Core.tuniv ->
  semantic_typing Γ M0 A ->
  semantic_conv2 Γ N0 N0' B[M0..] ->
(* ------------------------- *)
  semantic_conv2 Γ (Core.mkpair M0 N0) (Core.mkpair M0 N0') (Core.tsig A B).
Proof.
  move=> TA TB TM CN STA STB STM SCN.
  have TN : typing Γ N0 B[M0..] := proj1 (conv_typing CN).
  have TN' : typing Γ N0' B[M0..] := proj2 (conv_typing CN).
  move=> ρ m Δ σ TS FR VS CD u a WT evP evS.
  have Vρ : valid_env ρ := fits_valid_env FR.
  have TAs : typing Δ A[σ] Core.tuniv
    by (move: (substitution_tm _ _ _ _ _ TA TS CD) => hh; cbn in hh; exact hh).
  have CE : ctx (Δ ++ A[σ]) by (eapply c_cons; eauto).
  have TSE : typing_subst (Δ ++ A[σ]) (⇑ σ) (Γ ++ A) by (eapply typing_subst_lift; eauto).
  have TBs : typing (Δ ++ A[σ]) B[⇑ σ] Core.tuniv.
  { have CC : typing (Δ ++ A[σ]) B[⇑ σ] Core.tuniv[⇑ σ] by (eapply substitution_tm; eauto).
    cbn in CC. exact CC. }
  have TMs : typing Δ M0[σ] A[σ]
    by (eapply substitution_tm; [ exact TM | exact TS | exact CD ]).
  have TNs : typing Δ N0[σ] B[⇑ σ][M0[σ]..].
  { have hh : typing Δ (N0[σ]) (B[M0..][σ])
      by (eapply substitution_tm; [ exact TN | exact TS | exact CD ]).
    rewrite subst1_subst_comm in hh. exact hh. }
  have TNs' : typing Δ N0'[σ] B[⇑ σ][M0[σ]..].
  { have hh : typing Δ (N0'[σ]) (B[M0..][σ])
      by (eapply substitution_tm; [ exact TN' | exact TS | exact CD ]).
    rewrite subst1_subst_comm in hh. exact hh. }
  have convNN' : conv Δ N0[σ] N0'[σ] B[⇑ σ][M0[σ]..].
  { have hh : conv Δ (N0[σ]) (N0'[σ]) (B[M0..][σ])
      := substitution_conv Γ N0 N0' (B[M0..]) Δ σ CN TS CD.
    rewrite subst1_subst_comm in hh. exact hh. }
  have TSs : typing Δ (Core.tsig A[σ] B[⇑ σ]) Core.tuniv
    by (eapply t_tsig; [ exact TAs | exact TBs ]).
  have TPs : typing Δ (Core.mkpair M0[σ] N0[σ]) (Core.tsig A[σ] B[⇑ σ])
    by (eapply t_mkpair; [ exact TAs | exact TBs | exact TMs | exact TNs ]).
  have TPs' : typing Δ (Core.mkpair M0[σ] N0'[σ]) (Core.tsig A[σ] B[⇑ σ])
    by (eapply t_mkpair; [ exact TAs | exact TBs | exact TMs | exact TNs' ]).
  have evU : EvalRel Core.tuniv ρ tuniv by (cbn; apply le_refl).
  have evP0 := evP. have evS0 := evS.
  move=> RB Hrank. destruct RB; [ exact I | ].
  destruct a as [ | | | | | | | | | b f | | ]; try done.
  destruct u as [ | | | | | | | | | | x y | ]; try done.
  cbn in evP. move: evP => [Vxy [EMx ENy]].
  have Vx : valid x by (eapply valid_mkpair1; exact Vxy).
  have evSc := evS. cbn in evSc. move: evSc => [Vb [Vf [evA_b _]]].
  have EBapp : EvalRel B[M0..] ρ (app f x) := sigma_cod_eval Vρ Vx evS0 EMx.
  rewrite EqVal_mkpair.
  (* the type record *)
  have VTy : Val (S RB) Δ (Core.tsig A B)[σ] Core.tuniv[σ] (wt_mkpair_ty WT).
  { eapply st_tsig_Val_edge with (σ' := σ); try eassumption.
    - exact (ConvSub_refl TS).
    - exact (ValSub_EqValSub VS).
    - cbn in Hrank |- *; lia. }
  split; [ eapply Val_ValTy; exact VTy | ].
  (* the components' relations *)
  have [valM _] :=
    STM ρ m Δ σ σ TS TS (ConvSub_refl TS) FR VS VS (ValSub_EqValSub VS) CD
        x b (wt_mkpair_fst WT) EMx evA_b.
  have VM1 : Val RB Δ M0[σ] A[σ] (wt_mkpair_fst WT)
    by (eapply valM; cbn in Hrank |- *; lia).
  have ENN' : EqVal RB Δ N0[σ] N0'[σ] B[⇑ σ][M0[σ]..] (wt_mkpair_snd WT).
  { rewrite -subst1_subst_comm.
    eapply (SCN ρ m Δ σ TS FR VS CD y (app f x) (wt_mkpair_snd WT) ENy EBapp).
    move: (rk_app f x) => Hax; cbn in Hrank |- *; lia. }
  (* the first side's pair record, by hand *)
  have VPrM : ValPair RB Δ (Core.mkpair M0 N0)[σ] (Core.tsig A B)[σ] WT.
  { exists A[σ]. exists B[⇑ σ]. split; [ apply ms_refl | ].
    split; [ apply c_refl; exact TSs | ].
    exists M0[σ]. exists N0[σ]. split; [ apply ms_refl | ].
    split; [ apply c_refl; exact TPs | ].
    split; [ exact TMs | ]. split; [ exact TNs | ].
    split; [ exact VM1 | exact (EqVal_Val1 ENN') ]. }
  split; [ exact VPrM | ].
  (* the second side's pair record *)
  have VPrN : ValPair RB Δ (Core.mkpair M0 N0')[σ] (Core.tsig A B)[σ] WT.
  { exists A[σ]. exists B[⇑ σ]. split; [ apply ms_refl | ].
    split; [ apply c_refl; exact TSs | ].
    exists M0[σ]. exists N0'[σ]. split; [ apply ms_refl | ].
    split; [ apply c_refl; exact TPs' | ].
    split; [ exact TMs | ]. split; [ exact TNs' | ].
    split; [ exact VM1 | exact (EqVal_Val2 ENN') ]. }
  split; [ exact VPrN | ].
  (* the pair equality *)
  split; [ exact VPrM | ]. split; [ exact VPrN | ].
  exists A[σ]. exists B[⇑ σ]. split; [ apply ms_refl | ].
  exists M0[σ]. exists N0[σ]. exists M0[σ]. exists N0'[σ].
  split; [ apply ms_refl | ]. split; [ apply ms_refl | ].
  split; [ apply c_refl; exact TMs | ].
  split; [ exact convNN' | ].
  split; [ eapply Val_EqVal; exact VM1 | exact ENN' ].
Qed.

(** Pair congruence in the first component.  Here the two records live at
    DIFFERENT type terms for their second component ([B[⇑ σ][M0[σ]..]] vs
    [B[⇑ σ][M0'[σ]..]]), so the second side's [Val] is obtained by a type
    transport whose [EqValTy] is the type record's [PiEdgeEq] at the canonical
    selection below [x] -- the same move [EqValPair_sym] makes internally. *)
Lemma sc_mkpair1 A (B : Tm (S n)) M0 M0' N0 :
  typing Γ A Core.tuniv ->
  typing (Γ ++ A) B Core.tuniv ->
  conv Γ M0 M0' A ->
  typing Γ N0 B[M0..] ->
  semantic_typing Γ A Core.tuniv ->
  semantic_typing (Γ ++ A) B Core.tuniv ->
  semantic_typing Γ N0 B[M0..] ->
  semantic_conv2 Γ M0 M0' A ->
(* ------------------------- *)
  semantic_conv2 Γ (Core.mkpair M0 N0) (Core.mkpair M0' N0) (Core.tsig A B).
Proof.
  move=> TA TB CM TN STA STB STN SCM.
  have TM : typing Γ M0 A := proj1 (conv_typing CM).
  have TM' : typing Γ M0' A := proj2 (conv_typing CM).
  move=> ρ m Δ σ TS FR VS CD u a WT evP evS.
  have Vρ : valid_env ρ := fits_valid_env FR.
  have TAs : typing Δ A[σ] Core.tuniv
    by (move: (substitution_tm _ _ _ _ _ TA TS CD) => hh; cbn in hh; exact hh).
  have CE : ctx (Δ ++ A[σ]) by (eapply c_cons; eauto).
  have TSE : typing_subst (Δ ++ A[σ]) (⇑ σ) (Γ ++ A) by (eapply typing_subst_lift; eauto).
  have TBs : typing (Δ ++ A[σ]) B[⇑ σ] Core.tuniv.
  { have CC : typing (Δ ++ A[σ]) B[⇑ σ] Core.tuniv[⇑ σ] by (eapply substitution_tm; eauto).
    cbn in CC. exact CC. }
  have TMs : typing Δ M0[σ] A[σ]
    by (eapply substitution_tm; [ exact TM | exact TS | exact CD ]).
  have TMs' : typing Δ M0'[σ] A[σ]
    by (eapply substitution_tm; [ exact TM' | exact TS | exact CD ]).
  have convMM' : conv Δ M0[σ] M0'[σ] A[σ]
    := substitution_conv Γ M0 M0' A Δ σ CM TS CD.
  have TNs : typing Δ N0[σ] B[⇑ σ][M0[σ]..].
  { have hh : typing Δ (N0[σ]) (B[M0..][σ])
      by (eapply substitution_tm; [ exact TN | exact TS | exact CD ]).
    rewrite subst1_subst_comm in hh. exact hh. }
  have cvB : conv Δ B[⇑ σ][M0[σ]..] B[⇑ σ][M0'[σ]..] Core.tuniv
    := conv_subst_arg Δ A[σ] B[⇑ σ] M0[σ] M0'[σ] TAs TBs TMs TMs' convMM'.
  have TNs' : typing Δ N0[σ] B[⇑ σ][M0'[σ]..]
    by (eapply t_conv; [ exact TNs | exact cvB ]).
  have TSs : typing Δ (Core.tsig A[σ] B[⇑ σ]) Core.tuniv
    by (eapply t_tsig; [ exact TAs | exact TBs ]).
  have TPs : typing Δ (Core.mkpair M0[σ] N0[σ]) (Core.tsig A[σ] B[⇑ σ])
    by (eapply t_mkpair; [ exact TAs | exact TBs | exact TMs | exact TNs ]).
  have TPs' : typing Δ (Core.mkpair M0'[σ] N0[σ]) (Core.tsig A[σ] B[⇑ σ])
    by (eapply t_mkpair; [ exact TAs | exact TBs | exact TMs' | exact TNs' ]).
  have evU : EvalRel Core.tuniv ρ tuniv by (cbn; apply le_refl).
  have evP0 := evP. have evS0 := evS.
  move=> RB Hrank. destruct RB; [ exact I | ].
  destruct a as [ | | | | | | | | | b f | | ]; try done.
  destruct u as [ | | | | | | | | | | x y | ]; try done.
  cbn in evP. move: evP => [Vxy [EMx ENy]].
  have Vx : valid x by (eapply valid_mkpair1; exact Vxy).
  have evSc := evS. cbn in evSc. move: evSc => [Vb [Vf [evA_b _]]].
  have EBapp : EvalRel B[M0..] ρ (app f x) := sigma_cod_eval Vρ Vx evS0 EMx.
  rewrite EqVal_mkpair.
  (* the type record, at a fuel one above so that its [PiEdgeEq] lands at
     [S RB] and [EqVal_EqValTy] gives an [EqValTy] at [RB] *)
  have VTy2 : Val (S (S RB)) Δ (Core.tsig A B)[σ] Core.tuniv[σ] (wt_mkpair_ty WT).
  { eapply st_tsig_Val_edge with (σ' := σ); try eassumption.
    - exact (ConvSub_refl TS).
    - exact (ValSub_EqValSub VS).
    - cbn in Hrank |- *; lia. }
  have VTyS : ValTy (S RB) Δ (Core.tsig A B)[σ] (wt_mkpair_ty WT)
    := Val_ValTy VTy2.
  split; [ eapply ValTy_fuel_down_le; [ cbn in Hrank |- *; lia | exact VTyS ] | ].
  (* the first components' relation, and the second component's [Val] *)
  have EM1 : EqVal (S RB) Δ M0[σ] M0'[σ] A[σ] (wt_mkpair_fst WT).
  { eapply (SCM ρ m Δ σ TS FR VS CD x b (wt_mkpair_fst WT) EMx evA_b).
    cbn in Hrank |- *; lia. }
  have [valN _] :=
    STN ρ m Δ σ σ TS TS (ConvSub_refl TS) FR VS VS (ValSub_EqValSub VS) CD
        y (app f x) (wt_mkpair_snd WT) ENy EBapp.
  have VN2 : Val (S RB) Δ N0[σ] B[⇑ σ][M0[σ]..] (wt_mkpair_snd WT).
  { rewrite -subst1_subst_comm.
    eapply valN; move: (rk_app f x) => Hax; cbn in Hrank |- *; lia. }
  (* the first side's pair record, by hand: its components are the [SCM]/[STN]
     data, so no [semantic_typing] of [M0] is needed *)
  have VPrM : ValPair RB Δ (Core.mkpair M0 N0)[σ] (Core.tsig A B)[σ] WT.
  { exists A[σ]. exists B[⇑ σ]. split; [ apply ms_refl | ].
    split; [ apply c_refl; exact TSs | ].
    exists M0[σ]. exists N0[σ]. split; [ apply ms_refl | ].
    split; [ apply c_refl; exact TPs | ].
    split; [ exact TMs | ]. split; [ exact TNs | ].
    split.
    - eapply Val_fuel_any; [ | | | | exact (EqVal_Val1 EM1) ];
        cbn in Hrank |- *; lia.
    - eapply Val_fuel_any; [ | | | | exact VN2 ];
        move: (rk_app f x) => Hax; cbn in Hrank |- *; lia. }
  split; [ exact VPrM | ].
  (* the codomain type equality along [M0[σ] -> M0'[σ]] *)
  rewrite ValTy_tsig in VTyS.
  move: (VTyS) => [A3 [B3 [HRs3 [TA3 [TB3 [vld3 [VDom3 [PEV3 PEE3]]]]]]]].
  asimpl in HRs3. have [E3 E4] := HeadRed_tsig_eq HRs3. subst A3 B3.
  have hpi : wt (tpi b f) tuniv := wt_tsig_tpi (wt_mkpair_ty WT).
  have [uf [vf [Selg [Leuf Eqvf]]]] := selectionBelow Vf Vx.
  have WTuf : wt uf b := wt_Selection (wt_tpi_dom hpi) Vf (wt_tpi_keys hpi) Selg.
  have EM1S : EqVal (S RB) Δ M0[σ] M0'[σ] A[σ] WTuf
    by (eapply restrictEqVal; [ exact Leuf | exact EM1 ]).
  have Ecod := PEE3 uf vf Selg WTuf M0[σ] M0'[σ] convMM' EM1S.
  subst vf.
  have ETy : EqValTy (S RB) Δ B[⇑ σ][M0[σ]..] B[⇑ σ][M0'[σ]..]
               (wt_Selection_codU (wt_tsig_tpi (wt_mkpair_ty WT)) Selg).
  { eapply EqValTy_fuel_up_le; [ | eapply EqVal_EqValTy; exact Ecod ].
    have Hfa := rk_app f x.
    have Hff : rk_fun f < rk (tsig b f) by (cbn; lia).
    cbn in Hrank; lia. }
  have VN2' : Val (S RB) Δ N0[σ] B[⇑ σ][M0'[σ]..] (wt_mkpair_snd WT).
  { eapply Val_EqVal_fwd;
      [ | | exact cvB | exact VN2 | exact ETy ].
    - cbn in Hrank |- *; lia.
    - have Hfa := rk_app f x.
      have Hff : rk_fun f < rk (tsig b f) by (cbn; lia).
      cbn in Hrank; lia. }
  (* the second side's pair record *)
  have VPrN : ValPair RB Δ (Core.mkpair M0' N0)[σ] (Core.tsig A B)[σ] WT.
  { exists A[σ]. exists B[⇑ σ]. split; [ apply ms_refl | ].
    split; [ apply c_refl; exact TSs | ].
    exists M0'[σ]. exists N0[σ]. split; [ apply ms_refl | ].
    split; [ apply c_refl; exact TPs' | ].
    split; [ exact TMs' | ]. split; [ exact TNs' | ].
    split.
    - eapply Val_fuel_any; [ | | | | exact (EqVal_Val2 EM1) ];
        cbn in Hrank |- *; lia.
    - eapply Val_fuel_any; [ | | | | exact VN2' ];
        move: (rk_app f x) => Hax; cbn in Hrank |- *; lia. }
  split; [ exact VPrN | ].
  (* the pair equality: first components from [SCM], second the diagonal *)
  split; [ exact VPrM | ]. split; [ exact VPrN | ].
  exists A[σ]. exists B[⇑ σ]. split; [ apply ms_refl | ].
  exists M0[σ]. exists N0[σ]. exists M0'[σ]. exists N0[σ].
  split; [ apply ms_refl | ]. split; [ apply ms_refl | ].
  split; [ exact convMM' | ].
  split; [ apply c_refl; exact TNs | ].
  split.
  - eapply EqVal_fuel_any; [ | | | | exact EM1 ]; cbn in Hrank |- *; lia.
  - eapply Val_EqVal.
    eapply Val_fuel_any; [ | | | | exact VN2 ];
      move: (rk_app f x) => Hax; cbn in Hrank |- *; lia.
Qed.

(** Surjective pairing.  The two sides do not head-reduce to one another, so
    both records have to be built: the right one is [M0]'s own record from
    [STM], and the left one is assembled from the projections, whose [Val]s are
    the right record's components moved along [HeadRed (pfst M0[σ]) N1] /
    [HeadRed (psnd M0[σ]) N2] (plus, for the second, the type transport
    [B[⇑ σ][N1..] -> B[⇑ σ][(pfst M0[σ])..]]).

    The one Σ-specific step is recovering [EvalRel M0 ρ (mkpair x y)] from the
    two projection evaluations: [EvalRel (pfst M0) ρ x] gives a pair
    [(x, y')] and [EvalRel (psnd M0) ρ y] a pair [(x', y)], and their join is
    an evaluation of [M0] above [(x, y)] ([EvalRel_compatible_lub] +
    [EvalRel_down]).  A [bot] component has no witness, but then the other
    component's pair already dominates [(x, y)]. *)
Lemma sc_pair_eta A (B : Tm (S n)) M0 :
  typing Γ A Core.tuniv ->
  typing (Γ ++ A) B Core.tuniv ->
  typing Γ M0 (Core.tsig A B) ->
  semantic_typing Γ A Core.tuniv ->
  semantic_typing (Γ ++ A) B Core.tuniv ->
  semantic_typing Γ M0 (Core.tsig A B) ->
(* ------------------------- *)
  semantic_conv2 Γ (Core.mkpair (Core.pfst M0) (Core.psnd M0)) M0 (Core.tsig A B).
Proof.
  move=> TA TB TM STA STB STM.
  move=> ρ m Δ σ TS FR VS CD u a WT evP evS.
  have Vρ : valid_env ρ := fits_valid_env FR.
  have TAs : typing Δ A[σ] Core.tuniv
    by (move: (substitution_tm _ _ _ _ _ TA TS CD) => hh; cbn in hh; exact hh).
  have CE : ctx (Δ ++ A[σ]) by (eapply c_cons; eauto).
  have TSE : typing_subst (Δ ++ A[σ]) (⇑ σ) (Γ ++ A) by (eapply typing_subst_lift; eauto).
  have TBs : typing (Δ ++ A[σ]) B[⇑ σ] Core.tuniv.
  { have CC : typing (Δ ++ A[σ]) B[⇑ σ] Core.tuniv[⇑ σ] by (eapply substitution_tm; eauto).
    cbn in CC. exact CC. }
  have TMσ : typing Δ M0[σ] (Core.tsig A[σ] B[⇑ σ])
    by (move: (substitution_tm _ _ _ _ _ TM TS CD) => hh; cbn in hh; exact hh).
  have TFσ : typing Δ (Core.pfst M0[σ]) A[σ]
    by (eapply t_pfst; [ exact TAs | exact TBs | exact TMσ ]).
  have TSndσ : typing Δ (Core.psnd M0[σ]) B[⇑ σ][(Core.pfst M0[σ])..]
    by (eapply t_psnd; [ exact TAs | exact TBs | exact TMσ ]).
  have TSs : typing Δ (Core.tsig A[σ] B[⇑ σ]) Core.tuniv
    by (eapply t_tsig; [ exact TAs | exact TBs ]).
  have TPl : typing Δ (Core.mkpair (Core.pfst M0[σ]) (Core.psnd M0[σ]))
               (Core.tsig A[σ] B[⇑ σ])
    by (eapply t_mkpair; [ exact TAs | exact TBs | exact TFσ | exact TSndσ ]).
  have evU : EvalRel Core.tuniv ρ tuniv by (cbn; apply le_refl).
  have evP0 := evP. have evS0 := evS.
  move=> RB Hrank. destruct RB; [ exact I | ].
  destruct a as [ | | | | | | | | | b f | | ]; try done.
  destruct u as [ | | | | | | | | | | x y | ]; try done.
  cbn in evP. move: evP => [Vxy [EFx ESy]].
  have Vx : valid x by (eapply valid_mkpair1; exact Vxy).
  have Vy : valid y by (eapply valid_mkpair2; exact Vxy).
  have NBxy : ~~ (is_bot x && is_bot y) by (eapply valid_mkpair3; exact Vxy).
  have Vp : valid (mkpair x y) := Vxy.
  have evSc := evS. cbn in evSc. move: evSc => [Vb [Vf [evA_b _]]].
  (* ---- recover an evaluation of [M0] at the pair code itself ---- *)
  have EM0 : EvalRel M0 ρ (mkpair x y).
  { destruct (is_bot x) eqn:Hx.
    - (* x = bot: the [psnd] witness's pair already dominates [(x, y)] *)
      have Ex : x = bot by (apply is_bot_eq; rewrite Hx).
      destruct (is_bot y) eqn:Hy.
      { exfalso. by move: NBxy. }
      move: ESy => [x' EM'].
      eapply EvalRel_down; [ exact Vρ | exact Vp | exact EM' | ].
      rewrite Ex. apply le_mkpair_intro; [ apply le_bot' | apply le_refl; exact Vy ].
    - destruct (is_bot y) eqn:Hy.
      + (* y = bot: the [pfst] witness's pair dominates *)
        have Ey : y = bot by (apply is_bot_eq; rewrite Hy).
        move: EFx => [y' EM'].
        eapply EvalRel_down; [ exact Vρ | exact Vp | exact EM' | ].
        rewrite Ey. apply le_mkpair_intro; [ apply le_refl; exact Vx | apply le_bot' ].
      + (* both informative: the two pairs' join dominates [(x, y)] *)
        move: EFx => [y' EM1]. move: ESy => [x' EM2].
        have Vp1 : valid (mkpair x y') := EvalRel_valid EM1.
        have Vp2 : valid (mkpair x' y) := EvalRel_valid EM2.
        have Vy' : valid y' by (eapply valid_mkpair2; exact Vp1).
        have Vx' : valid x' by (eapply valid_mkpair1; exact Vp2).
        have Cp : compatible (mkpair x y') (mkpair x' y)
          by (eapply EvalRel_compatible; [ exact Vρ | exact EM1 | exact EM2 ]).
        have EJ : EvalRel M0 ρ (lub (mkpair x y') (mkpair x' y))
          := proj2 (EvalRel_compatible_lub Vρ EM1 EM2) _ erefl.
        cbn in Cp. case/andP: Cp => Cx Cy.
        cbn in EJ.
        eapply EvalRel_down; [ exact Vρ | exact Vp | exact EJ | ].
        apply le_mkpair_intro.
        * apply le_lub_left; [ exact Cx | exact Vx | exact Vx' ].
        * apply le_lub_right; [ exact Cy | exact Vy' | exact Vy ]. }
  (* ---- [M0]'s own record, at two fuels ---- *)
  have [valM _] :=
    STM ρ m Δ σ σ TS TS (ConvSub_refl TS) FR VS VS (ValSub_EqValSub VS) CD
        (mkpair x y) (tsig b f) WT EM0 evS0.
  have VM := valM (S RB) Hrank.
  rewrite Val_mkpair in VM. move: VM => [VTyd VPrM0].
  have VM2 : Val (S (S RB)) Δ M0[σ] (Core.tsig A B)[σ] WT
    by (eapply valM; cbn in Hrank |- *; lia).
  rewrite Val_mkpair in VM2. move: VM2 => [VTyS _].
  move: (VPrM0) => [A0 [B0 [HRs [CTs [N1 [N2 [HRp [CTp [T1 [T2 [V1 V2]]]]]]]]]]].
  asimpl in HRs. have [EA0 EB0] := HeadRed_tsig_eq HRs. subst A0 B0.
  (* ---- the two projections reduce into the record's components ---- *)
  have HRf : HeadRed (Core.pfst M0[σ]) N1.
  { eapply relations.ms_app;
      [ eapply HeadRed_pfst; exact HRp
      | eapply ms_trans; [ apply hr_pfst | apply ms_refl ] ]. }
  have HRsnd : HeadRed (Core.psnd M0[σ]) N2.
  { eapply relations.ms_app;
      [ eapply HeadRed_psnd; exact HRp
      | eapply ms_trans; [ apply hr_psnd | apply ms_refl ] ]. }
  have cvF : conv Δ (Core.pfst M0[σ]) N1 A[σ].
  { eapply c_trans.
    - eapply c_pfst; [ exact TAs | exact TBs | exact CTp ].
    - eapply c_beta_fst; [ exact TAs | exact TBs | exact T1 | exact T2 ]. }
  have cvTy : conv Δ B[⇑ σ][N1..] B[⇑ σ][(Core.pfst M0[σ])..] Core.tuniv
    := conv_subst_arg Δ A[σ] B[⇑ σ] N1 (Core.pfst M0[σ]) TAs TBs T1 TFσ
         (c_sym _ _ _ _ _ cvF).
  have cvSnd : conv Δ (Core.psnd M0[σ]) N2 B[⇑ σ][N1..].
  { eapply c_trans.
    - eapply c_conv;
        [ eapply c_psnd; [ exact TAs | exact TBs | exact CTp ]
        | apply c_sym; exact cvTy ].
    - eapply c_beta_snd; [ exact TAs | exact TBs | exact T1 | exact T2 ]. }
  (* ---- the codomain type equality [B[N1..] = B[(pfst M0[σ])..]] ---- *)
  rewrite ValTy_tsig in VTyS.
  move: (VTyS) => [A3 [B3 [HRs3 [TA3 [TB3 [vld3 [VDom3 [PEV3 PEE3]]]]]]]].
  asimpl in HRs3. have [E3 E4] := HeadRed_tsig_eq HRs3. subst A3 B3.
  have hpi : wt (tpi b f) tuniv := wt_tsig_tpi (wt_mkpair_ty WT).
  have [uf [vf [Selg [Leuf Eqvf]]]] := selectionBelow Vf Vx.
  have WTuf : wt uf b := wt_Selection (wt_tpi_dom hpi) Vf (wt_tpi_keys hpi) Selg.
  have EFst : EqVal (S RB) Δ N1 (Core.pfst M0[σ]) A[σ] (wt_mkpair_fst WT).
  { eapply EqVal_headred_expand;
      [ apply ms_refl | exact HRf | apply c_refl; exact T1 | exact cvF | ].
    eapply Val_EqVal.
    eapply Val_fuel_any; [ | | | | exact V1 ]; cbn in Hrank |- *; lia. }
  have EFstS : EqVal (S RB) Δ N1 (Core.pfst M0[σ]) A[σ] WTuf
    by (eapply restrictEqVal; [ exact Leuf | exact EFst ]).
  have Ecod := PEE3 uf vf Selg WTuf N1 (Core.pfst M0[σ])
                 (c_sym _ _ _ _ _ cvF) EFstS.
  subst vf.
  have ETy : EqValTy RB Δ B[⇑ σ][N1..] B[⇑ σ][(Core.pfst M0[σ])..]
               (wt_Selection_codU (wt_tsig_tpi (wt_mkpair_ty WT)) Selg)
    := EqVal_EqValTy Ecod.
  (* ---- the left record's two components ---- *)
  have VF : Val RB Δ (Core.pfst M0[σ]) A[σ] (wt_mkpair_fst WT)
    by (eapply Val_beta_expand; [ exact HRf | exact cvF | exact V1 ]).
  have VS2 : Val RB Δ (Core.psnd M0[σ]) B[⇑ σ][N1..] (wt_mkpair_snd WT)
    by (eapply Val_beta_expand; [ exact HRsnd | exact cvSnd | exact V2 ]).
  have VS2' : Val RB Δ (Core.psnd M0[σ]) B[⇑ σ][(Core.pfst M0[σ])..]
                (wt_mkpair_snd WT).
  { eapply Val_EqVal_fwd;
      [ | | exact cvTy | exact VS2 | exact ETy ].
    - cbn in Hrank |- *; lia.
    - have Hfa := rk_app f x.
      have Hff : rk_fun f < rk (tsig b f) by (cbn; lia).
      cbn in Hrank; lia. }
  have VPrL : ValPair RB Δ (Core.mkpair (Core.pfst M0) (Core.psnd M0))[σ]
                (Core.tsig A B)[σ] WT.
  { exists A[σ]. exists B[⇑ σ]. split; [ apply ms_refl | ].
    split; [ apply c_refl; exact TSs | ].
    exists (Core.pfst M0[σ]). exists (Core.psnd M0[σ]).
    split; [ apply ms_refl | ]. split; [ apply c_refl; exact TPl | ].
    split; [ exact TFσ | ]. split; [ exact TSndσ | ].
    split; [ exact VF | exact VS2' ]. }
  (* ---- assemble ---- *)
  rewrite EqVal_mkpair.
  split; [ exact VTyd | ]. split; [ exact VPrL | ]. split; [ exact VPrM0 | ].
  split; [ exact VPrL | ]. split; [ exact VPrM0 | ].
  exists A[σ]. exists B[⇑ σ]. split; [ apply ms_refl | ].
  exists (Core.pfst M0[σ]). exists (Core.psnd M0[σ]). exists N1. exists N2.
  split; [ apply ms_refl | ]. split; [ exact HRp | ].
  split; [ exact cvF | ].
  split; [ eapply c_conv; [ exact cvSnd | exact cvTy ] | ].
  split.
  - eapply EqVal_sym;
      [ cbn in Hrank |- *; lia | cbn in Hrank |- *; lia | ].
    eapply EqVal_fuel_any; [ | | | | exact EFst ]; cbn in Hrank |- *; lia.
  - (* the second components, at the LEFT record's type term *)
    eapply EqVal_EqVal_fwd;
      [ | | exact cvTy | | exact ETy ].
    + cbn in Hrank |- *; lia.
    + have Hfa := rk_app f x.
      have Hff : rk_fun f < rk (tsig b f) by (cbn; lia).
      cbn in Hrank; lia.
    + eapply EqVal_headred_expand;
        [ exact HRsnd | apply ms_refl | exact cvSnd | apply c_refl; exact T2 | ].
      eapply Val_EqVal. exact V2.
Qed.

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
  destruct u as [ | | | | | | g_val | | | | | ]; try done.
  - (* u = bot *) apply EqVal_Bot.
  - (* u = abs g_val *)
    destruct a as [ | | | | | b f_ty | | | | | | ];
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


(* ==================================================================
   The Prop fragment: the second sort.

   Agda: [ty-Prop], [ty-Prop-U], [ty-Pi-Prop], [conv-Prop], [conv-Prop-U],
   [conv-Pi-Prop] ([Adequacy5.agda]).  [Val]/[EqVal] at a [tprop] TYPE code is
   the [tuniv] content at the [wt_prop_univ]-lifted code (raw_validity's
   [Val_prop_to_univ]), which is what makes all six rules cheap:

     - Pi-formation at [Prop] is [st_tpi]/[sc_tpi] plus that transfer;
     - the two Prop-to-U subtyping rules are the transfer, applied at a TYPED
       ENLARGEMENT of the given code (Agda's [theorem1], here
       [typing_EvalRel]), followed by [restrictVal] back down to the code --
       this is Agda's [adequacySub2-Prop-U-PiCode];
     - proof irrelevance is [InvTyped_prop_bot]: every approximation of a term
       at a Prop type is [bot], where [EqVal] is total ([EqVal_Bot]).
   ================================================================== *)

(** [Prop : U] -- the second sort is itself a type.  [tprop] is a code leaf,
    so this is [st_univ] verbatim. *)
Lemma st_prop :
  ctx Γ ->
(* ------------------------- *)
  semantic_typing Γ Core.tprop Core.tuniv.
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

(** Prop-to-U subtyping ([ty-Prop-U]).  Stated at an arbitrary context, since
    [st_tpi_prop] below needs it at the extended one. *)
Lemma st_prop_u {q} (Δ0 : Ctx q) (A : Tm q) :
  typing Δ0 A Core.tprop ->
  semantic_typing Δ0 A Core.tprop ->
(* ------------------------- *)
  semantic_typing Δ0 A Core.tuniv.
Proof.
  move=> TA STA.
  move=> ρ m Δ σ σ' TS TS' CS Fρ VS VS' EVS CΔ u a WT EM EU.
  cbn in EU.
  destruct a; cbn in EU; try done.
  - (* the given type code is [bot], hence so is the element *)
    move: (wt_bot_inv WT) => Eu. subst u.
    split; move=> RB _; [ apply Val_Bot | apply EqVal_Bot ].
  - (* the given type code is [tuniv]: take the typed enlargement [u'] of [u]
       -- it inhabits [tprop] -- run the IH there, transfer to [tuniv], and
       restrict back down to [u]. *)
    have IA : InvTyped Δ0 A Core.tprop ρ := typing_EvalRel TA Fρ.
    move: (IA u EM) => [u' [c [WT' [LEu [EMu' Ec]]]]].
    cbn in Ec.
    have evP : EvalRel Core.tprop ρ tprop by (cbn; apply le_refl).
    case: (le_tprop_inv_r _ Ec) => Ecc; subst c.
    + (* the enlargement's type code is [bot], so [u] is [bot] *)
      move: (wt_bot_inv WT') => Eu'; subst u'.
      move: (le_bot_inv _ LEu) => Eu; subst u.
      split; move=> RB _; [ apply Val_Bot | apply EqVal_Bot ].
    + move: (STA ρ m Δ σ σ' TS TS' CS Fρ VS VS' EVS CΔ u' tprop WT' EMu' evP)
        => [Vh Eh].
      split.
      * move=> RB Hrank.
        set kh := max RB (S (max (rk u') 1)).
        have HRB : RB <= S kh by (rewrite /kh; lia).
        have H1 : max (rk u') (rk tprop) < S kh by (cbn; rewrite /kh; lia).
        have V2 : Val (S kh) Δ A[σ] Core.tuniv (wt_prop_univ WT')
          by (eapply Val_prop_to_univ; exact (Vh (S kh) H1)).
        have V3 : Val (S kh) Δ A[σ] Core.tuniv WT
          by (eapply restrictVal; [ exact LEu | exact V2 ]).
        eapply Val_fuel_down_to;
          [ exact HRB | cbn in Hrank |- *; lia | cbn in Hrank |- *; lia | exact V3 ].
      * move=> RB Hrank.
        set kh := max RB (S (max (rk u') 1)).
        have HRB : RB <= S kh by (rewrite /kh; lia).
        have H1 : max (rk u') (rk tprop) < S kh by (cbn; rewrite /kh; lia).
        have E2 : EqVal (S kh) Δ A[σ] A[σ'] Core.tuniv (wt_prop_univ WT')
          by (eapply EqVal_prop_to_univ; exact (Eh (S kh) H1)).
        have E3 : EqVal (S kh) Δ A[σ] A[σ'] Core.tuniv WT
          by (eapply restrictEqVal; [ exact LEu | exact E2 ]).
        eapply EqVal_fuel_down_to;
          [ exact HRB | cbn in Hrank |- *; lia | cbn in Hrank |- *; lia | exact E3 ].
Qed.

(** Prop-to-U subtyping on conversions ([conv-Prop-U]): [st_prop_u]'s binary
    half. *)
Lemma sc_prop_u {q} (Δ0 : Ctx q) (M N : Tm q) :
  conv Δ0 M N Core.tprop ->
  semantic_conv2 Δ0 M N Core.tprop ->
(* ------------------------- *)
  semantic_conv2 Δ0 M N Core.tuniv.
Proof.
  move=> CMN SC.
  move=> ρ m Δ σ TS Fρ VS CΔ u a WT EM EU RB Hrank.
  cbn in EU.
  have [TM _] := conv_typing CMN.
  destruct a; cbn in EU; try done.
  - move: (wt_bot_inv WT) => Eu. subst u. apply EqVal_Bot.
  - have IA : InvTyped Δ0 M Core.tprop ρ := typing_EvalRel TM Fρ.
    move: (IA u EM) => [u' [c [WT' [LEu [EMu' Ec]]]]].
    cbn in Ec.
    have evP : EvalRel Core.tprop ρ tprop by (cbn; apply le_refl).
    case: (le_tprop_inv_r _ Ec) => Ecc; subst c.
    + move: (wt_bot_inv WT') => Eu'; subst u'.
      move: (le_bot_inv _ LEu) => Eu; subst u. apply EqVal_Bot.
    + set kh := max RB (S (max (rk u') 1)).
      have HRB : RB <= S kh by (rewrite /kh; lia).
      have H1 : max (rk u') (rk tprop) < S kh by (cbn; rewrite /kh; lia).
      have E2 : EqVal (S kh) Δ M[σ] N[σ] Core.tuniv (wt_prop_univ WT')
        by (eapply EqVal_prop_to_univ;
            exact (SC ρ m Δ σ TS Fρ VS CΔ u' tprop WT' EMu' evP (S kh) H1)).
      have E3 : EqVal (S kh) Δ M[σ] N[σ] Core.tuniv WT
        by (eapply restrictEqVal; [ exact LEu | exact E2 ]).
      eapply EqVal_fuel_down_to;
        [ exact HRB | cbn in Hrank |- *; lia | cbn in Hrank |- *; lia | exact E3 ].
Qed.

(** Pi-formation at the second sort ([ty-Pi-Prop]): [st_tpi] with the codomain
    lifted to [tuniv], plus the [tprop]/[tuniv] transfer on the result. *)
Lemma st_tpi_prop A B :
  typing Γ A Core.tuniv ->
  typing (Γ ++ A) B Core.tprop ->
  semantic_typing Γ A Core.tuniv ->
  semantic_typing (Γ ++ A) B Core.tprop ->
(* ------------------------- *)
  semantic_typing Γ (Core.tpi A B) Core.tprop.
Proof.
  move=> TA TB STA STB.
  have TBu : typing (Γ ++ A) B Core.tuniv by (eapply t_prop_u; exact TB).
  have STBu : semantic_typing (Γ ++ A) B Core.tuniv
    by (eapply st_prop_u; [ exact TB | exact STB ]).
  have STPi := st_tpi TA TBu STA STBu.
  move=> ρ m Δ σ σ' TS TS' CS Fρ VS VS' EVS CΔ u a WT EM EU.
  cbn in EU.
  destruct a; cbn in EU; try done.
  - move: (wt_bot_inv WT) => Eu. subst u.
    split; move=> RB _; [ apply Val_Bot | apply EqVal_Bot ].
  - have WTu : wt u tuniv := wt_prop_univ WT.
    have evU : EvalRel Core.tuniv ρ tuniv by (cbn; apply le_refl).
    move: (STPi ρ m Δ σ σ' TS TS' CS Fρ VS VS' EVS CΔ u tuniv WTu EM evU)
      => [Vh Eh].
    split.
    + move=> RB Hrank. destruct RB as [|RB]; first (cbn in Hrank; lia).
      have V1 : Val (S RB) Δ (Core.tpi A B)[σ] Core.tuniv WTu
        by (eapply (Vh (S RB)); cbn in Hrank |- *; lia).
      eapply Val_univ_to_prop; exact V1.
    + move=> RB Hrank. destruct RB as [|RB]; first (cbn in Hrank; lia).
      have E1 : EqVal (S RB) Δ (Core.tpi A B)[σ] (Core.tpi A B)[σ'] Core.tuniv WTu
        by (eapply (Eh (S RB)); cbn in Hrank |- *; lia).
      eapply EqVal_univ_to_prop; exact E1.
Qed.

(** Proof irrelevance ([conv-Prop]): at a Prop type every approximation of the
    subject is [bot], and [EqVal] is total there. *)
Lemma sc_prop M N A :
  typing Γ A Core.tprop ->
  typing Γ M A ->
  typing Γ N A ->
(* ------------------------- *)
  semantic_conv2 Γ M N A.
Proof.
  move=> TA TM TN.
  move=> ρ m Δ σ TS Fρ VS CΔ u a WT EM EA RB Hrank.
  have IA : InvTyped Γ A Core.tprop ρ := typing_EvalRel TA Fρ.
  have IM : InvTyped Γ M A ρ := typing_EvalRel TM Fρ.
  have Eu : u = bot := InvTyped_prop_bot IA IM EM.
  subst u. apply EqVal_Bot.
Qed.

(** The Pi congruence at the second sort ([conv-Pi-Prop]): [sc_tpi] with the
    codomain conversion lifted, plus the transfer. *)
Lemma sc_tpi_prop A0 A1 (B0 B1 : Tm (S n)) :
  typing Γ A0 Core.tuniv ->
  typing Γ A1 Core.tuniv ->
  typing (Γ ++ A0) B0 Core.tprop ->
  typing (Γ ++ A1) B1 Core.tprop ->
  conv Γ A0 A1 Core.tuniv ->
  conv (Γ ++ A0) B0 B1 Core.tprop ->
  semantic_typing Γ A0 Core.tuniv ->
  semantic_typing Γ A1 Core.tuniv ->
  semantic_typing (Γ ++ A0) B0 Core.tprop ->
  semantic_typing (Γ ++ A1) B1 Core.tprop ->
  semantic_conv2 Γ A0 A1 Core.tuniv ->
  semantic_conv2 (Γ ++ A0) B0 B1 Core.tprop ->
(* ------------------------- *)
  semantic_conv2 Γ (Core.tpi A0 B0) (Core.tpi A1 B1) Core.tprop.
Proof.
  move=> TA0 TA1 TB0 TB1 CA CB STA0 STA1 STB0 STB1 SCA SCB.
  have TB0u : typing (Γ ++ A0) B0 Core.tuniv by (eapply t_prop_u; exact TB0).
  have TB1u : typing (Γ ++ A1) B1 Core.tuniv by (eapply t_prop_u; exact TB1).
  have CBu : conv (Γ ++ A0) B0 B1 Core.tuniv by (eapply c_prop_u; exact CB).
  have STB0u : semantic_typing (Γ ++ A0) B0 Core.tuniv
    by (eapply st_prop_u; [ exact TB0 | exact STB0 ]).
  have STB1u : semantic_typing (Γ ++ A1) B1 Core.tuniv
    by (eapply st_prop_u; [ exact TB1 | exact STB1 ]).
  have SCBu : semantic_conv2 (Γ ++ A0) B0 B1 Core.tuniv
    by (eapply sc_prop_u; [ exact CB | exact SCB ]).
  have SCPi := sc_tpi TA0 TA1 TB0u TB1u CA CBu
                      STA0 STA1 STB0u STB1u SCA SCBu.
  move=> ρ m Δ σ TS Fρ VS CΔ u a WT EM EU RB Hrank.
  cbn in EU.
  destruct a; cbn in EU; try done.
  - move: (wt_bot_inv WT) => Eu. subst u. apply EqVal_Bot.
  - have WTu : wt u tuniv := wt_prop_univ WT.
    have evU : EvalRel Core.tuniv ρ tuniv by (cbn; apply le_refl).
    destruct RB as [|RB]; first (cbn in Hrank; lia).
    have E1 : EqVal (S RB) Δ (Core.tpi A0 B0)[σ] (Core.tpi A1 B1)[σ] Core.tuniv WTu
      by (eapply (SCPi ρ m Δ σ TS Fρ VS CΔ u tuniv WTu EM evU);
          cbn in Hrank |- *; lia).
    eapply EqVal_univ_to_prop; exact E1.
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
  - move=> h. dependent destruction h; try prop_only.
    + eapply st_var; eauto.
    + eapply st_conv; eauto.
    + eapply st_abs; eauto.
    + eapply st_app; eauto.
    + eapply st_nat; eauto.
    + eapply st_zero; eauto.
    + eapply st_succ; eauto.
    + eapply st_case; eauto.
    + eapply st_fix; eauto.
    + eapply st_tid; eauto.
    + eapply st_rfl; eauto.
    + eapply st_jcase; eauto.
    + eapply st_tpi; eauto.
    + eapply st_univ; eauto.
    + eapply st_tsig; eauto.
    + eapply st_mkpair; eauto.
    + eapply st_pfst; eauto.
    + eapply st_psnd; eauto.
    + (* t_prop *) eapply st_prop; eauto.
    + (* t_prop_u *) eapply st_prop_u; eauto.
    + (* t_tpi_prop *) eapply st_tpi_prop; eauto.
  - move=> h. dependent destruction h; try prop_only.
    + eapply sc_conv; eauto.
    + eapply sc_refl; eauto. 
    + eapply sc_sym; eauto.
    + eapply sc_trans; eauto.
    + eapply sc_app1; eauto.
    + eapply sc_app2; eauto.
    + eapply sc_beta; eauto.
    + eapply sc_eta; eauto.
    + eapply sc_ncase_Z; eauto.
    + eapply sc_ncase_S; eauto.
    + eapply sc_ncase; eauto.
    + eapply sc_succ; eauto.
    + eapply sc_abs; eauto.
    + eapply sc_fix; eauto.
    + eapply sc_fix_cong; eauto.
    + eapply sc_tid; eauto.
    + eapply sc_rfl; eauto.
    + eapply sc_jcase_beta; eauto.
    + eapply sc_jcase; eauto.
    + eapply sc_tpi; eauto.
    + eapply sc_tsig; eauto.
    + eapply sc_beta_fst; eauto.
    + eapply sc_beta_snd; eauto.
    + eapply sc_pair_eta; eauto.
    + eapply sc_mkpair1; eauto.
    + eapply sc_mkpair2; eauto.
    + eapply sc_pfst; eauto.
    + eapply sc_psnd; eauto.
    + (* c_prop *) eapply sc_prop; eauto.
    + (* c_prop_u *) eapply sc_prop_u; eauto.
    + (* c_tpi_prop *) eapply sc_tpi_prop; eauto.
Qed.

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
  dependent destruction WT; try prop_only.
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

(* ===========================================================
   Sigma-injectivity (step 10 of sigma_extension_plan.md).

   The [piConv]/[piInjectivity] pair verbatim.  [EvalRel] at a [tsig] code is
   definitionally [EvalRel] at the matching [tpi] code
   ([EvalRel_tpi_tsig]), so even the trivial evaluation is shared.
   =========================================================== *)

Lemma evalRel_Sigma_trivial {n} (A : Tm n) (B : Tm (S n)) (ρ : Env n) :
  EvalRel (Core.tsig A B) ρ (tsig bot nil).
Proof. apply EvalRel_tpi_tsig. apply evalRel_Pi_trivial. Qed.

Lemma sigmaConv {n} (Γ : Ctx n) (A0 : Tm n) (B1 : Tm n) (F1 : Tm (S n)) :
  conv Γ A0 (Core.tsig B1 F1) Core.tuniv ->
  exists B0 F0,
    HeadRed A0 (Core.tsig B0 F0)
    /\ conv Γ B0 B1 Core.tuniv
    /\ conv (Γ ++ B0) F0 F1 Core.tuniv.
Proof.
  move=> d.
  have cΓ : ctx Γ by eapply conv_ctx; exact d.
  have WT : wt (tsig bot nil) tuniv.
  { apply: wt_tsig.
    - apply wt_bot. apply wt_tuniv.
    - move=> ui vi [].
    - move=> ui vi [].
    - done. }
  have evSig : EvalRel (Core.tsig B1 F1) bot_env (tsig bot nil)
    by apply evalRel_Sigma_trivial.
  have IC : InvConv Γ A0 (Core.tsig B1 F1) Core.tuniv bot_env.
  { eapply conv_EvalRel. exact d. exact (@fits_bot_env n Γ cΓ). }
  move: IC => [_ [_ [_ bwd]]].
  have evA0 : EvalRel A0 bot_env (tsig bot nil) by apply bwd; exact evSig.
  have evU : EvalRel Core.tuniv (@bot_env n) tuniv by [].
  have SCA : semantic_conv2 Γ A0 (Core.tsig B1 F1) Core.tuniv.
  { apply adequacyEqSub; exact d. }
  have EVfun : EqVal 2 Γ A0[var] (Core.tsig B1 F1)[var] Core.tuniv[var] WT.
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
  rewrite (instId'_Tm A0) (instId'_Tm (Core.tsig B1 F1)) (instId'_Tm Core.tuniv) in EV1.
  have EVT := EqVal_EqValTy EV1.
  clear EV1 EVfun.
  dependent destruction WT; try prop_only.
  rewrite EqValTy_tsig in EVT. cbn [Rec.EqValTySig] in EVT.
  move: EVT => [_ [_ [B0 [F0 [HRA0 [A' [B' [HRSig [cD [cC _]]]]]]]]]].
  have [EA EB] := HeadRed_tsig_eq HRSig. subst A' B'.
  exists B0, F0. split; [ exact HRA0 | split; [ exact cD | exact cC ] ].
Qed.

(** Σ-injectivity: a conversion between two Σ-types entails convertibility of
    the domains and codomains. *)
Lemma sigmaInjectivity {n} (Γ : Ctx n)
  (A0 A1 : Tm n) (B0 B1 : Tm (S n)) :
  conv Γ (Core.tsig A0 B0) (Core.tsig A1 B1) Core.tuniv ->
  conv Γ A0 A1 Core.tuniv /\
  conv (Γ ++ A0) B0 B1 Core.tuniv.
Proof.
  move=> H.
  destruct (sigmaConv H) as [B0' [F0' [HR [convD convC]]]].
  have [EQA EQB]: B0' = A0 /\ F0' = B0.
  { eapply HeadRed_tsig_det. exact HR. apply ms_refl. }
  subst B0' F0'.
  split; auto.
Qed.

Lemma tuniv_not_tsig {n} (Γ : Ctx n) (A : Tm n) (B : Tm (S n)) :
  ~ conv Γ Core.tuniv (Core.tsig A B) Core.tuniv.
Proof.
  move=> H. destruct (sigmaConv H) as [B0 [F0 [HR _]]].
  inversion HR; subst; try discriminate.
  match goal with [ S : HeadRed1 Core.tuniv _ |- _ ] => inversion S end.
Qed.

(* ===========================================================
   Id-injectivity (Agda [ID/IdInjectivity.agda]).

   Exactly the [piConv]/[piInjectivity] pair, one former along: evaluate both
   sides at the bottom environment, transfer the trivial identity code
   [tid bot bot bot] across the conversion, and read the recorded [HeadRed]
   and the three component conversions off the resulting [EqValTyId].
   =========================================================== *)

(* The trivial identity code approximates every [tid]: its three components are
   [bot], which approximates everything. *)
Lemma evalRel_Id_trivial {n} (A a b : Tm n) (ρ : Env n) :
  EvalRel (Core.tid A a b) ρ (tid bot bot bot).
Proof.
  cbn. split; [ done | ].
  split; [ apply EvalRel_bot | ].
  split; [ apply EvalRel_bot | apply EvalRel_bot ].
Qed.

Lemma idConv {n} (Γ : Ctx n) (T : Tm n) (A1 a1 b1 : Tm n) :
  conv Γ T (Core.tid A1 a1 b1) Core.tuniv ->
  exists A0 a0 b0,
    HeadRed T (Core.tid A0 a0 b0)
    /\ conv Γ A0 A1 Core.tuniv
    /\ conv Γ a0 a1 A0
    /\ conv Γ b0 b1 A0.
Proof.
  move=> d.
  have cΓ : ctx Γ by eapply conv_ctx; exact d.
  have WT : wt (tid bot bot bot) tuniv.
  { apply: wt_tid.
    - apply wt_bot. apply wt_tuniv.
    - apply wt_bot. apply wt_bot. apply wt_tuniv.
    - apply wt_bot. apply wt_bot. apply wt_tuniv. }
  have evId : EvalRel (Core.tid A1 a1 b1) bot_env (tid bot bot bot)
    by apply evalRel_Id_trivial.
  have IC : InvConv Γ T (Core.tid A1 a1 b1) Core.tuniv bot_env.
  { eapply conv_EvalRel. exact d. exact (@fits_bot_env n Γ cΓ). }
  move: IC => [_ [_ [_ bwd]]].
  have evT : EvalRel T bot_env (tid bot bot bot) by apply bwd; exact evId.
  have evU : EvalRel Core.tuniv (@bot_env n) tuniv by [].
  have SCA : semantic_conv2 Γ T (Core.tid A1 a1 b1) Core.tuniv
    by (apply adequacyEqSub; exact d).
  (* fuel 2: above [rk (tid bot bot bot) = 1] and [rk tuniv = 1] *)
  have EVfun : EqVal 2 Γ T[var] (Core.tid A1 a1 b1)[var] Core.tuniv[var] WT.
  { eapply SCA.
    - apply typing_subst_id. exact cΓ.
    - apply fits_bot_env. exact cΓ.
    - apply ValSub_id.
    - exact cΓ.
    - exact evT.
    - exact evU.
    - cbn; lia. }
  have EV1 := EVfun.
  unfold subst1, Subst_Tm in EV1.
  rewrite (instId'_Tm T) (instId'_Tm (Core.tid A1 a1 b1)) (instId'_Tm Core.tuniv) in EV1.
  have EVT := EqVal_EqValTy EV1.
  clear EV1 EVfun.
  dependent destruction WT; try prop_only.
  cbn [Rec.EqValTy] in EVT.
  move: EVT => [_ [_ [A0 [a0 [b0 [HRT [A' [a' [b' [HRId [cA [ca [cb _]]]]]]]]]]]]].
  have [E1 [E2 E3]] := HeadRed_tid_eq HRId. subst A' a' b'.
  exists A0. exists a0. exists b0.
  split; [ exact HRT | ].
  split; [ exact cA | split; [ exact ca | exact cb ] ].
Qed.

Lemma idInjectivity {n} (Γ : Ctx n) (A0 a0 b0 A1 a1 b1 : Tm n) :
  conv Γ (Core.tid A0 a0 b0) (Core.tid A1 a1 b1) Core.tuniv ->
  conv Γ A0 A1 Core.tuniv /\ conv Γ a0 a1 A0 /\ conv Γ b0 b1 A0.
Proof.
  move=> H.
  destruct (idConv H) as [A0' [a0' [b0' [HR [cA [ca cb]]]]]].
  (* [tid] is head-normal, so determinacy identifies the recorded normal form *)
  have [E1 [E2 E3]] : A0' = A0 /\ a0' = a0 /\ b0' = b0
    by (eapply HeadRed_tid_det; [ exact HR | apply ms_refl ]).
  subst A0' a0' b0'.
  split; [ exact cA | split; [ exact ca | exact cb ] ].
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

Lemma HeadRed1_jcase_inv {n} (C d p : Tm n) (N' : Tm n) :
  HeadRed1 (Core.jcase C d p) N' ->
  (exists a, p = Core.rfl a /\ N' = Core.app d a)
  \/ (exists p', HeadRed1 p p' /\ N' = Core.jcase C d p').
Proof.
  move=> h. inversion h; subst.
  - left. eexists. split; reflexivity.
  - right. eexists. split; [ eassumption | reflexivity ].
Qed.

(** The J-beta step, as a conversion at the *derivation's* type.

    [c_jcase_beta] states the contraction at the redex's own type
    [app (app (app C a0) a0) (rfl a0)], while the derivation types
    [jcase C d (rfl a0)] at [app (app (app C a) b) (rfl a0)].  Matching the two
    means inverting [typing Γ (rfl a0) (tid A a b)] to get [conv Γ a0 a A] and
    [conv Γ a0 b A] -- which is exactly what [idInjectivity] delivers -- and
    then transporting along [motive_app_conv_args].  This is the [tid] analogue
    of the [piInjectivity] appeal in the beta case of [red1_conv] below.

    (Note this is *not* in tension with Agda's observation that the
    [conv-J-beta] *rule* needs no Id-injectivity: that is about the rule's two
    sides having equal types, which they do.) *)
(* [tuniv] is head-normal and is not an [tid], so it is never convertible to
   one.  This rules out the second alternative that the Prop-to-U subtyping
   rule [t_prop_u] adds to the [typing_*_inv] family (see the comment on
   [typing_app_inv] in [syntax/typing.v]). *)
Lemma tuniv_not_tid {n} (Γ : Ctx n) (A a b : Tm n) :
  conv Γ Core.tuniv (Core.tid A a b) Core.tuniv -> False.
Proof.
  move=> cc.
  destruct (idConv cc) as [Ac [ac [bc [HR _]]]].
  inversion HR; subst; try discriminate.
  match goal with [ S : HeadRed1 Core.tuniv _ |- _ ] => inversion S end.
Qed.

Lemma jcase_beta_conv {n} (Γ : Ctx n) (A a b C d a0 : Tm n) :
  typing Γ A Core.tuniv -> typing Γ a A -> typing Γ b A ->
  typing Γ C (motive_ty A) -> typing Γ d (base_ty A C) ->
  typing Γ (Core.rfl a0) (Core.tid A a b) ->
  conv Γ (Core.jcase C d (Core.rfl a0)) (Core.app d a0)
         (Core.app (Core.app (Core.app C a) b) (Core.rfl a0)).
Proof.
  move=> TA Ta Tb TC Td TR.
  move: (typing_rfl_inv TR) => [A' [Ta0' cc0]].
  have cc : conv Γ (Core.tid A' a0 a0) (Core.tid A a b) Core.tuniv
    by (case: cc0 => cc0; [ exact cc0 | exfalso; exact (tuniv_not_tid cc0) ]).
  have [cAA' [ca0a ca0b]] := idInjectivity cc.
  have Ta0 : typing Γ a0 A by (eapply t_conv; [ exact Ta0' | exact cAA' ]).
  have ca0aA : conv Γ a0 a A by (eapply c_conv; [ exact ca0a | exact cAA' ]).
  have ca0bA : conv Γ a0 b A by (eapply c_conv; [ exact ca0b | exact cAA' ]).
  have TRA : typing Γ (Core.rfl a0) (Core.tid A a0 a0)
    by (eapply t_rfl; [ exact TA | exact Ta0 ]).
  eapply c_conv;
    [ eapply c_jcase_beta; [ exact TA | exact Ta0 | exact TC | exact Td ] | ].
  eapply motive_app_conv_args;
    [ exact TA | exact Ta0 | exact Ta | exact Ta0 | exact Tb | exact TC
    | exact TRA | exact ca0aA | exact ca0bA ].
Qed.

(** Head reduction is contained in conversion, for well-typed terms.  Each
    contraction is exactly one of the computation rules ([c_beta],
    [c_ncase_Z], [c_ncase_S]) and each congruence step is [c_app1]/[c_ncase].
    The β-case needs the abstraction's own domain, so it goes through
    [typing_abs_inv] + [piInjectivity] — which is why this lemma has to come
    *after* adequacy rather than in the syntactic layer. *)
(* Inversion of a head reduction whose redex is a projection. *)
Lemma HeadRed1_pfst_inv {n} (P N' : Tm n) :
  HeadRed1 (Core.pfst P) N' ->
  (exists M1 M2, P = Core.mkpair M1 M2 /\ N' = M1) \/
  (exists P2, HeadRed1 P P2 /\ N' = Core.pfst P2).
Proof.
  move=> h. inversion h; subst.
  - left. do 2 eexists. split; reflexivity.
  - right. eexists. split; [ eassumption | reflexivity ].
Qed.

Lemma HeadRed1_psnd_inv {n} (P N' : Tm n) :
  HeadRed1 (Core.psnd P) N' ->
  (exists M1 M2, P = Core.mkpair M1 M2 /\ N' = M2) \/
  (exists P2, HeadRed1 P P2 /\ N' = Core.psnd P2).
Proof.
  move=> h. inversion h; subst.
  - left. do 2 eexists. split; reflexivity.
  - right. eexists. split; [ eassumption | reflexivity ].
Qed.

(* [typing_abs_inv]'s Sigma twin: a pair's derivation factors through its own
   Sigma type, related to the ascribed one by a conversion. *)
Lemma typing_mkpair_inv {n} (Γ : Ctx n) (M N T : Tm n) :
  typing Γ (Core.mkpair M N) T ->
  exists A0 B0, typing Γ A0 Core.tuniv /\ typing (Γ ++ A0) B0 Core.tuniv
             /\ typing Γ M A0 /\ typing Γ N B0[M..]
             /\ (conv Γ (Core.tsig A0 B0) T Core.tuniv
                 \/ conv Γ Core.tuniv T Core.tuniv).
Proof.
  move=> h. dependent induction h.
  - specialize (IHh M N ltac:(eauto)).
    destruct IHh as [A0 [B0 [tA0 [tB0 [tM [tN CC]]]]]].
    exists A0, B0. repeat split; auto.
    destruct CC as [CC|CC]; [ left | right ]; (eapply c_trans; [ exact CC | eassumption ]).
  - exists A, B. repeat split; auto.
    left. apply c_refl. eapply t_tsig; eauto.
  - (* t_prop_u: the given type is literally [tuniv] *)
    specialize (IHh M N ltac:(eauto)).
    destruct IHh as [A0 [B0 [tA0 [tB0 [tM [tN _]]]]]].
    exists A0, B0. repeat split; auto.
    right. apply c_refl. apply t_univ. eapply typing_ctx; eassumption.
Qed.

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
    | n Γ Ay gy tAy IHAy tgy IHgy
    | n Γ Ai ai bi tAi IHAi tai IHai tbi IHbi
    | n Γ Ar ar tAr IHAr tar IHar
    | n Γ Aj aj bj Cj dj pj tAj IHAj taj IHaj tbj IHbj
        tCj IHCj tdj IHdj tpj IHpj
    | n Γ A B tA IHA tB IHB
    | n Γ cΓ
    | n Γ Asg Bsg tAsg IHAsg tBsg IHBsg
    | n Γ Amp Bmp Mmp Nmp tAmp IHAmp tBmp IHBmp tMmp IHMmp tNmp IHNmp
    | n Γ Af Bf Mf tAf IHAf tBf IHBf tMf IHMf
    | n Γ As Bs Ms tAs IHAs tBs IHBs tMs IHMs
    | n Γ cΓ
    | n Γ Apu tApu IHApu
    | n Γ Apr Bpr tApr IHApr tBpr IHBpr ]; intros N' hr.
  all: try solve [ inversion hr ].
  - (* t_conv: peel the conversion, recurse, re-wrap. *)
    eapply c_conv; [ eapply IHM; exact hr | exact cAB ].
  - (* t_app on [app F a] : B[a..] *)
    apply HeadRed1_app_inv in hr.
    destruct hr as [ [A0 [M' [-> ->]]] | [F2 [hrF ->]] ].
    + (* β: the redex is [app (abs A0 M') a].  [c_beta] wants everything at the
         abstraction's *own* domain [A0], so move [a] and [B] across [cA]. *)
      destruct (typing_abs_inv _ _ _ _ _ tF) as [B2 [tM' cPi0]].
      have cPi : conv Γ (Core.tpi A0 B2) (Core.tpi A B) Core.tuniv
        by (case: cPi0 => cPi0;
              [ exact cPi0 | exfalso; exact (tuniv_not_tpi cPi0) ]).
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
        [ exact tT | exact tMc1 | eapply IHMc; exact hrM
        | apply c_refl; exact tMc0 | apply c_refl; exact tMc1 ].
  - (* t_fix: the only redex is the Y-unfolding *)
    inversion hr; subst.
    eapply c_fix; [ exact tAy | exact tgy ].
  - (* t_jcase: either the J-beta contraction on a literal [rfl], or the proof
       reduces.  The beta case has to match the redex's own type
       [tid Aj a0 a0] against the derivation's [tid Aj aj bj] -- exactly as the
       [app (abs ..)] case above matches through [piInjectivity] -- which is
       what [id_endpoint_inv] provides. *)
    apply HeadRed1_jcase_inv in hr.
    destruct hr as [ [a0 [-> ->]] | [pj' [hrP ->]] ].
    + eapply jcase_beta_conv;
        [ exact tAj | exact taj | exact tbj | exact tCj | exact tdj | exact tpj ].
    + eapply (@c_jcase _ Γ Aj aj bj Cj Cj dj dj pj pj');
        [ exact tAj | exact taj | exact tbj | exact tCj | exact tdj | exact tpj
        | apply c_refl; exact tCj | apply c_refl; exact tdj
        | eapply IHpj; exact hrP ].
  - (* t_pfst: either the first-projection beta on a literal pair, or the
       scrutinee reduces.  The beta case matches the redex's own Sigma against
       the derivation's, through [sigmaInjectivity]. *)
    apply HeadRed1_pfst_inv in hr.
    destruct hr as [ [M1 [M2 [-> ->]]] | [P2 [hrP ->]] ].
    + destruct (typing_mkpair_inv tMf) as [A0 [B0 [tA0 [tB0 [tM1 [tM2 cSig0]]]]]].
      have cSig : conv Γ (Core.tsig A0 B0) (Core.tsig Af Bf) Core.tuniv
        by (case: cSig0 => cSig0;
              [ exact cSig0 | exfalso; exact (tuniv_not_tsig cSig0) ]).
      destruct (sigmaInjectivity cSig) as [cA cB].
      eapply c_conv;
        [ eapply c_beta_fst; [ exact tA0 | exact tB0 | exact tM1 | exact tM2 ]
        | exact cA ].
    + eapply c_pfst; [ exact tAf | exact tBf | eapply IHMf; exact hrP ].
  - (* t_psnd: as above, plus the codomain has to be moved from the redex's own
       [B0[M1..]] to the derivation's [Bs[(pfst (mkpair M1 M2))..]] -- one
       [conv_subst1] along the codomain conversion and one [conv_subst_arg]
       along the first-projection beta. *)
    apply HeadRed1_psnd_inv in hr.
    destruct hr as [ [M1 [M2 [-> ->]]] | [P2 [hrP ->]] ].
    + destruct (typing_mkpair_inv tMs) as [A0 [B0 [tA0 [tB0 [tM1 [tM2 cSig0]]]]]].
      have cSig : conv Γ (Core.tsig A0 B0) (Core.tsig As Bs) Core.tuniv
        by (case: cSig0 => cSig0;
              [ exact cSig0 | exfalso; exact (tuniv_not_tsig cSig0) ]).
      destruct (sigmaInjectivity cSig) as [cA cB].
      have cB0 : conv Γ (Core.psnd (Core.mkpair M1 M2)) M2 B0[M1..]
        by (eapply c_beta_snd; [ exact tA0 | exact tB0 | exact tM1 | exact tM2 ]).
      have cBs1 : conv Γ B0[M1..] Bs[M1..] Core.tuniv := conv_subst1 cB tM1.
      have tM1s : typing Γ M1 As by (eapply t_conv; [ exact tM1 | exact cA ]).
      have tFst : typing Γ (Core.pfst (Core.mkpair M1 M2)) As
        by (eapply t_pfst; [ exact tAs | exact tBs | exact tMs ]).
      have cFst : conv Γ M1 (Core.pfst (Core.mkpair M1 M2)) As.
      { apply c_sym. eapply c_conv;
          [ eapply c_beta_fst; [ exact tA0 | exact tB0 | exact tM1 | exact tM2 ]
          | exact cA ]. }
      have cBs2 : conv Γ Bs[M1..] Bs[(Core.pfst (Core.mkpair M1 M2))..] Core.tuniv
        := conv_subst_arg Γ As Bs M1 (Core.pfst (Core.mkpair M1 M2))
             tAs tBs tM1s tFst cFst.
      eapply c_conv; [ eapply c_conv; [ exact cB0 | exact cBs1 ] | exact cBs2 ].
    + eapply c_psnd; [ exact tAs | exact tBs | eapply IHMs; exact hrP ].
  - (* t_prop_u: [tprop] and [tpi] are head-normal, so only the subject of the
       subtyping rule can reduce; its conversion lifts by [c_prop_u]. *)
    eapply c_prop_u. eapply IHApu; exact hr.
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
    | n Γ Ay gy tAy IHAy tgy IHgy
    | n Γ Ai ai bi tAi IHAi tai IHai tbi IHbi
    | n Γ Ar ar tAr IHAr tar IHar
    | n Γ Aj aj bj Cj dj pj tAj IHAj taj IHaj tbj IHbj
        tCj IHCj tdj IHdj tpj IHpj
    | n Γ A B tA IHA tB IHB
    | n Γ cΓ
    | n Γ Asg Bsg tAsg IHAsg tBsg IHBsg
    | n Γ Amp Bmp Mmp Nmp tAmp IHAmp tBmp IHBmp tMmp IHMmp tNmp IHNmp
    | n Γ Af Bf Mf tAf IHAf tBf IHBf tMf IHMf
    | n Γ As Bs Ms tAs IHAs tBs IHBs tMs IHMs
    | n Γ cΓ
    | n Γ Apu tApu IHApu
    | n Γ Apr Bpr tApr IHApr tBpr IHBpr ]; intros N' hr.
  all: try solve [ inversion hr ].
  - (* t_conv: peel the conversion, recurse, re-wrap. *)
    eapply t_conv; [ eapply IHM; exact hr | exact cAB ].
  - (* t_app on [app F a] : B[a..] *)
    apply HeadRed1_app_inv in hr.
    destruct hr as [ [A0 [M' [-> ->]]] | [F2 [hrF ->]] ].
    + (* β: F = abs A0 M'.  Invert the Lam typing, align via Π-injectivity. *)
      destruct (typing_abs_inv _ _ _ _ _ tF) as [B2 [tM' cPi0]].
      have cPi : conv Γ (Core.tpi A0 B2) (Core.tpi A B) Core.tuniv
        by (case: cPi0 => cPi0;
              [ exact cPi0 | exfalso; exact (tuniv_not_tpi cPi0) ]).
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
  - (* t_fix: [fix g] unfolds to [app g (fix g)], typed at [Ay] because
       [Ay⟨↑⟩[(fix_ g)..] = Ay] *)
    inversion hr; subst.
    have TY : typing Γ (Core.fix_ gy) Ay
      by (eapply t_fix; [ exact tAy | exact tgy ]).
    eapply t_app' with (A := Ay) (B := Ay⟨↑⟩);
      [ exact tAy
      | apply typing_weaken_shift; [ exact tAy | exact tAy ]
      | exact tgy
      | exact TY
      | apply subst1_shift ].
  - (* t_jcase: use [red1_conv] and read the second side off [conv_typing];
       the J-beta case's type matching is packaged in [jcase_beta_conv]. *)
    have TJ : typing Γ (Core.jcase Cj dj pj)
                (Core.app (Core.app (Core.app Cj aj) bj) pj)
      by (eapply t_jcase;
            [ exact tAj | exact taj | exact tbj | exact tCj | exact tdj | exact tpj ]).
    exact (proj2 (conv_typing (red1_conv TJ hr))).
  - (* t_pfst / t_psnd: same trick -- [red1_conv] already did the type
       matching, so read the right-hand side's typing off [conv_typing] *)
    have TP : typing Γ (Core.pfst Mf) Af
      by (eapply t_pfst; [ exact tAf | exact tBf | exact tMf ]).
    exact (proj2 (conv_typing (red1_conv TP hr))).
  - have TP : typing Γ (Core.psnd Ms) Bs[(Core.pfst Ms)..]
      by (eapply t_psnd; [ exact tAs | exact tBs | exact tMs ]).
    exact (proj2 (conv_typing (red1_conv TP hr))).
  - (* t_prop_u: the reduct stays a Prop, then lifts again *)
    eapply t_prop_u. eapply IHApu; exact hr.
Qed.

(* Subject reduction for multi-step head reduction. *)
Lemma subject_red {n} (Γ : Ctx n) (M N A : Tm n) :
  typing Γ M A -> HeadRed M N -> typing Γ N A.
Proof.
  move=> H hr. move: A H. induction hr as [ e | e1 e2 e3 s _ IH ]; intros A H.
  - exact H.
  - apply IH. eapply subject_red1; eassumption.
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

(* Likewise [tid] and [tnat]: at the bottom environment [tid A a b] evaluates
   to the code [tid bot bot bot], which is not below [tnat]. *)
Lemma tid_not_tnat {n} (Γ : Ctx n) (A a b : Tm n) :
  ~ conv Γ (Core.tid A a b) Core.tnat Core.tuniv.
Proof.
  move=> d.
  have cΓ : ctx Γ by eapply conv_ctx; exact d.
  have IC : InvConv Γ (Core.tid A a b) Core.tnat Core.tuniv bot_env
    by (eapply conv_EvalRel; [ exact d | exact (@fits_bot_env n Γ cΓ) ]).
  move: IC => [_ [_ [fwd _]]].
  have evI : EvalRel (Core.tid A a b) (@bot_env n) (tid bot bot bot).
  { cbn. split; [ done | ].
    split; [ apply EvalRel_bot | ].
    split; [ apply EvalRel_bot | apply EvalRel_bot ]. }
  have evN : EvalRel Core.tnat (@bot_env n) (tid bot bot bot) := fwd _ evI.
  cbn in evN. done.
Qed.

(* Sigma non-confusion.  [sigmaConv] turns a conversion into a [HeadRed] onto a
   [tsig], which every other head-normal former refutes by inversion; the two
   reversed forms go through [piConv]/[idConv] the same way. *)
Lemma tnat_not_tsig {n} (Γ : Ctx n) (A : Tm n) (B : Tm (S n)) :
  ~ conv Γ Core.tnat (Core.tsig A B) Core.tuniv.
Proof.
  move=> H. destruct (sigmaConv H) as [B0 [F0 [HR _]]].
  inversion HR; subst; try discriminate.
  match goal with [ S : HeadRed1 Core.tnat _ |- _ ] => inversion S end.
Qed.

Lemma tpi_not_tsig {n} (Γ : Ctx n) (A' : Tm n) (B' : Tm (S n))
  (A : Tm n) (B : Tm (S n)) :
  ~ conv Γ (Core.tpi A' B') (Core.tsig A B) Core.tuniv.
Proof.
  move=> H. destruct (sigmaConv H) as [B0 [F0 [HR _]]].
  inversion HR; subst; try discriminate.
  match goal with [ S : HeadRed1 (Core.tpi _ _) _ |- _ ] => inversion S end.
Qed.

Lemma tid_not_tsig {n} (Γ : Ctx n) (A0 a0 b0 : Tm n)
  (A : Tm n) (B : Tm (S n)) :
  ~ conv Γ (Core.tid A0 a0 b0) (Core.tsig A B) Core.tuniv.
Proof.
  move=> H. destruct (sigmaConv H) as [B0 [F0 [HR _]]].
  inversion HR; subst; try discriminate.
  match goal with [ S : HeadRed1 (Core.tid _ _ _) _ |- _ ] => inversion S end.
Qed.

Lemma tsig_not_tnat {n} (Γ : Ctx n) (A : Tm n) (B : Tm (S n)) :
  ~ conv Γ (Core.tsig A B) Core.tnat Core.tuniv.
Proof.
  move=> H. apply tnat_not_tsig with (Γ := Γ) (A := A) (B := B).
  apply c_sym. exact H.
Qed.

Lemma tsig_not_tpi {n} (Γ : Ctx n) (A : Tm n) (B : Tm (S n))
  (A' : Tm n) (B' : Tm (S n)) :
  ~ conv Γ (Core.tsig A B) (Core.tpi A' B') Core.tuniv.
Proof.
  move=> H. destruct (piConv H) as [B0 [F0 [HR _]]].
  inversion HR; subst; try discriminate.
  match goal with [ S : HeadRed1 (Core.tsig _ _) _ |- _ ] => inversion S end.
Qed.

Lemma tsig_not_tid {n} (Γ : Ctx n) (A : Tm n) (B : Tm (S n))
  (A0 a0 b0 : Tm n) :
  ~ conv Γ (Core.tsig A B) (Core.tid A0 a0 b0) Core.tuniv.
Proof.
  move=> H. destruct (idConv H) as [Ac [ac [bc [HR _]]]].
  inversion HR; subst; try discriminate.
  match goal with [ S : HeadRed1 (Core.tsig _ _) _ |- _ ] => inversion S end.
Qed.

(** * Progress for closed terms

    A closed, well-typed term is either a value (weak-head-normal form) or it
    takes a head-reduction step.  The content is in the application case: a
    closed value of Π type must be a λ (canonical forms), proved from the
    per-former type inversions ([typing_univ_inv], [typing_nat_inv],
    [typing_tpi_inv], [typing_zero_inv], [typing_succ_inv], at the end of
    [syntax/typing.v]) together with the [tnat]/[tuniv] vs Π non-confusion
    facts. *)

(* ------------------------------------------------------------------
   Non-confusion for the second sort, and the alternative-killing tactic.

   [tprop] is a head-normal former distinct from every other one, so the same
   three [*Conv] head-reduction lemmas refute it; [tprop] vs [tnat] goes the
   semantic route ([tuniv_not_tnat]'s script).
   ------------------------------------------------------------------ *)
Lemma tprop_not_tpi {n} (Γ : Ctx n) (A : Tm n) (B : Tm (S n)) :
  ~ conv Γ Core.tprop (Core.tpi A B) Core.tuniv.
Proof.
  move=> H. destruct (piConv H) as [B0 [F0 [HR _]]].
  inversion HR; subst; try discriminate.
  match goal with [ S : HeadRed1 Core.tprop _ |- _ ] => inversion S end.
Qed.

Lemma tprop_not_tsig {n} (Γ : Ctx n) (A : Tm n) (B : Tm (S n)) :
  ~ conv Γ Core.tprop (Core.tsig A B) Core.tuniv.
Proof.
  move=> H. destruct (sigmaConv H) as [B0 [F0 [HR _]]].
  inversion HR; subst; try discriminate.
  match goal with [ S : HeadRed1 Core.tprop _ |- _ ] => inversion S end.
Qed.

Lemma tprop_not_tid {n} (Γ : Ctx n) (A a b : Tm n) :
  ~ conv Γ Core.tprop (Core.tid A a b) Core.tuniv.
Proof.
  move=> H. destruct (idConv H) as [Ac [ac [bc [HR _]]]].
  inversion HR; subst; try discriminate.
  match goal with [ S : HeadRed1 Core.tprop _ |- _ ] => inversion S end.
Qed.

Lemma tprop_not_tnat {n} (Γ : Ctx n) :
  ~ conv Γ Core.tprop Core.tnat Core.tuniv.
Proof.
  move=> d.
  have cΓ : ctx Γ by eapply conv_ctx; exact d.
  have IC : InvConv Γ Core.tprop Core.tnat Core.tuniv bot_env
    by (eapply conv_EvalRel; [ exact d | exact (@fits_bot_env n Γ cΓ) ]).
  move: IC => [_ [_ [fwd _]]].
  have evP : EvalRel Core.tprop (@bot_env n) tprop by [].
  have evN : EvalRel Core.tnat (@bot_env n) tprop := fwd _ evP.
  cbn in evN. done.
Qed.

(* Every [typing_*_inv] lemma now offers a second alternative -- the [tuniv]
   that the Prop-to-U subtyping rule [t_prop_u] introduces, or, for [tpi],
   the second sort [tprop] itself ([t_tpi_prop]).  At a head-normal type
   former both alternatives are refuted by non-confusion, which is what this
   tactic does: it leaves the primary conversion in [H]. *)
Ltac inv_alt H :=
  case: H => H;
    [ idtac
    | exfalso;
      solve [ exact (tuniv_not_tpi H) | exact (tuniv_not_tnat H)
            | exact (tuniv_not_tsig H) | exact (tuniv_not_tid H)
            | exact (tprop_not_tpi H)  | exact (tprop_not_tnat H)
            | exact (tprop_not_tsig H) | exact (tprop_not_tid H)
            | exact (tuniv_not_tpi (c_sym _ _ _ _ _ H)) ] ].

(* Values (weak-head-normal forms) and neutral (variable-headed) terms. *)
Inductive value {n} : Tm n -> Prop :=
| v_univ : value Core.tuniv
| v_nat  : value Core.tnat
| v_tpi  : forall A B, value (Core.tpi A B)
| v_zero : value Core.zero
| v_succ : forall M, value (Core.succ M)
| v_abs  : forall A M, value (Core.abs A M)
| v_tid  : forall A a b, value (Core.tid A a b)
| v_rfl  : forall a, value (Core.rfl a)
| v_tsig : forall A B, value (Core.tsig A B)
| v_mkpair : forall M N, value (Core.mkpair M N)
(* the second sort is a value, like [tuniv] *)
| v_prop : value Core.tprop.

Inductive neutral {n} : Tm n -> Prop :=
| ne_var : forall x, neutral (Core.var x)
| ne_app : forall M N, neutral M -> neutral (Core.app M N)
| ne_ncase : forall M M0 M1, neutral M -> neutral (Core.ncase M M0 M1)
| ne_jcase : forall C d p, neutral p -> neutral (Core.jcase C d p)
| ne_pfst : forall M, neutral M -> neutral (Core.pfst M)
| ne_psnd : forall M, neutral M -> neutral (Core.psnd M).

(* Canonical forms at Π type (any context): a value of Π type is a λ. *)
Lemma canonical_pi {n} (Γ : Ctx n) (M : Tm n) (A : Tm n) (B : Tm (S n)) :
  value M -> typing Γ M (Core.tpi A B) -> exists A' N, M = Core.abs A' N.
Proof.
  move=> v; destruct v; move=> HT.
  - exfalso; exact (tuniv_not_tpi (typing_univ_inv HT)).
  - exfalso; exact (tuniv_not_tpi (typing_nat_inv HT)).
  - exfalso. move: (typing_tpi_inv HT) => cc. inv_alt cc. exact (tuniv_not_tpi cc).
  - exfalso. move: (typing_zero_inv HT) => cc. inv_alt cc. exact (tnat_not_tpi cc).
  - exfalso. move: (typing_succ_inv HT) => cc. inv_alt cc. exact (tnat_not_tpi cc).
  - eexists; eexists; reflexivity.
  - (* v_tid: an [tid] is a type code, so its type is [tuniv] *)
    exfalso; exact (tuniv_not_tpi (typing_tid_inv HT)).
  - (* v_rfl: a proof's type is an [tid], which is head-normal *)
    exfalso.
    move: (typing_rfl_inv HT) => [A0 [_ cc]]. inv_alt cc.
    destruct (piConv cc) as [B0 [F0 [HR _]]].
    inversion HR; subst; try discriminate.
    match goal with [ S : HeadRed1 (Core.tid _ _ _) _ |- _ ] => inversion S end.
  - (* v_tsig: a [tsig] is a type code, so its type is [tuniv] *)
    exfalso; exact (tuniv_not_tpi (typing_tsig_inv HT)).
  - (* v_mkpair: a pair's type is a [tsig], which is head-normal *)
    exfalso.
    move: (typing_mkpair_inv HT) => [A0 [B0 [_ [_ [_ [_ cc]]]]]]. inv_alt cc.
    exact (tsig_not_tpi cc).
  - (* v_prop: the second sort's own type is [tuniv] *)
    exfalso. move: (typing_prop_inv HT) => cc. exact (tuniv_not_tpi cc).
Qed.

(* Canonical forms at [tnat]: a value of type [tnat] is [zero] or a successor. *)
Lemma canonical_nat {n} (Γ : Ctx n) (M : Tm n) :
  value M -> typing Γ M Core.tnat -> M = Core.zero \/ exists N, M = Core.succ N.
Proof.
  move=> v; destruct v; move=> HT.
  - exfalso; exact (tuniv_not_tnat (typing_univ_inv HT)).
  - exfalso; exact (tuniv_not_tnat (typing_nat_inv HT)).
  - exfalso. move: (typing_tpi_inv HT) => cc. inv_alt cc. exact (tuniv_not_tnat cc).
  - left; reflexivity.
  - right; eexists; reflexivity.
  - exfalso. destruct (typing_abs_inv _ _ _ _ _ HT) as [B2 [_ cPi]]. inv_alt cPi.
    exact (tpi_not_tnat cPi).
  - (* v_tid *) exfalso; exact (tuniv_not_tnat (typing_tid_inv HT)).
  - (* v_rfl: [tid] is head-normal and distinct from [tnat] *)
    exfalso.
    move: (typing_rfl_inv HT) => [A0 [_ cc]]. inv_alt cc.
    (* [cc : conv Γ (tid A0 a a) tnat tuniv]; both are head-normal codes *)
    exact (tid_not_tnat cc).
  - (* v_tsig *) exfalso; exact (tuniv_not_tnat (typing_tsig_inv HT)).
  - (* v_mkpair *) exfalso.
    move: (typing_mkpair_inv HT) => [A0 [B0 [_ [_ [_ [_ cc]]]]]]. inv_alt cc.
    exact (tsig_not_tnat cc).
  - (* v_prop *)
    exfalso. move: (typing_prop_inv HT) => cc. exact (tuniv_not_tnat cc).
Qed.

(* Progress, general form: every well-typed term is a value, a neutral
   (variable-headed) term, or head-reduces. *)
(** Canonical forms at an [tid] type: a value of identity type is a [rfl].
    The [tid] analogue of [canonical_pi]; each non-[rfl] value is ruled out by
    inverting its typing and observing, via [idConv], that its own head-normal
    former would have to head-reduce to an [tid]. *)
Lemma canonical_id {n} (Γ : Ctx n) (M : Tm n) (A a b : Tm n) :
  value M -> typing Γ M (Core.tid A a b) -> exists a0, M = Core.rfl a0.
Proof.
  move=> v; destruct v; move=> HT.
  - (* tuniv *) exfalso.
    destruct (idConv (typing_univ_inv HT)) as [Ac [ac [bc [HR _]]]].
    inversion HR; subst; try discriminate.
    match goal with [ S : HeadRed1 Core.tuniv _ |- _ ] => inversion S end.
  - (* tnat *) exfalso.
    destruct (idConv (typing_nat_inv HT)) as [Ac [ac [bc [HR _]]]].
    inversion HR; subst; try discriminate.
    match goal with [ S : HeadRed1 Core.tuniv _ |- _ ] => inversion S end.
  - (* tpi (as a type code, so its type is [tuniv] or [tprop]) *) exfalso.
    move: (typing_tpi_inv HT) => cc. inv_alt cc.
    destruct (idConv cc) as [Ac [ac [bc [HR _]]]].
    inversion HR; subst; try discriminate.
    match goal with [ S : HeadRed1 Core.tuniv _ |- _ ] => inversion S end.
  - (* zero *) exfalso.
    move: (typing_zero_inv HT) => cc. inv_alt cc.
    destruct (idConv cc) as [Ac [ac [bc [HR _]]]].
    inversion HR; subst; try discriminate.
    match goal with [ S : HeadRed1 Core.tnat _ |- _ ] => inversion S end.
  - (* succ *) exfalso.
    move: (typing_succ_inv HT) => cc. inv_alt cc.
    destruct (idConv cc) as [Ac [ac [bc [HR _]]]].
    inversion HR; subst; try discriminate.
    match goal with [ S : HeadRed1 Core.tnat _ |- _ ] => inversion S end.
  - (* abs: its type is a [tpi], which is head-normal *) exfalso.
    destruct (typing_abs_inv _ _ _ _ _ HT) as [B2 [_ cPi]]. inv_alt cPi.
    destruct (idConv cPi) as [Ac [ac [bc [HR _]]]].
    inversion HR; subst; try discriminate.
    match goal with [ S : HeadRed1 (Core.tpi _ _) _ |- _ ] => inversion S end.
  - (* tid (a type code) *) exfalso.
    destruct (idConv (typing_tid_inv HT)) as [Ac [ac [bc [HR _]]]].
    inversion HR; subst; try discriminate.
    match goal with [ S : HeadRed1 Core.tuniv _ |- _ ] => inversion S end.
  - (* rfl *) eexists; reflexivity.
  - (* tsig (a type code) *) exfalso.
    destruct (idConv (typing_tsig_inv HT)) as [Ac [ac [bc [HR _]]]].
    inversion HR; subst; try discriminate.
    match goal with [ S : HeadRed1 Core.tuniv _ |- _ ] => inversion S end.
  - (* mkpair: its type is a [tsig], which is head-normal *) exfalso.
    move: (typing_mkpair_inv HT) => [A0 [B0 [_ [_ [_ [_ cc]]]]]]. inv_alt cc.
    exact (tsig_not_tid cc).
  - (* tprop (a type code) *) exfalso.
    destruct (idConv (typing_prop_inv HT)) as [Ac [ac [bc [HR _]]]].
    inversion HR; subst; try discriminate.
    match goal with [ S : HeadRed1 Core.tuniv _ |- _ ] => inversion S end.
Qed.

(** Canonical forms at a Σ type: a value of Σ type is a pair.  The [tsig]
    analogue of [canonical_pi]/[canonical_id]. *)
Lemma canonical_sigma {n} (Γ : Ctx n) (M : Tm n) (A : Tm n) (B : Tm (S n)) :
  value M -> typing Γ M (Core.tsig A B) -> exists M1 M2, M = Core.mkpair M1 M2.
Proof.
  move=> v; destruct v; move=> HT.
  - exfalso; exact (tuniv_not_tsig (typing_univ_inv HT)).
  - exfalso; exact (tuniv_not_tsig (typing_nat_inv HT)).
  - exfalso. move: (typing_tpi_inv HT) => cc. inv_alt cc. exact (tuniv_not_tsig cc).
  - exfalso. move: (typing_zero_inv HT) => cc. inv_alt cc. exact (tnat_not_tsig cc).
  - exfalso. move: (typing_succ_inv HT) => cc. inv_alt cc. exact (tnat_not_tsig cc).
  - exfalso. destruct (typing_abs_inv _ _ _ _ _ HT) as [B2 [_ cPi]]. inv_alt cPi.
    exact (tpi_not_tsig cPi).
  - exfalso; exact (tuniv_not_tsig (typing_tid_inv HT)).
  - exfalso. move: (typing_rfl_inv HT) => [A0 [_ cc]]. inv_alt cc.
    exact (tid_not_tsig cc).
  - exfalso; exact (tuniv_not_tsig (typing_tsig_inv HT)).
  - eexists; eexists; reflexivity.
  - (* v_prop *)
    exfalso. move: (typing_prop_inv HT) => cc. exact (tuniv_not_tsig cc).
Qed.

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
    | n Γ Ay gy tAy IHAy tgy IHgy
    | n Γ Ai ai bi tAi IHAi tai IHai tbi IHbi
    | n Γ Ar ar tAr IHAr tar IHar
    | n Γ Aj aj bj Cj dj pj tAj IHAj taj IHaj tbj IHbj
        tCj IHCj tdj IHdj tpj IHpj
    | n Γ A B tA IHA tB IHB
    | n Γ cΓ
    | n Γ Asg Bsg tAsg IHAsg tBsg IHBsg
    | n Γ Amp Bmp Mmp Nmp tAmp IHAmp tBmp IHBmp tMmp IHMmp tNmp IHNmp
    | n Γ Af Bf Mf tAf IHAf tBf IHBf tMf IHMf
    | n Γ As Bs Ms tAs IHAs tBs IHBs tMs IHMs
    | n Γ cΓ
    | n Γ Apu tApu IHApu
    | n Γ Apr Bpr tApr IHApr tBpr IHBpr ].
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
  - (* t_fix: always unfolds *)
    right; right; eexists; apply hr_fix.
  - (* t_tid: a type code is a value *) left; constructor.
  - (* t_rfl: a proof is a value *) left; constructor.
  - (* t_jcase: a value proof at an [tid] type is a [rfl] and the eliminator
       fires (hr_jcase); a neutral proof makes the eliminator neutral; a
       stepping proof steps by hr_jcase_scrut. *)
    destruct IHpj as [ vp | [ nep | [pj' stp] ] ].
    + destruct (canonical_id vp tpj) as [a0 ->].
      right; right; eexists; apply hr_jcase.
    + right; left; apply ne_jcase; exact nep.
    + right; right; eexists; apply hr_jcase_scrut; exact stp.
  - left; constructor.
  - left; constructor.
  - (* t_tsig: a Σ type code is a value *) left; constructor.
  - (* t_mkpair: a pair is a value *) left; constructor.
  - (* t_pfst: a value scrutinee at a Σ type is a pair and the projection fires
       (hr_pfst); a neutral scrutinee makes it neutral; a stepping scrutinee
       steps by hr_pfst_scrut. *)
    destruct IHMf as [ vM | [ neM | [Mf' stM] ] ].
    + destruct (canonical_sigma vM tMf) as [M1 [M2 ->]].
      right; right; eexists; apply hr_pfst.
    + right; left; apply ne_pfst; exact neM.
    + right; right; eexists; apply hr_pfst_scrut; exact stM.
  - (* t_psnd: as above *)
    destruct IHMs as [ vM | [ neM | [Ms' stM] ] ].
    + destruct (canonical_sigma vM tMs) as [M1 [M2 ->]].
      right; right; eexists; apply hr_psnd.
    + right; left; apply ne_psnd; exact neM.
    + right; right; eexists; apply hr_psnd_scrut; exact stM.
  - (* t_prop: the second sort is a value *) left; constructor.
  - (* t_prop_u: the subject is unchanged *) exact IHApu.
  - (* t_tpi_prop: a Π code is a value, at either sort *) left; constructor.
Qed.

(* A closed term has no neutral (variable-headed) subterm. *)
Lemma neutral_not_closed (M : Tm 0) : neutral M -> False.
Proof. induction 1 as
         [ x | M N ne IH | M M0 M1 ne IH | C d p ne IH | M ne IH | M ne IH ].
       - destruct x. - exact IH. - exact IH. - exact IH. - exact IH. - exact IH. Qed.

(* Progress for closed terms. *)
Lemma progress (M A : Tm 0) :
  typing ctx_empty M A -> value M \/ exists N, HeadRed1 M N.
Proof.
  move=> H. destruct (progress_gen H) as [ v | [ ne | st ] ].
  - left; exact v.
  - exfalso; exact (neutral_not_closed ne).
  - right; exact st.
Qed.
