(* Fundamental theorem of the logical relation
 *)


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

(* ============================================================
   Cross-fuel bridges (from the above-rank fuel-stability lemmas
   [Val_fuel_up]/[Val_fuel_down] in raw_validity.v).  Between any two
   fuels that are BOTH above the ranks of [u] and [a], [Val]/[EqVal] are
   interchangeable.  These let the [forall RB] substitution relations be
   threaded at any above-rank fuel — the Coq counterpart of Agda's
   single canonical stage [Stage (suc (max (RANK u) (RANK a)))].
   ============================================================ *)
Lemma Val_fuel_up_to {n} (Γ : Ctx n) (M T : Tm n) u a (h : wt u a) k k' :
  k <= k' -> rk u < k -> rk a < k -> Val k Γ M T h -> Val k' Γ M T h.
Proof.
  move=> Hle Hu Ha V. induction Hle as [|k' Hle IH]; first exact V.
  apply Val_fuel_up; [ lia | lia | exact IH ].
Qed.

Lemma Val_fuel_down_to {n} (Γ : Ctx n) (M T : Tm n) u a (h : wt u a) k k' :
  k' <= k -> rk u < k' -> rk a < k' -> Val k Γ M T h -> Val k' Γ M T h.
Proof.
  move=> Hle Hu Ha. induction Hle as [|k Hle IH]; first (move=> V; exact V).
  move=> V. apply IH. apply Val_fuel_down; [ lia | lia | exact V ].
Qed.

Lemma Val_fuel_any {n} (Γ : Ctx n) (M T : Tm n) u a (h : wt u a) k k' :
  rk u < k -> rk a < k -> rk u < k' -> rk a < k' -> Val k Γ M T h -> Val k' Γ M T h.
Proof.
  move=> Hu Ha Hu' Ha' V. destruct (Nat.le_ge_cases k k') as [Hle|Hge].
  - exact (Val_fuel_up_to Hle Hu Ha V).
  - exact (Val_fuel_down_to Hge Hu' Ha' V).
Qed.

Lemma EqVal_fuel_up_to {n} (Γ : Ctx n) (M N T : Tm n) u a (h : wt u a) k k' :
  k <= k' -> rk u < k -> rk a < k -> EqVal k Γ M N T h -> EqVal k' Γ M N T h.
Proof.
  move=> Hle Hu Ha V. induction Hle as [|k' Hle IH]; first exact V.
  apply EqVal_fuel_up; [ lia | lia | exact IH ].
Qed.

Lemma EqVal_fuel_down_to {n} (Γ : Ctx n) (M N T : Tm n) u a (h : wt u a) k k' :
  k' <= k -> rk u < k' -> rk a < k' -> EqVal k Γ M N T h -> EqVal k' Γ M N T h.
Proof.
  move=> Hle Hu Ha. induction Hle as [|k Hle IH]; first (move=> V; exact V).
  move=> V. apply IH. apply EqVal_fuel_down; [ lia | lia | exact V ].
Qed.

Lemma EqVal_fuel_any {n} (Γ : Ctx n) (M N T : Tm n) u a (h : wt u a) k k' :
  rk u < k -> rk a < k -> rk u < k' -> rk a < k' -> EqVal k Γ M N T h -> EqVal k' Γ M N T h.
Proof.
  move=> Hu Ha Hu' Ha' V. destruct (Nat.le_ge_cases k k') as [Hle|Hge].
  - exact (EqVal_fuel_up_to Hle Hu Ha V).
  - exact (EqVal_fuel_down_to Hge Hu' Ha' V).
Qed.

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
    cbn. eapply c_abs; [ exact convA | exact convN ].
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
      - cbn. eapply c_sym. eapply c_tpi; [ exact convA | exact convB ]. }
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
    cbn. eapply c_tpi; [ exact convA | exact convB ].
  - (* t_univ *) cbn. eapply c_refl. eapply t_univ. exact CΔ.
Qed.

Lemma ConvSub_sym {h} {g} (Δ : Ctx h) (Γ : Ctx g) (σ1 σ2 : Sub g h) :
  ConvSub Δ Γ σ1 σ2 -> ConvSub Δ Γ σ2 σ1.
Proof.
Admitted.

(* [semantic_typing] bundles the two value-only results of
   [MIN/Adequacy/Value.agda] over a well-typed [M : A]:
     - [adequacySub2]     : [Val]   at [M[σ]]            (one substitution),
     - [adequacyConvSub2] : [EqVal] at [M[σ]] / [M[σ']]  (two substitutions).
   Following Agda, it takes [ValSub σ] ([vs]), [ValSub σ'] ([vs']) and
   [EqValSub σ σ'] ([vcs]) as separate hypotheses. *)
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

(* [semantic_conv2] is [adequacyEqSub2] of [MIN/Adequacy/Value.agda]: from a
   conversion [M ≡ N : A], a *single* substitution [σ] gives
   [EqVal] at [M[σ]] / [N[σ]].  (No second substitution, unlike the old
   two-σ formulation that made [sc_sym]/[sc_trans] unprovable.) *)
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

(* ============================================================
   Bridging lemmas needed by st_app.

   These mirror Adequacy2.agda's helpers:
   - Val_transport ≈ app-transport-Val2  (combines restrictVal + downVal)
   - EvalRel_Pi_app_type ≈ EvalRel-Pi-app-type
   - EvalRel_app_Comp    ≈ EvalRel-Comp
   ============================================================ *)

(* Val_transport: bridge Val along both a u-decrease AND an a-decrease.
   Internally chains:
     - wt_le on h' to get an intermediate witness wt u' a,
     - restrictVal to drop u: from h (wt u a) → intermediate (wt u' a),
     - downVal to drop a: from intermediate (wt u' a) → h' (wt u' a'). *)
Lemma Val_transport {n} (Γ : Ctx n) (M T : Tm n) u u' a a'
  (h : wt u a) (h' : wt u' a')
  (hUa : wt a tuniv) (hUa' : wt a' tuniv) :
  le u' u -> le a' a ->
  forall RB, Val RB Γ M T h -> Val RB Γ M T h'.
Proof.
  move=> LEu LEa RB VH.
  have h'' : wt u' a by eapply wt_le; eauto.
  have VH'' : Val RB Γ M T h'' by eapply (@restrictVal RB _ Γ M T u u' a h'' h); eauto.
  eapply (@downVal RB _ Γ M T u' a' a h' h''); eauto.
Qed.

(* Val_transport_up: bridge Val along a u-decrease AND a TYPE-increase
   ([le a a']).  This is the [App]-codomain transport: the codomain type
   at the selection key [ef_usel = app g u_sel] is *below* the codomain
   type at the actual argument [ac1 = app g v0] (argument monotonicity),
   so the type goes up.  Coq's discrete order lets us replace Agda's
   [Sup]-join transport ([app-transport-Val2]) with [upVal]+[restrictVal]:
     - [wt_le] on [h] gives the intermediate witness [wt u a'],
     - [upVal] raises the type [a -> a'] (needs [ValTy a']),
     - [restrictVal] drops the element [u -> u']. *)
Lemma Val_transport_up {n} (Γ : Ctx n) (M T : Tm n) u u' a a'
  (h : wt u a) (h' : wt u' a')
  (hUa : wt a tuniv) (hUa' : wt a' tuniv) :
  le u' u -> le a a' ->
  forall RB, Val RB Γ T Core.tuniv hUa' -> Val RB Γ M T h -> Val RB Γ M T h'.
Proof.
  move=> LEu LEa RB VT VH.
  have hmid : wt u a' by eapply wt_le; eauto.
  have Vmid : Val RB Γ M T hmid
    by eapply (@upVal RB _ Γ M T u a a' h hmid hUa hUa'); eauto.
  eapply (@restrictVal RB _ Γ M T u u' a' h' hmid); eauto.
Qed.

Lemma EqVal_transport_up {n} (Γ : Ctx n) (M N T : Tm n) u u' a a'
  (h : wt u a) (h' : wt u' a')
  (hUa : wt a tuniv) (hUa' : wt a' tuniv) :
  le u' u -> le a a' ->
  forall RB, Val RB Γ T Core.tuniv hUa' -> EqVal RB Γ M N T h -> EqVal RB Γ M N T h'.
Proof.
  move=> LEu LEa RB VT VH.
  have hmid : wt u a' by eapply wt_le; eauto.
  have Vmid : EqVal RB Γ M N T hmid
    by eapply (@upEqVal RB _ Γ M N T u a a' h hmid hUa hUa'); eauto.
  eapply (@restrictEqVal RB _ Γ M N T u u' a' h' hmid); eauto.
Qed.

(* ------------------------------------------------------------------
   Val_app_transport / EqVal_app_transport: the App-codomain [Sup]-join
   transport — Agda [app-transport-Val2] / [app-transport-EqVal2].

   Moves a [Val]/[EqVal] from the edge's codomain type [af = app f u_sel]
   (at element [v = v_sel]) to the environment-given codomain type [a] (at
   element [u]).  Because [a] and [af] are only *compatible* (both evaluate
   the codomain [B[N..]]) and need not be ordered, this goes through their
   join [lub a af] and relies on the type-validity join [ValTy_Sup] /
   [EqValTy_Sup] (Agda [ValTy2-Sup] / [EqValTy2-Sup]; the corresponding
   [ValTy_Sup] in raw_validity.v is currently Aborted).

   ADMITTED: these isolate exactly that Sup machinery.  Discharging them
   amounts to porting Agda's SupPack (stage induction over the Pi type-code
   join) and threading the codomain [ValTy] at [a] from the codomain IH.
   See [[finelt-adequacy-coq-gotchas]]. *)
(* Discrete-order transport via the join [c = lub a af]: with [ValTy] at [c]
   in hand ([VTc]), [Val] moves [af -> c] ([upVal], the only step needing
   [ValTy]), restricts the element [v -> u] ([restrictVal]), then drops
   [c -> a] ([downVal]).  No [ValTy_Sup] is needed because [ValTy] at the
   join is supplied as a hypothesis (threaded by the caller from the
   function's own [ValTy]).  This is the Coq-discrete replacement for Agda's
   [app-transport-Val2]. *)
Lemma Val_app_transport {n} (Γ : Ctx n) (MN T : Tm n) u v a af
  (h : wt v af) (h' : wt u a) (hUc : wt (lub a af) tuniv) :
  compatible a af -> le u v ->
  forall RB, Val RB Γ T Core.tuniv hUc -> Val RB Γ MN T h -> Val RB Γ MN T h'.
Proof.
  move=> Caf LEuv RB VTc VH.
  have Wa  : wt a  tuniv := wt_ty_tuniv h'.
  have Waf : wt af tuniv := wt_ty_tuniv h.
  have Va  : valid a  := wt_valid_tm Wa.
  have Vaf : valid af := wt_valid_tm Waf.
  have LEac  : le a  (lub a af) := le_lub_left  Caf Va Vaf.
  have LEafc : le af (lub a af) := le_lub_right Caf Va Vaf.
  have hvc : wt v (lub a af) by (eapply wt_le; [ exact h | exact LEafc | exact Waf | exact hUc ]).
  have VHc : Val RB Γ MN T hvc
    by (eapply (@upVal RB _ Γ MN T v af (lub a af) h hvc Waf hUc); [ exact LEafc | exact VH | exact VTc ]).
  have huc : wt u (lub a af) by (eapply wt_le; [ exact h' | exact LEac | exact Wa | exact hUc ]).
  have VHuc : Val RB Γ MN T huc
    by (eapply (@restrictVal RB _ Γ MN T v u (lub a af) huc hvc); [ exact LEuv | exact VHc ]).
  eapply (@downVal RB _ Γ MN T u a (lub a af) h' huc); [ exact LEac | exact VHuc ].
Qed.

Lemma EqVal_app_transport {n} (Γ : Ctx n) (M N T : Tm n) u v a af
  (h : wt v af) (h' : wt u a) (hUc : wt (lub a af) tuniv) :
  compatible a af -> le u v ->
  forall RB, Val RB Γ T Core.tuniv hUc -> EqVal RB Γ M N T h -> EqVal RB Γ M N T h'.
Proof.
  move=> Caf LEuv RB VTc VH.
  have Wa  : wt a  tuniv := wt_ty_tuniv h'.
  have Waf : wt af tuniv := wt_ty_tuniv h.
  have Va  : valid a  := wt_valid_tm Wa.
  have Vaf : valid af := wt_valid_tm Waf.
  have LEac  : le a  (lub a af) := le_lub_left  Caf Va Vaf.
  have LEafc : le af (lub a af) := le_lub_right Caf Va Vaf.
  have hvc : wt v (lub a af) by (eapply wt_le; [ exact h | exact LEafc | exact Waf | exact hUc ]).
  have VHc : EqVal RB Γ M N T hvc
    by (eapply (@upEqVal RB _ Γ M N T v af (lub a af) h hvc Waf hUc); [ exact LEafc | exact VH | exact VTc ]).
  have huc : wt u (lub a af) by (eapply wt_le; [ exact h' | exact LEac | exact Wa | exact hUc ]).
  have VHuc : EqVal RB Γ M N T huc
    by (eapply (@restrictEqVal RB _ Γ M N T v u (lub a af) huc hvc); [ exact LEuv | exact VHc ]).
  eapply (@downEqVal RB _ Γ M N T u a (lub a af) h' huc); [ exact LEac | exact VHuc ].
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


(* (Val_ty_conv removed: transporting [Val] across a *syntactic* type conversion
   has no Agda analog — Agda transports along the *semantic* type-equality
   [EqValTy] (= Coq's [Val_EqVal_fwd]).  Its two former uses now build the
   semantic equality from the domain/Pi IH [STA]/[st_tpi_EqVal_edge] and apply
   [Val_EqVal_fwd] directly.) *)

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

(* EvalRel_app_Comp: two EvalRel results of the same term in the same
   environment are compatible (i.e., their lub exists).

   Mirrors Agda's EvalRel-Comp.  Specialized for applications, but the
   general statement applies to any term. *)
Lemma EvalRel_app_Comp {n} (M : Tm n) (ρ : Env n) (u v : elt) :
  valid_env ρ ->
  EvalRel M ρ u ->
  EvalRel M ρ v ->
  compatible u v.
Proof. intros; eapply EvalRel_compatible; eauto. Qed.


(* ------------------ semantic typing rules ----------- *)

Section SemanticTyping.

Local Notation "Γ ⊨ M ∈ A" := (semantic_typing Γ M A).
Local Notation "Γ ⊨ M ≡ N ∈ A" := (semantic_conv2 Γ M N A).

Variable (n:nat) (Γ : Ctx n).

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
  asimpl. asimpl in valMA. asimpl in eqvalMA. asimpl in eqAB.
  split.
  - move=> RB Hrank. eapply Val_EqVal_fwd;
      [ exact (valMA RB Hrank)
      | eapply EqVal_EqValTy; eapply (eqAB (S RB)); cbn in Hrank |- *; lia ].
  - move=> RB Hrank. eapply EqVal_EqVal_fwd;
      [ exact (eqvalMA RB Hrank)
      | eapply EqVal_EqValTy; eapply (eqAB (S RB)); cbn in Hrank |- *; lia ].
Qed.


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
      move: VPi => [A0 [B0 [HRpi [pav _]]]].
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
        by (eapply EvalRel_app_Comp; [ exact Vρ | exact evBN | exact evB_af ]).
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
      move: EPi => [A0 [B0 [HRpi paev]]].
      move: VPiM' => [A0' [B0' [HRpi' [_ pae']]]].
      asimpl in HRpi. asimpl in HRpi'.
      have [EA0 EB0] := HeadRed_tpi_eq HRpi. subst A0 B0.
      have [EA0' EB0'] := HeadRed_tpi_eq HRpi'. subst A0' B0'.
      (* function variation: [App sf sa] vs [App sf' sa] *)
      have Efun := paev u_sel v_sel Sel WTu_sel N[σ] TNσ (valN RBf HfN).
      (* argument variation: [App sf' sa] vs [App sf' sa'] *)
      have Earg := pae' u_sel v_sel Sel WTu_sel N[σ] N[σ'] convNN' (eqvalN RBf HfN).
      (* combine by transitivity *)
      have Ecomb := EqVal_trans Efun Earg.
      (* the edge codomain [app f u_sel] also evaluates [B[N..]] *)
      have evB_af : EvalRel B[N..] ρ (app f u_sel).
      { destruct (is_bot (app f u_sel)) eqn:Hbaf.
        - have -> : app f u_sel = bot by apply is_bot_eq; rewrite Hbaf. apply EvalRel_bot.
        - have NB : ~ is_bot (app f u_sel) by rewrite Hbaf.
          eapply EvalRel_Pi_app_type;
            [ exact evTpi | exact Vρ | exact Vusel | reflexivity | exact NB | exact evN_usel ]. }
      have Caaf : compatible a (app f u_sel)
        by (eapply EvalRel_app_Comp; [ exact Vρ | exact evBN | exact evB_af ]).
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

(* t_nat: ctx Γ ⟹ tnat : tuniv 0 *)
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

(* t_zero: ctx Γ ⟹ zero : tnat *)
Lemma st_zero :
  ctx Γ ->
(* ------------------------- *)
  semantic_typing Γ Core.zero Core.tnat.
Proof.
  (* TODO: rework for current Rec signatures / WF Val-EqVal. *)
Admitted.

(* t_succ: M : tnat ⟹ succ M : tnat *)
Lemma st_succ M :
  typing Γ M Core.tnat ->
  semantic_typing Γ M Core.tnat ->
(* ------------------------- *)
  semantic_typing Γ (Core.succ M) Core.tnat.
Proof.
  (* TODO: rework for current Rec signatures / WF Val-EqVal. *)
Admitted.

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
Proof. Admitted. *)

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
  { move=> RB0 Hr0. eapply Val_EqVal_fwd; [ exact (VPall RB0 Hr0) | ].
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
Lemma st_abs_Val_edge (A : Tm n) (B M : Tm (S n))
  (TA : typing Γ A Core.tuniv) (TB : typing (Γ ++ A) B Core.tuniv)
  (STA : semantic_typing Γ A Core.tuniv)
  (STB : semantic_typing (Γ ++ A) B Core.tuniv)
  (STM : semantic_typing (Γ ++ A) M B)
  ρ m (Δ : Ctx m) (σ σ' : Sub n m)
  (TS : typing_subst Δ σ Γ) (TS' : typing_subst Δ σ' Γ) (CS : ConvSub Δ Γ σ σ')
  (Fρ : fits Γ ρ) (VS : ValSub Δ Γ σ ρ) (VS' : ValSub Δ Γ σ' ρ)
  (EVS : EqValSub Δ Γ σ σ' ρ) (CΔ : ctx Δ) u a (WT : wt u a)
  (evAN : EvalRel (Core.abs A M) ρ u) (evAB : EvalRel (Core.tpi A B) ρ a) :
  forall RB, max (rk u) (rk a) < RB -> Val RB Δ (Core.abs A M)[σ] (Core.tpi A B)[σ] WT.
Proof.
  have Vρ : valid_env ρ := fits_valid_env Fρ.
  have evU : EvalRel Core.tuniv ρ tuniv by (cbn; apply le_refl).
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
      exists A[σ], B[⇑ σ]. split; [ apply ms_refl | ]. split.
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
        eapply Val_beta_expand; [ | exact HvB ].
        eapply ms_trans; [ apply hr_beta | apply ms_refl ].
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
        eapply EqVal_headred_expand;
          [ eapply ms_trans; [ apply hr_beta | apply ms_refl ]
          | eapply ms_trans; [ apply hr_beta | apply ms_refl ]
          | exact HvB ].
Qed.

Lemma st_abs_EqVal_edge (A : Tm n) (B M : Tm (S n))
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
    have VN : Val (S RB) Δ (Core.abs A M)[σ'] (Core.tpi A B)[σ] WT
      by (eapply Val_EqVal_fwd; [ exact VN0 | exact (EqValTy_sym (EqVal_EqValTy eqPi)) ]).
    rewrite Val_abs in VM. rewrite Val_abs in VN.
    move: VM => [VTd VPiM]. move: VN => [_ VPiN].
    split; [ exact VTd | ]. split; [ exact VPiM | ]. split; [ exact VPiN | ].
    (* the [EqValPi] edge *)
    exists A[σ], B[⇑ σ]. split; [ apply ms_refl | ].
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
    { move=> RB0 Hr0. eapply Val_EqVal_fwd; [ exact (VPall RB0 Hr0) | ].
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
    eapply EqVal_headred_expand;
      [ eapply ms_trans; [ apply hr_beta | apply ms_refl ]
      | eapply ms_trans; [ apply hr_beta | apply ms_refl ]
      | exact HvB ].
Qed.

Lemma st_abs A B M :
  typing Γ A Core.tuniv ->
  typing (Γ ++ A) B Core.tuniv ->
  semantic_typing Γ A Core.tuniv ->
  semantic_typing (Γ ++ A) B Core.tuniv ->
  semantic_typing (Γ ++ A) M B ->
(* ------------------------- *)
  semantic_typing Γ (Core.abs A M) (Core.tpi A B).
Proof.
  move=> TA TB STA STB STM.
  move=> ρ m Δ σ σ' TS TS' CS Fρ VS VS' EVS CΔ u a WT evAN evAB.
  split.
  - eapply st_abs_Val_edge; eassumption.
  - eapply st_abs_EqVal_edge; eassumption.
Qed.

Lemma st_univ :
  ctx Γ ->
(* ------------------------- *)
  semantic_typing Γ Core.tuniv Core.tuniv.
Proof.
  (* TODO: rework for current Rec signatures / WF Val-EqVal. *)
Admitted.


(* -------- semantic conversion rules -------- *)

(* c_conv: M ≡ N : A, A ≡ B : tuniv i ⟹ M ≡ N : B *)
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
  move=> RB Hrank. eapply EqVal_EqVal_fwd;
    [ exact (eqMN RB Hrank)
    | eapply EqVal_EqValTy; eapply (eqAB (S RB)); cbn in Hrank |- *; lia ].
Qed.

(* c_refl: M : A ⟹ M ≡ M : A *)
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
  move=> RB Hrank. eapply EqVal_sym. exact (h RB Hrank).
Qed.

(* c_trans: M ≡ N : A, N ≡ P : A ⟹ M ≡ P : A *)
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
  move=> RB Hrank. eapply EqVal_trans; [ exact (e1 RB Hrank) | exact (e2 RB Hrank) ].
Qed.

(* c_app1: N ≡ N' : (tpi A B), M : A ⟹ app N M ≡ app N' M : B[M..] *)
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
  move: EM => [_ [_ [_ EPi]]]. move: EPi => [A0 [B0 [HRpi paev]]].
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
    by (eapply EvalRel_app_Comp; [ exact Vρ | exact EBM | exact evB_af ]).
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

(* c_app2: N : (tpi A B), M ≡ M' : A ⟹ app N M ≡ app N M' : B[M..] *)
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
  move: VN => [_ VPi]. move: VPi => [A0 [B0 [HRpi [_ pae]]]].
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
    by (eapply EvalRel_app_Comp; [ exact Vρ | exact EBM | exact evB_af ]).
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

(* c_beta: A, B, body N, arg M ⟹ app (abs A N) M ≡ N[M..] : B[M..] *)
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
Proof. Admitted.

(* c_eta: function extensionality *)
Lemma sc_eta A B (N N' : Tm n) :
  typing Γ A Core.tuniv ->
  typing (Γ ++ A) B Core.tuniv ->
  typing Γ N (Core.tpi A B) ->
  typing Γ N' (Core.tpi A B) ->
  conv (Γ ++ A) (Core.app N⟨↑⟩ (var var_zero))
                (Core.app N'⟨↑⟩ (var var_zero)) B ->
  semantic_typing Γ A Core.tuniv ->
  semantic_typing (Γ ++ A) B Core.tuniv ->
  semantic_typing Γ N (Core.tpi A B) ->
  semantic_typing Γ N' (Core.tpi A B) ->
  semantic_conv2 (Γ ++ A) (Core.app N⟨↑⟩ (var var_zero))
                          (Core.app N'⟨↑⟩ (var var_zero)) B ->
(* ------------------------- *)
  semantic_conv2 Γ N N' (Core.tpi A B).
Proof. Admitted.

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
Proof. Admitted.

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
Proof. Admitted.
*)

Lemma sc_succ M N  :
  conv Γ M N Core.tnat ->
  semantic_conv2 Γ M N Core.tnat ->
(* ------------------------- *)
  semantic_conv2 Γ (Core.succ M) (Core.succ N) Core.tnat.
Proof.
  move=> CMN SC1.
  move=> ρ m Δ σ TS FR VS CD u a WT EM EA.
  have Vρ : valid_env ρ := fits_valid_env FR.
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
  refine (ex_intro _ M[σ] (conj _ (ex_intro _ N[σ] (conj _ _))));
    [ apply ms_refl | apply ms_refl | ].
  (* inner [EqVal M[σ] N[σ] : tnat] at the predecessor value [w] *)
  destruct (is_bot w) eqn:Bw.
  { have Ew : w = bot by (apply is_bot_eq; rewrite Bw).
    move: (wt_succ_inv WT). rewrite Ew. move=> wb. apply EqVal_Bot. }
  have RPw : 1 <= rk w := rk_pos Bw.
  have evN : EvalRel Core.tnat ρ tnat by (cbn; apply le_refl).
  apply (SC1 ρ m Δ σ TS FR VS CD w tnat (wt_succ_inv WT) EMw evN RB).
  cbn in Hrank |- *. lia.
Qed.

(* c_tpi: A0 ≡ A1 : tuniv i, B0 ≡ B1 : tuniv i ⟹ tpi A0 B0 ≡ tpi A1 B1 : tuniv i *)
Lemma sc_tpi A0 A1 (B0 B1 : Tm (S n)) :
  conv Γ A0 A1 Core.tuniv ->
  conv (Γ ++ A0) B0 B1 Core.tuniv ->
  semantic_conv2 Γ A0 A1 Core.tuniv ->
  semantic_conv2 (Γ ++ A0) B0 B1 Core.tuniv ->
(* ------------------------- *)
  semantic_conv2 Γ (Core.tpi A0 B0) (Core.tpi A1 B1) Core.tuniv.
Proof. Admitted.

(* c_abs: A ≡ A' : tuniv i, M ≡ M' : B ⟹ abs A M ≡ abs A' M' : tpi A B *)
Lemma sc_abs (A A' : Tm n) (B M M' : Tm (S n)) :
  conv Γ A A' Core.tuniv ->
  conv (Γ ++ A) M M' B ->
  semantic_conv2 Γ A A' Core.tuniv ->
  semantic_conv2 (Γ ++ A) M M' B ->
(* ------------------------- *)
  semantic_conv2 Γ (Core.abs A M) (Core.abs A' M') (Core.tpi A B).
Proof. Admitted.


End SemanticTyping.


(*
------------------------------------------------------------------------
-- Part 6: Main mutual block — adequacySub2 / adequacyEqSub2 /
--                              adequacyConvSub2
--
-- These three theorems form the main "Theorem 2" of the paper
-- (p.660) and the central mutual block of Adequacy2.agda.  In the
-- Agda development they are a single TERMINATING mutual block; here
-- we state them as Theorems with proofs left admitted, and use the
-- previously defined semantic_typing / semantic_conv / semantic_conv2
-- to express their (unfolded) conclusions.
--
-- The Agda hypotheses translate as follows (with the source context
-- H instantiated to ctx_empty, i.e. closing substitutions):
--
--     HasType G M A             ≈  typing Γ M A
--     ConvTm   G M N A          ≈  conv   Γ M N A
--     σ : Sub h g               ≈  σ : Sub g  (= fin g -> Tm 0)
--     ρ : EnvApprox g           ≈  ρ : Env g
--     CoherentEnv ρ             ≈  valid_env ρ   (from fits_valid_env)
--     ValidSub2 H G σ ρ         ≈  ValSub Γ ρ σ
--     ValidConvSub2 H G σ σ' ρ  ≈  EqValSub Γ ρ σ σ'
--     Fits G ρ                  ≈  fits Γ ρ
--     WtSub H G σ               ≈  typing_subst ctx_empty σ Γ
--     WtConvSub H G σ σ'        ≈  (no Rocq counterpart yet — would
--                                  be a pointwise conv predicate)
--     WfCtx H                   ≈  ctx Γ
--     FinMem u a                ≈  wt u a
--     Val2 H M[σ] A[σ] u a      ≈  Val M[σ] A[σ] (h : wt u a)
u--     EqVal2 H M[σ] N[σ] A[σ]   ≈  EqVal M[σ] N[σ] A[σ] (h : wt u a)
------------------------------------------------------------------------
*)

(* adequacySub2 (Adequacy2.agda, p.660 Theorem 2 part 4):

       HasType G M A
     → CoherentEnv ρ, ValidSub2 H G σ ρ, Fits G ρ,
       WtSub H G σ, WfCtx H
     → (u : FinEl) -> EvalRel M ρ u
     → (a : FinEl) -> EvalRel A ρ a ->  FinMem u a
     → Val2 H M[σ] A[σ] u a

   Rocq: well-typed terms are semantically typed.                *)
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
    + eapply sc_succ; eauto.
    + eapply sc_abs; eauto.
    + eapply sc_tpi; eauto.
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

(* evalRel_Pi_trivial: every Pi type evaluates to (tpi bot nil).
   Mirrors evalRel-Pi-trivial in PiInjectivity.agda. *)
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

(* piConv (Corollary 6, parts 1–3):
   From conv Γ A₀ (tpi B₁ F₁) (tuniv i) extract HeadRed A₀ (tpi B₀ F₀)
   and conversions on the domain and codomain.
 *)
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

(* piInjectivity (Corollary): from conv Γ (tpi A₀ B₀) (tpi A₁ B₁) U,
   extract domain and codomain conversions.
   Mirrors piInjectivity in PiInjectivity.agda. *)
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

