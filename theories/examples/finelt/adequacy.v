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

(* A valid substitution σ maps every term in ρ to one that 
   can be interpreted in Δ. *) 
(* The substitution relations hold at *every* fuel [RB] (the [forall RB]
   is at the leaf).  This is what lets [st_conv] obtain [EqVal (S RB)]
   for the type-equality bridge while the term is used at fuel [RB],
   without any (false) fuel-monotonicity step. *)
Definition ValSub {n} (Δ : Ctx n) {g} (Γ : Ctx g) (σ : Sub g n) (ρ : Env g)    : Prop :=
  forall i u, valid u -> le u (ρ i) ->
    forall a, EvalRel (lookup i Γ) ρ a ->
    forall (h : wt u a) RB,
      Val RB Δ (σ i) (lookup i Γ)[σ] h.

Lemma ValSub_empty {g} (Δ : Ctx g)(σ : Sub 0 g) :
  ValSub Δ ctx_empty σ null.
unfold ValSub. done. Qed.

Lemma ValSub_cons {g} (Γ : Ctx g) (ρ : Env g) {h} (Δ : Ctx h) (σ : Sub g h) (A: Tm g) v (M : Tm h):
    (forall u, valid u -> le u v -> forall a (h : wt u a),
    EvalRel A ρ a ->
    forall RB, Val RB Δ M A[σ] h) ->
    ValSub Δ Γ σ ρ ->
    ValSub Δ (Γ ++ A) (M .: σ) (v .: ρ).
Proof.
  intros hyp0 VS.
  unfold ValSub in *.
  move=> i u0 Vu0 Le0 a0 E0 WT0 RB.
  destruct i as [i|].
  - (* succ case *) 
    cbn in *. asimpl.
    apply EvalRel_unwk in E0.
    specialize (VS i u0 Vu0 Le0 a0 E0 WT0 RB).
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
    forall (h : wt u a) RB,
      EqVal RB Δ (σ1 i) (σ2 i) (lookup i Γ)[σ1] h.

  
Lemma EqValSub_empty {g} (Δ : Ctx g)(σ1 σ2 : Sub 0 g) :
   EqValSub Δ ctx_empty  σ1 σ2 null.
unfold EqValSub. done. Qed.

Lemma EqValSub_cons {h} {g} (Δ : Ctx h) (Γ : Ctx g) (ρ : Env g)
  (σ1 σ2 : Sub g h) A v (M1 M2 : Tm h):
    (forall u, valid u -> le u v -> forall a (h : wt u a),
    EvalRel A ρ a ->
    forall RB, EqVal RB Δ M1 M2 A[σ1] h) ->
    EqValSub Δ Γ σ1 σ2 ρ ->
    EqValSub Δ (Γ ++ A)  (M1 .: σ1) (M2 .: σ2) (v .: ρ).
Proof.
  intros hyp0 VS.
  unfold ValSub in *.
  move=> i u0 Vu0 Le0 a0 E0 WT0 RB.
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

(* Cross-substitution conv: if M is typed at A in Γ, and σ ≈ σ' pointwise
   (both as ConvSub and well-typed), then M[σ] is conv to M[σ'] at A[σ].
   This is the syntactic analog of EqValSub's effect at any well-typed M.
   Proof would go by induction on typing — admitted here, to be developed
   alongside the other syntactic substitution lemmas. *)
Lemma subst_conv_cross {n} (Γ : Ctx n) (M A : Tm n) :
  typing Γ M A ->
  forall m (Δ : Ctx m) (σ σ' : Sub n m),
    ctx Δ ->
    typing_subst Δ σ Γ ->
    typing_subst Δ σ' Γ ->
    ConvSub Δ Γ σ σ' ->
    conv Δ M[σ] M[σ'] A[σ].
Proof. Admitted.

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
    (forall RB, Val RB Δ M[σ] A[σ] WT) /\
    (forall RB, EqVal RB Δ M[σ] M[σ'] A[σ] WT).

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
    (forall RB, EqVal RB Δ M[σ] N[σ] A[σ] WT).

Lemma EqValSub_ValSub_left {n} (Γ : Ctx n) ρ {m} (Δ : Ctx m) σ1 σ2 :
  EqValSub Δ Γ σ1 σ2 ρ ->
  ValSub Δ Γ σ1 ρ.
Proof.
  move=> EVS i u Vu LE a E1 h RB.
  specialize (EVS i u Vu LE a E1 h RB).
  eapply EqVal_Val1; eauto.
Qed.

Lemma ValSub_EqValSub {n} (Γ : Ctx n) ρ {m} (Δ : Ctx m) σ :
  ValSub Δ Γ σ ρ ->
    EqValSub Δ Γ σ σ ρ .
Proof.
  move=> VS.
  unfold EqValSub.
  move=> i u Vu LE a E1 h RB.
  specialize (VS i u Vu LE a E1 h RB).
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
Lemma Val_app_transport {n} (Γ : Ctx n) (MN T : Tm n) u v a af
  (h : wt v af) (h' : wt u a) :
  compatible a af -> le u v ->
  forall RB, Val RB Γ MN T h -> Val RB Γ MN T h'.
Admitted.

Lemma EqVal_app_transport {n} (Γ : Ctx n) (M N T : Tm n) u v a af
  (h : wt v af) (h' : wt u a) :
  compatible a af -> le u v ->
  forall RB, EqVal RB Γ M N T h -> EqVal RB Γ M N T h'.
Admitted.

(* subst1_subst_comm: a pure autosubst fact (single substitution commutes
   with [σ]).  [asimpl] cannot discharge it here because this development's
   [..] uses the raw [var] constructor rather than the typeclass [ids], so
   the [asimpl] rewrite system does not fire (the same gap that leaves
   [syntax.typing.substitution_tm] admitted).  ADMITTED. *)
Lemma subst1_subst_comm {n m} (B : Tm (S n)) (N : Tm n) (σ : Sub n m) :
  B[N .: var][σ] = B[⇑ σ][N[σ] .: var].
Admitted.


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
  - move=> RB. eapply Val_EqVal_fwd;
      [ exact (valMA RB) | eapply EqVal_EqValTy; exact (eqAB (S RB)) ].
  - move=> RB. eapply EqVal_EqVal_fwd;
      [ exact (eqvalMA RB) | eapply EqVal_EqValTy; exact (eqAB (S RB)) ].
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
  have Vρ : valid_env ρ := fits_valid_env Fρ.
  move: (substitution_tm _ _ _ _ _ TA TS CΔ) => TAs. cbn in TAs.
  have CE: ctx (Δ ++ A[σ]). eapply c_cons; eauto.
  have TSE: typing_subst (Δ ++ A[σ]) (⇑σ) (Γ ++ A).
  eapply typing_subst_lift; eauto.
  have TBs: typing (Δ ++ A[σ]) B[⇑ σ] Core.tuniv.
  {
    have CC: typing (Δ ++ A[σ]) B[⇑ σ] Core.tuniv[⇑ σ].
    eapply substitution_tm; eauto. 
    cbn in CC. auto.
  } 
  specialize (STA ρ m Δ σ σ' TS TS' CS Fρ VS VS' EVS CΔ).
  split; intro RB; destruct RB; try solve [cbn; auto].
  - destruct (is_bot u) eqn:Hu.
    { have Eu : u = bot by apply is_bot_eq; rewrite Hu.
      subst u. apply Val_Bot. } 
    cbn in evAN. destruct u; try done.
    move: evAN => [Vl [NNl [a0 [WTa0 [Ra0 h0]]]]].
    cbn in evAB. destruct a; try done. inversion WT.
    move: evAB => [Va [Vl0 [Ea [a' [Ra' h']]]]].
    have WTa: wt a tuniv. inversion H5. auto. 
    specialize (STA _ _ WTa Ea). cbn in STA. autorewrite with le in STA.
    destruct STA as [ValA EValA]. done.
    
    subst.
    cbn.
    split.
    exists A[σ]. exists B[⇑ σ]. 
    repeat split; eauto. 
    + eapply ms_refl. 
    + rewrite Va Vl0. done.
    + eapply Val_irr. eapply ValA.
    + intros u v WTua APP NB N TN VN.
      have FE: fits (Γ ++ A) (u .: ρ).
      { eapply (fits_cons TA Ea WTa WTua ); eauto. } 
Admitted.

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
  split; intro RB.
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
      (* argument IH at the selection key *)
      have [valN _] :=
        STN ρ m Δ σ σ' TS TS' CS Fρ VS VS' EVS CΔ u_sel b WTu_sel evN_usel evA_b.
      (* function IH, exposing its value edge *)
      have [valMbig _] :=
        STM ρ m Δ σ σ' TS TS' CS Fρ VS VS' EVS CΔ (abs g) (tpi b f) WTbig evMbig evTpi.
      have TNσ : typing Δ N[σ] A[σ]
        by (eapply substitution_tm; [ exact TN | exact TS | exact CΔ ]).
      have VM := valMbig (S RB). rewrite Val_abs in VM. move: VM => [_ VPi].
      move: VPi => [A0 [B0 [HRpi [pav _]]]].
      asimpl in HRpi.
      have [EA0 EB0] := HeadRed_tpi_eq HRpi. subst A0 B0.
      (* apply the value edge to the argument *)
      have Vapp := pav u_sel v_sel Sel WTu_sel N[σ] TNσ (valN RB).
      (* the edge codomain [app f u_sel] is compatible with the given [a] *)
      have Caaf : compatible a (app f u_sel).
      { destruct (is_bot (app f u_sel)) eqn:Hbaf.
        - have -> : app f u_sel = bot by apply is_bot_eq; rewrite Hbaf.
          apply compatible_bot.
        - have NB : ~ is_bot (app f u_sel) by rewrite Hbaf.
          have evB_af : EvalRel B[N..] ρ (app f u_sel).
          { eapply EvalRel_Pi_app_type.
            - exact evTpi.
            - exact Vρ.
            - exact Vusel.
            - reflexivity.
            - exact NB.
            - exact evN_usel. }
          eapply EvalRel_app_Comp; [ exact Vρ | exact evBN | exact evB_af ]. }
      (* the result element [u] is below the selection value [v_sel] *)
      have LEu_vsel : le u v_sel.
      { rewrite le_fun_cons in LEfun.
        have LEua := proj1 (andb_prop _ _ LEfun).
        rewrite Eq_vsel in LEua. exact LEua. }
      (* transport the edge result to the goal codomain *)
      asimpl in Vapp.
      match goal with
      | |- Val _ _ _ ?T _ => replace T with (B[⇑ σ][N[σ] .: var])
      end;
        [ exact (@Val_app_transport _ Δ _ _ u v_sel a (app f u_sel)
                   (wt_Selection_abs WTbig Sel) WT Caaf LEu_vsel RB Vapp)
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
      have EM := eqvalMbig (S RB). rewrite EqVal_abs in EM.
      move: EM => [_ [_ [VPiM' EPi]]].
      move: EPi => [A0 [B0 [HRpi paev]]].
      move: VPiM' => [A0' [B0' [HRpi' [_ pae']]]].
      asimpl in HRpi. asimpl in HRpi'.
      have [EA0 EB0] := HeadRed_tpi_eq HRpi. subst A0 B0.
      have [EA0' EB0'] := HeadRed_tpi_eq HRpi'. subst A0' B0'.
      (* function variation: [App sf sa] vs [App sf' sa] *)
      have Efun := paev u_sel v_sel Sel WTu_sel N[σ] TNσ (valN RB).
      (* argument variation: [App sf' sa] vs [App sf' sa'] *)
      have Earg := pae' u_sel v_sel Sel WTu_sel N[σ] N[σ'] convNN' (eqvalN RB).
      (* combine by transitivity *)
      have Ecomb := EqVal_trans Efun Earg.
      (* the edge codomain [app f u_sel] is compatible with the given [a] *)
      have Caaf : compatible a (app f u_sel).
      { destruct (is_bot (app f u_sel)) eqn:Hbaf.
        - have -> : app f u_sel = bot by apply is_bot_eq; rewrite Hbaf.
          apply compatible_bot.
        - have NB : ~ is_bot (app f u_sel) by rewrite Hbaf.
          have evB_af : EvalRel B[N..] ρ (app f u_sel).
          { eapply EvalRel_Pi_app_type.
            - exact evTpi.
            - exact Vρ.
            - exact Vusel.
            - reflexivity.
            - exact NB.
            - exact evN_usel. }
          eapply EvalRel_app_Comp; [ exact Vρ | exact evBN | exact evB_af ]. }
      have LEu_vsel : le u v_sel.
      { rewrite le_fun_cons in LEfun.
        have LEua := proj1 (andb_prop _ _ LEfun).
        rewrite Eq_vsel in LEua. exact LEua. }
      (* transport the combined edge result to the goal codomain *)
      asimpl in Ecomb.
      match goal with
      | |- EqVal _ _ _ _ ?T _ => replace T with (B[⇑ σ][N[σ] .: var])
      end;
        [ exact (@EqVal_app_transport _ Δ _ _ _ u v_sel a (app f u_sel)
                   (wt_Selection_abs WTbig Sel) WT Caaf LEu_vsel RB Ecomb)
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
Proof. Admitted.

(* t_tpi: A : tuniv i, (Γ ++ A) ⊢ B : tuniv i ⟹ tpi A B : tuniv i *)
Lemma st_tpi A B :
  typing Γ A Core.tuniv ->
  typing (Γ ++ A) B Core.tuniv ->
  semantic_typing Γ A Core.tuniv ->
  semantic_typing (Γ ++ A) B Core.tuniv ->
(* ------------------------- *)
  semantic_typing Γ (Core.tpi A B) Core.tuniv.
Proof.
  (* TODO: rework for current Rec signatures / WF Val-EqVal. *)
Admitted.

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
Proof. Admitted.

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
  move=> RB. eapply EqVal_sym. exact (h RB).
Qed.

(* c_trans: M ≡ N : A, N ≡ P : A ⟹ M ≡ P : A *)
Lemma sc_trans M N P A :
  conv Γ M N A ->
  conv Γ N P A ->
  semantic_conv2 Γ M N A ->
  semantic_conv2 Γ N P A ->
(* ------------------------- *)
  semantic_conv2 Γ M P A.
Proof. Admitted.

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
  (* TODO: rework for current Rec signatures / WF Val-EqVal. *)
Admitted.

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
  (* TODO: rework for current Rec signatures / WF Val-EqVal. *)
Admitted.

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
                (Core.app N'⟨↑⟩ (var var_zero)) A⟨↑⟩ ->
  semantic_typing Γ A Core.tuniv ->
  semantic_typing (Γ ++ A) B Core.tuniv ->
  semantic_typing Γ N (Core.tpi A B) ->
  semantic_typing Γ N' (Core.tpi A B) ->
  semantic_conv2 (Γ ++ A) (Core.app N⟨↑⟩ (var var_zero))
                          (Core.app N'⟨↑⟩ (var var_zero)) A⟨↑⟩ ->
(* ------------------------- *)
  semantic_conv2 Γ N N' (Core.tpi A B).
Proof. Admitted.

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


Lemma sc_tuniv M N  :
  conv Γ M N Core.tuniv ->
  semantic_conv2 Γ M N Core.tuniv ->
(* ------------------------- *)
  semantic_conv2 Γ M N Core.tuniv.
Proof. Admitted.

(* c_tpi: A0 ≡ A1 : tuniv i, B0 ≡ B1 : tuniv i ⟹ tpi A0 B0 ≡ tpi A1 B1 : tuniv i *)
Lemma sc_tpi A0 A1 (B0 B1 : Tm (S n)) :
  conv Γ A0 A1 Core.tuniv ->
  conv (Γ ++ A0) B0 B1 Core.tuniv ->
  semantic_conv2 Γ A0 A1 Core.tuniv ->
  semantic_conv2 (Γ ++ A0) B0 B1 Core.tuniv ->
(* ------------------------- *)
  semantic_conv2 Γ (Core.tpi A0 B0) (Core.tpi A1 B1) Core.tuniv.
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
    + eapply st_nrec; eauto.
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
    + eapply sc_nrec_Z; eauto.
    + eapply sc_nrec_S; eauto.
    + eapply sc_tuniv; eauto.
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
  move=> i u Vu LE a ER h.
  unfold bot_env in LE.
  apply le_bot_inv in LE. subst.
  apply Val_Bot.
Qed.


Lemma EqValSub_id n (Γ:Ctx n) :
  EqValSub Γ Γ var var bot_env.
Proof.
  unfold EqValSub.
  move=> i u Vu LE a ER h.
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
  have EVfun : forall RB, EqVal RB Γ A0[var] (Core.tpi B1 F1)[var] Core.tuniv[var] WT.
  { intro RB. eapply SCA.
    - apply typing_subst_id. exact cΓ.
    - apply fits_bot_env. exact cΓ.
    - apply ValSub_id.
    - exact cΓ.
    - exact evA0.
    - exact evU. }
  (* EVfun : forall RB, EqVal RB Γ A0[var] (tpi B1 F1)[var] tuniv[var] WT *)
  move: (EVfun 1) => EV1.
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

