(* Fundamental theorem of the logical relation

   see Adequacy2.adga

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
Definition ValSub {n} (Δ : Ctx n) {g} (Γ : Ctx g) (σ : Sub g n) (ρ : Env g)    : Prop :=
  forall i u, valid u -> le u (ρ i) ->
    forall a, EvalRel (lookup i Γ) ρ a ->
    forall (h : wt u a),
      Val Δ (σ i) (lookup i Γ)[σ] h.

Lemma ValSub_empty {g} (Δ : Ctx g)(σ : Sub 0 g) : 
  ValSub Δ ctx_empty σ null.
unfold ValSub. done. Qed.

Lemma ValSub_cons {g} (Γ : Ctx g) (ρ : Env g) {h} (Δ : Ctx h) (σ : Sub g h) (A: Tm g) v (M : Tm h):
    (forall u, valid u -> le u v -> forall a (h : wt u a),
    EvalRel A ρ a ->
    Val Δ M A[σ] h) ->
    ValSub Δ Γ σ ρ ->
    ValSub Δ (Γ ++ A) (M .: σ) (v .: ρ).
Proof.
  intros hyp0 VS.
  unfold ValSub in *.
  move=> i u0 Vu0 Le0 a0 E0 WT0.
  destruct i as [i|].
  - (* succ case *) 
    cbn in *. asimpl.
    apply EvalRel_unwk in E0.
    specialize (VS i u0 Vu0 Le0 a0 E0 WT0).
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
    forall (h : wt u a),
      EqVal Δ (σ1 i) (σ2 i) (lookup i Γ)[σ1] h.

  
Lemma EqValSub_empty {g} (Δ : Ctx g)(σ1 σ2 : Sub 0 g) : 
   EqValSub Δ ctx_empty  σ1 σ2 null.
unfold EqValSub. done. Qed.

Lemma EqValSub_cons {h} {g} (Δ : Ctx h) (Γ : Ctx g) (ρ : Env g)
  (σ1 σ2 : Sub g h) A v (M1 M2 : Tm h):
    (forall u, valid u -> le u v -> forall a (h : wt u a),
    EvalRel A ρ a ->
    EqVal Δ M1 M2 A[σ1] h) ->
    EqValSub Δ Γ σ1 σ2 ρ ->
    EqValSub Δ (Γ ++ A)  (M1 .: σ1) (M2 .: σ2) (v .: ρ).
Proof.
  intros hyp0 VS.
  unfold ValSub in *.
  move=> i u0 Vu0 Le0 a0 E0 WT0.
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

Definition semantic_typing {n} (Γ : Ctx n) (M : Tm n) (A : Tm n) :=
  forall ρ m (Δ : Ctx m) (σ σ': Sub n m) (TS : typing_subst Δ σ Γ)
    (TS' : typing_subst Δ σ' Γ)
    (CS : ConvSub Δ Γ σ σ')
    (F : fits Γ ρ)
    (VS : EqValSub Δ Γ σ σ' ρ) (cΔ : ctx Δ),
  forall u a (WT : wt u a),
    EvalRel M ρ u ->
    EvalRel A ρ a ->
    Val Δ M[σ] A[σ] WT /\
    EqVal Δ M[σ] M[σ'] A[σ] WT.
Definition semantic_conv2 {n} (Γ : Ctx n) (M N: Tm n) (A : Tm n) :=
  forall ρ  m (Δ : Ctx m) σ1 σ2 (TS1 : typing_subst Δ σ1 Γ)
    (TS2 : typing_subst Δ σ2 Γ)
    (CS : ConvSub Δ Γ σ1 σ2)
    (F : fits Γ ρ)
    (EVS : EqValSub Δ Γ σ1 σ2 ρ) (cΔ : ctx Δ),
  forall u a (WT : wt u a),
    EvalRel M ρ u ->
    EvalRel A ρ a ->
    EqVal Δ M[σ1] N[σ1] A[σ1] WT /\
    EqVal Δ M[σ1] N[σ2] A[σ1] WT.

Lemma EqValSub_ValSub_left {n} (Γ : Ctx n) ρ {m} (Δ : Ctx m) σ1 σ2 :
  EqValSub Δ Γ σ1 σ2 ρ ->
  ValSub Δ Γ σ1 ρ.
Proof.
  move=> EVS i u Vu LE a E1 h.
  specialize (EVS i u Vu LE a E1 h).
  eapply EqVal_Val1; eauto.
Qed.

Lemma ValSub_EqValSub {n} (Γ : Ctx n) ρ {m} (Δ : Ctx m) σ :
  ValSub Δ Γ σ ρ ->
    EqValSub Δ Γ σ σ ρ .
Proof.
  move=> VS.
  unfold EqValSub.
  move=> i u Vu LE a E1 h.
  specialize (VS i u Vu LE a E1 h).
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
  Val Γ M T h -> Val Γ M T h'.
Proof.
  move=> LEu LEa VH.
  have h'' : wt u' a by eapply wt_le; eauto.
  have VH'' : Val Γ M T h'' by eapply (@restrictVal _ Γ M T u u' a h'' h); eauto.
  eapply (@downVal _ Γ M T u' a' a h' h''); eauto.
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
    valid u -> app f u = Some v -> ~ is_bot v ->
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
  move=> ρ m Δ σ σ' TS TS' CS FR VS CD u1 a1 WT1 Ex ER.
  cbn in *. move: Ex => [Vu1 Le1].
  split.
  - eapply EqValSub_ValSub_left; eauto.
  - eapply (VS x); eauto.
Qed.

Lemma st_conv M A B :
  typing Γ M A ->
  conv Γ A B Core.tuniv ->
  semantic_typing Γ M A ->
  semantic_conv2 Γ A B Core.tuniv ->
(* ------------------------- *)
  semantic_typing Γ M B.
Proof.
  (* Following Adequacy2.agda's ty-conv case (UCode branch, lines 535-542):
       evA'  = convSound-inv d2 evA       — bridge EvalRel B → EvalRel A
       val   = adequacySub2 d1 ... evA'   — Val of M at A
       eqAB  = adequacyEqSub2 d2 ...      — EqVal of A B at tuniv
       eqvty = snd (snd eqAB)             — extract EqValTy
       result = Val2-EqValTy2-fwd val eqvty  — transport Val along EqValTy
     Coq counterparts:
       conv_EvalRel C2 FR's bwd direction ≈ convSound-inv
       h1 ≈ adequacySub2 d1
       h2 ≈ adequacyEqSub2 d2
       Val_EqVal_fwd ≈ Val2-EqValTy2-fwd *)
  move=> T1 C2 h1 h2.
  move=> ρ m Δ σ σ' TS TS' CS FR VS CD u1 a1 WT1 Ex Ea1.
  (* Step 1: bridge EvalRel B ρ a1 → EvalRel A ρ a1 via conv_EvalRel C2. *)
  move: (conv_EvalRel C2 FR) => [_ [_ [_ bwd]]].
  have Ea1_A : EvalRel A ρ a1 by apply bwd.
  (* Step 2: apply h1 (semantic_typing Γ M A) to get Val Δ M[σ] A[σ] WT1. *)
  have [valM_A eqvalM_A] : Val Δ M[σ] A[σ] WT1 /\ EqVal Δ M[σ] M[σ'] A[σ] WT1
    by exact (h1 ρ m Δ σ σ' TS TS' CS FR VS CD u1 a1 WT1 Ex Ea1_A).
  (* Step 3: apply h2 (semantic_conv2 Γ A B tuniv) at (a1, tuniv).
     We need wt a1 tuniv (extracted from WT1 via wt_ty_tuniv). *)
  have WTa1_univ : wt a1 tuniv by eapply wt_ty_tuniv; exact WT1.
  have evU : EvalRel Core.tuniv ρ tuniv by [].
  have VS_diag : EqValSub Δ Γ σ σ ρ
    by exact (ValSub_EqValSub (EqValSub_ValSub_left VS)).
  move: (h2 ρ m Δ σ σ TS TS (ConvSub_refl TS) FR VS_diag CD
                a1 tuniv WTa1_univ Ea1_A evU) => [eqAB _].
  asimpl in eqAB.
  (* Step 4: extract EqValTy from EqVal at tuniv via EqVal_EqValTy. *)
  have eqAB_ty : EqValTy Δ A[σ] B[σ] WTa1_univ
    by eapply EqVal_EqValTy; exact eqAB.
  (* Step 5: transport Val Δ M[σ] A[σ] WT1 → Val Δ M[σ] B[σ] WT1
     via Val_EqVal_fwd, and EqVal M[σ] M[σ'] A[σ] → EqVal M[σ] M[σ'] B[σ]
     via EqVal_EqVal_fwd. *)
  asimpl.
  split.
  - eapply Val_EqVal_fwd; [exact valM_A | exact eqAB_ty].
  - eapply EqVal_EqVal_fwd; [exact eqvalM_A | exact eqAB_ty].
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
  (* Variable naming follows Adequacy2.agda's [adequacySub2-Lam].
     Agda → Coq:
       d1, d2, d3   ↦  T1, T2, T3   (the three typings)
       semantic     ↦  s1, s2, s3   (semantic_typings)
       g0           ↦  g_body       (abs body fn)
       b, f0        ↦  b_dom, f_pi  (post-destruct tpi)
       a_lam        ↦  a_lam        (type-elt from EvalRel A from EvA1)
       bodyLam      ↦  body_lam     (per-edge EvalRel M)
       evAb         ↦  evA_b        (EvalRel A ρ b_dom)
       u', v'       ↦  u', v'       (PiAppVal inputs)
       N            ↦  P            (syntactic arg)
       x            ↦  x            (selected dom value)
       evM_x_v'     ↦  evM_x_v'     (EvalRel M at (x .: ρ))
       evM_u'_v'    ↦  evM_u'       (after EvalRel_mono_env to (u' .: ρ))
       evB_u'_ef    ↦  evB_u'       (EvalRel B at (u' .: ρ)) *)
  move=> T1 T2 s1 s2 s3.
  move=> ρ m Δ σ σ' TS TS' CS FR VS CD u_sem a_sem WT EvA1 EvA2.
  cbn in EvA1, EvA2.
  asimpl.
  have VSl : ValSub Δ Γ σ ρ by exact (EqValSub_ValSub_left VS).
  split; [|admit].
  dependent destruction WT.
  - (* wt_bot: u_sem = bot. *) apply Val_Bot.
  - (* wt_tuniv: EvA1 forces u_sem = abs, but here u_sem = tuniv. *) done.
  - (* wt_tnat *) done.
  - (* wt_zero *) done.
  - (* wt_succ *) done.
  - (* wt_tpi  *) done.
  - (* wt_abs: main case.  Names from dependent destruction:
       a (dom), g (codom fn = f_pi), f (abs body = g_body),
       w (wt of keys),  w0 (wt of vals),
       i (valid (abs f)),  WT (wt (tpi a g) tuniv).            *)
    rename a into b_dom, g into f_pi, f into g_body.
    rename w into w_keys, w0 into w_vals, i into V_abs_g.
    (* EvA1 destructure: EvalRel (abs A M) ρ (abs g_body) *)
    destruct EvA1 as [V_g_body [Nnil_g [a_lam [WT_a_lam_univ [evA_a_lam body_lam]]]]].
    (* EvA2 destructure: EvalRel (tpi A B) ρ (tpi b_dom f_pi) *)
    destruct EvA2 as [V_b_dom [V_f_pi [evA_b_dom [a_pi [evA_a_pi body_pi]]]]].

    (* Goal: Val Δ (Core.abs A[σ] M[⇑σ]) (Core.tpi A[σ] B[⇑σ]) (wt_abs ...). *)
    have Vρ : valid_env ρ by eauto with valid.
    have TD_A : typing Δ A[σ] Core.tuniv.
    { have h := @substitution_tm _ Γ A Core.tuniv _ Δ σ T1 TS CD. exact h. }
    have ctx_ΔA : ctx (Δ ++ A[σ])
      by eapply c_cons; eauto.
    have TD_B : typing (Δ ++ A[σ]) B[⇑σ] Core.tuniv.
    { have TS_lift : typing_subst (Δ ++ A[σ]) (⇑σ) (Γ ++ A)
        by exact (@typing_subst_lift _ Δ _ σ Γ A ctx_ΔA TS).
      have h := @substitution_tm _ (Γ ++ A) B Core.tuniv _ (Δ ++ A[σ]) (⇑σ)
                  T2 TS_lift ctx_ΔA. exact h. }
    cbn.
    split.
    + (* ValTy A[σ] tuniv (wt_abs_ty WT) — i.e., the Pi-type as a type.
         The witness wt_abs_ty (wt_abs ...) is defined via inversion and does
         not reduce in cbn, blocking unfolding of Rec.ValTy.  The proper
         construction mirrors Agda's [adequacySub2 (ty-Pi d1 d2)] which
         yields ValTyPi2 directly.  Left admitted — the construction is
         analogous to st_tpi (which is itself currently admitted). *)
      admit.
    + (* ValPi: produce A0 = A[σ], B0 = B[⇑σ], with HeadRed by ms_refl. *)
      unfold Rec.ValPi.
      exists A[σ], B[⇑σ].
      split; first by apply ms_refl.
      split; [|admit (* PiAppEq for abstraction — needs adequacyEqSub recursion *)].
      (* PiAppVal: forall u v t Vu APP NB APPg P, typing P A[σ] -> Val P A[σ] -> Val (app abs P) B[P..]. *)
      unfold Rec.PiAppVal.
      intros u v_body t_codom Vu APPgbody NBv APPfpi P TP VP.
      (* Goal: Val Δ (Core.app (Core.abs A[σ] M[⇑σ]) P) B[⇑σ][P..] (wt_abs_inv2 WT_full Vu APPgbody NBv APPfpi). *)
      (* By beta-expand: app (abs A[σ] M[⇑σ]) P →β M[⇑σ][P..]. *)
      eapply Val_beta_expand.
      { eapply ms_trans; [eapply hr_beta | eapply ms_refl]. }
      (* Now need Val Δ M[⇑σ][P..] B[⇑σ][P..] (wt_abs_inv2 ...). *)
      (* Apply s3 at extended env (u .: ρ) and σ' = P .: σ. *)
      (* Use body_lam to get x with wt x a_lam, le x u, EvalRel M (x .: ρ) v_body. *)
      destruct (body_lam u v_body Vu APPgbody) as [x [wt_x_alam [Lex evM_x_v]]].
      have Vx : valid x by eapply wt_valid_tm; eauto.
      have Vρext_x : valid_env (x .: ρ) by eapply valid_cons; eauto.
      have Vρext_u : valid_env (u .: ρ) by eapply valid_cons; eauto.
      have evM_u : EvalRel M (u .: ρ) v_body.
      { eapply EvalRel_mono_env; first exact evM_x_v.
        - exact Vρext_x.
        - exact Vρext_u.
        - move=> [j|]; cbn; auto using le_refl.
          apply le_refl, Vρ. }
      (* Get y for the codom side. *)
      destruct (body_pi u t_codom Vu APPfpi) as [y [wt_y_apii [Ley evB_y_t]]].
      have Vy : valid y by eapply wt_valid_tm; eauto.
      have Vρext_y : valid_env (y .: ρ) by eapply valid_cons; eauto.
      have evB_u : EvalRel B (u .: ρ) t_codom.
      { eapply EvalRel_mono_env; first exact evB_y_t.
        - exact Vρext_y.
        - exact Vρext_u.
        - move=> [j|]; cbn; auto using le_refl.
          apply le_refl, Vρ. }
      (* Build extended ValSub etc. *)
      have WTu_dom : wt u b_dom by eapply w_keys; eauto.
      have TS_ext : typing_subst Δ (P .: σ) (Γ ++ A)
        by eapply typing_subst_cons; eauto.
      have FR_ext : fits (Γ ++ A) (u .: ρ).
      { eapply fits_cons; first exact T1.
        - exact evA_b_dom.
        - eapply wt_tpi_dom; exact WT.
        - exact WTu_dom.
        - exact FR. }
      have VS_ext : ValSub Δ (Γ ++ A) (P .: σ) (u .: ρ).
      { eapply ValSub_cons; [|exact VSl].
        intros uu Vuu Leu aa hwtu ERAu.
        (* VP : Val Δ P A[σ] (wt_abs_inv1 .. : wt u b_dom).
           Goal: Val Δ P A[σ] hwtu where hwtu : wt uu aa.
           Bridge via restrictVal (uu ≤ u, b_dom side) and type-side
           transport (b_dom vs aa via EvalRel A compatibility).  Same
           issue as st_app's VT_c.  Admitted. *)
        admit. }
      (* Apply s3 at the extended substitution. *)
      have [h_val _] := s3 (u .: ρ) m Δ (P .: σ) (P .: σ) TS_ext TS_ext
                       (ConvSub_refl TS_ext) FR_ext
                       (ValSub_EqValSub VS_ext) CD _ _
                       (wt_abs_inv2 (wt_abs w_keys w_vals V_abs_g WT) Vu APPgbody NBv APPfpi)
                       evM_u evB_u.
      (* h_val : Val Δ M[P .: σ] B[P .: σ] (wt_abs_inv2 ...) *)
      (* Bridge: M[P .: σ] = M[⇑σ][P..] and B[P .: σ] = B[⇑σ][P..]. *)
      have eq_M : M[⇑σ][P..] = M[P .: σ].
      { unfold subst1. asimpl. f_equal.
        apply functional_extensionality => -[j|] //=.
        change (subst_Tm (P .: var) ((σ j)⟨↑⟩) = σ j).
        rewrite renSubst_Tm. exact: instId'_Tm. }
      have eq_B : B[⇑σ][P..] = B[P .: σ].
      { unfold subst1. asimpl. f_equal.
        apply functional_extensionality => -[j|] //=.
        change (subst_Tm (P .: var) ((σ j)⟨↑⟩) = σ j).
        rewrite renSubst_Tm. exact: instId'_Tm. }
      rewrite -eq_M -eq_B in h_val.
      exact h_val.
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
  (* Variable naming follows Adequacy2.agda's [adequacySub2-App-core].
     Agda → Coq:
       dA dB d1 d2          ↦  T1 T2 T3 T4         (the four typings)
       semantic versions    ↦  s1 s2 s3 s4         (semantic_typings)
       u1                   ↦  u1                  (result element)
       ac1                  ↦  a1                  (result type elt)
       evAc1                ↦  ER                  (EvalRel of B[N..] at a1)
       v0                   ↦  v0                  (argument value)
       evA_v0               ↦  evA_v0              (EvalRel N ρ v0)
       evF_sing             ↦  evF_sing            (EvalRel M ρ (v0 ↦ u1))
       typed_f → u_big, a_pi, le_sing, evF_big, fm_big, evPi
       g_big, b_pi, f_pi    ↦  g_big, b_pi, f_pi   (post-destruct)
       typed_a → u_arg, ...
       pav_fun              ↦  pav_fun             (PiAppVal of u_big)
       val_arg              ↦  val_arg             (Val of N at u_arg)
       val_app_raw          ↦  val_app_raw         (PiAppVal applied)
   *)
  move=> T1 T2 T3 T4 s1 s2 s3 s4.
  move=> ρ m Δ σ σ' TS TS' CS FR VS CD u1 a1 WT1 Ex ER.
  have VSl : ValSub Δ Γ σ ρ by exact (EqValSub_ValSub_left VS).
  (* Specialize at (σ, σ') so that .1 still gives Val at σ and .2 gives the
     off-diagonal EqVal M[σ] M[σ'] / N[σ] N[σ'] we need for the EqVal goal. *)
  specialize (s1 ρ m Δ σ σ TS TS (ConvSub_refl TS) FR (ValSub_EqValSub VSl) CD).
  specialize (s3 ρ m Δ σ σ' TS TS' CS FR VS CD).
  specialize (s4 ρ m Δ σ σ' TS TS' CS FR VS CD).
  cbn in Ex.
  destruct (Raw.is_bot u1) eqn:HB.
  - (* EvalRel (app M N) is bot *)
    destruct u1; try done.
    dependent destruction WT1. cbn.
    split; destruct a; try done.
  -
    have TD : typing Δ N[σ] A[σ].
    { eapply (substitution_tm); eauto. }

    (* EvalRel (app M N) decomposes: there is an argument value v0 such that
       M evaluates to the singleton (v0 ↦ u1) and N evaluates to v0. *)
    move: Ex => [v0 [evF_sing evA_v0]].

    (* Typed enlargement of the function via theorem1 (= typing_EvalRel). *)
    move: (typing_EvalRel T3 FR) => typed_f.
    unfold InvTyped in typed_f.
    move: (typed_f _ evF_sing) => [u_big [a_pi [wt_big [le_sing [evF_big evPi]]]]].
    clear typed_f.
    (* Only [abs g_big] is non-trivial. *)
    unfold singleton in le_sing. rewrite HB in le_sing.
    destruct u_big as [| | | | | | g_big]; try done.
    (* Decompose le_sing: (v0 ↦ u1) ≤ abs g_big forces an entry in g_big
       whose sup over keys ≤ v0 is ≥ u1. *)
    inversion wt_big. subst.
    rewrite le_abs in le_sing.
    cbn in le_sing.
    destruct (app g_big v0) eqn:APP_g_big_v0; try done.
    rewrite Bool.andb_true_r in le_sing.

    have Vg_big : valid_fun g_big by eauto with valid.
    (* From wt_big : wt (abs g_big) (tpi b_pi f_pi), the type-side f_pi is
       valid (it's the wt_abs's 4th arg, a wt (tpi _ _) tuniv). *)
    have Vu1 : valid u1 by eapply wt_valid_tm; eauto.
    have Vv0 : valid v0 by eapply EvalRel_valid; eauto.

    (* Typed enlargement of the argument. *)
    move: (typing_EvalRel T4 FR) => typed_a.
    move: (typed_a _ evA_v0) => [u_arg [t_arg [wt_arg [le_arg [evA_arg evT_arg]]]]].
    clear typed_a.
    have Vu_arg : valid u_arg by eauto with valid.

    (* Image of u_arg under g_big (term-side sup) and under the type-side
       function (renamed [f_pi] in Agda — here it is the [g] of wt_abs). *)
    destruct (valid_app_exists Vg_big Vu_arg) as [e_sup [APP_g_big_arg Ve_sup]].
    move: (le_valid_compatible Vu_arg le_arg) => C_arg.
    move: (le_fun_mono_arg Vg_big Vv0 Vu_arg C_arg le_arg APP_g_big_v0 APP_g_big_arg)
      => [_ le_e_sup].

    (* Type-side image of u_arg under the type-side function of the big pi
       (Agda calls it f_pi; here it is the [g] introduced by inversion of
       wt_big above).  We obtain its validity by chaining wt_valid_tm on
       the 4th wt_abs arg (wt (tpi _ g) tuniv) and then valid_tpi2. *)
    have Vf_pi : valid_fun g by eauto with valid.
    destruct (valid_app_exists Vf_pi Vu_arg) as [t_sup [APP_f_pi_arg Vt_sup]].
    (* Image of v0 under the same type-side function, for use with
       le_fun_mono_arg to establish [le t_sup_v0 t_sup]. *)
    destruct (valid_app_exists Vf_pi Vv0) as [t_sup_v0 [APP_f_pi_v0 Vt_sup_v0]].
    move: (le_fun_mono_arg Vf_pi Vv0 Vu_arg C_arg le_arg
             APP_f_pi_v0 APP_f_pi_arg) => [_ le_t_sup].

    (* Apply s3 (semantic_typing of M) at the big witness — extract both
       Val Δ M[σ] (tpi A B)[σ] and EqVal Δ M[σ] M[σ'] (tpi A B)[σ]. *)
    move: (s3 _ _ wt_big evF_big evPi) => [s3val s3eqval].
    asimpl in s3val.
    asimpl in s3eqval.
    dependent destruction wt_big.
    cbn in s3val.
    cbn in s3eqval.
    move: s3val => [vt_pi vpi_fun].
    move: s3eqval => [_ [vpi_fun_σ [vpi_fun_σ' eqvpi_fun]]].
    (* Further destruct to expose the inner wt_tpi (b_pi, f_pi, ...). *)
    dependent destruction wt_big.
    apply ValTy_Val in vt_pi.
    cbn in vt_pi.
    destruct vt_pi as (A_pi & B_pi & red_pi & _ & _ & _ & vA_pi & piEV & piEE).
    unfold Rec.ValPi in vpi_fun.
    destruct vpi_fun as (A0 & B0 & red_fun & pav_fun & pae_fun).
    (* From vpi_fun_σ' extract pae_fun_σ' (PiAppEq for M[σ']). *)
    unfold Rec.ValPi in vpi_fun_σ'.
    destruct vpi_fun_σ' as (A0' & B0' & red_fun_σ' & pav_fun_σ' & pae_fun_σ').
    (* From eqvpi_fun extract paeqv_fun (function-differs, same-arg). *)
    unfold Rec.EqValPi in eqvpi_fun.
    destruct eqvpi_fun as (A0_eq & B0_eq & red_eq & paeqv_fun).
    have red_refl : HeadRed (Core.tpi A[σ] B[⇑ (σ)]) (Core.tpi A[σ] B[⇑ (σ)])
      by eapply ms_refl; eauto.
    move: (HeadRed_tpi_det red_fun red_refl) => [eqA_self eqB_self].
    move: (HeadRed_tpi_det red_fun red_pi)   => [eqA_pi   eqB_pi].
    move: (HeadRed_tpi_det red_fun_σ' red_refl) => [eqA_σ' eqB_σ'].
    move: (HeadRed_tpi_det red_eq red_refl) => [eqA_eq eqB_eq].
    subst.

    (* Validity / non-bot facts. *)
    have NBu1 : ~ is_bot u1.
    { apply EvalRel_valid in evF_sing. unfold singleton in evF_sing.
      rewrite HB in evF_sing. cbn in evF_sing.
      destruct u1; try done. }
    have NBe   : ~ is_bot e by destruct u1; destruct e; try done.
    (* le u1 e (from le_sing manipulation) and le e e_sup (from le_fun_mono_arg)
       give le u1 e_sup, so e_sup is non-bot since u1 is non-bot. *)
    have Ve : valid e
      by eapply (@valid_app g_big v0); eauto.
    have le_u1_e_sup : le u1 e_sup
      by exact (le_trans Vu1 Ve Ve_sup le_sing le_e_sup).
    have NBe_sup : ~ is_bot e_sup.
    { destruct e_sup; try done; intro Hb;
        apply le_bot_inv in le_u1_e_sup; subst u1; done. }

    (* From evPi : EvalRel (Core.tpi A B) ρ (tpi a g) we extract the EvalRel
       on the syntactic domain (used to apply s4 below). *)
    have evPi_copy : EvalRel (Core.tpi A B) ρ (tpi a g) by exact evPi.
    cbn in evPi.
    move: evPi => [_ [_ [evA_a _]]].
    (* evA_a : EvalRel A ρ a *)

    (* Step 1: pav_fun applied to (u_arg, e_sup, t_sup) and the syntactic
       argument N[σ].  Its remaining premise is a Val of N[σ] at A[σ]
       with the witness produced by wt_abs_inv1.                              *)
    specialize (pav_fun u_arg e_sup t_sup Vu_arg APP_g_big_arg NBe_sup
                        APP_f_pi_arg N[σ] TD).

    (* Step 2: discharge that premise via s4 (semantic_typing of N).
       The witness expected by pav_fun is equal to ours by wt_unique, so
       a single rewrite bridges them.                                       *)
    have WT_u_arg_a : wt u_arg a
      := w u_arg e_sup Vu_arg APP_g_big_arg NBe_sup.
    move: (s4 u_arg a WT_u_arg_a evA_arg evA_a) => [Val_N EqVal_N].
    erewrite (wt_unique WT_u_arg_a) in Val_N.
    erewrite (wt_unique WT_u_arg_a) in EqVal_N.
    specialize (pav_fun Val_N).
    (* pav_fun : Val Δ (Core.app M[σ] N[σ]) B[⇑σ][N[σ]..] (wt_abs_inv2 ...) *)

    (* Step 3: bridge the syntactic substitution
         B[⇑σ][N[σ]..]  =  B[N..][σ]
       so pav_fun's conclusion is at the goal's syntactic type. *)
    have subst_comm : B[⇑ σ][N[σ]..] = B[N..][σ].
    { asimpl. f_equal. apply functional_extensionality => -[j|] //=.
      change (subst_Tm (N[σ] .: var) ((σ j)⟨↑⟩) = σ j).
      rewrite renSubst_Tm. exact: instId'_Tm. }
    rewrite subst_comm in pav_fun.

    (* Step 4: EvalRel_Pi_app_type — the codomain B[N..] evaluates to t_sup. *)
    have Vρ : valid_env ρ by eauto with valid.
    (* wt e_sup t_sup via wt_abs's range check (w0) at u_arg, e_sup, t_sup. *)
    have WT_e_sup_t_sup : wt e_sup t_sup
      := w0 u_arg e_sup t_sup Vu_arg APP_g_big_arg NBe_sup APP_f_pi_arg.
    (* If t_sup were bot, wt_bot_inv would force e_sup = bot, contradicting NBe_sup. *)
    have NBt_sup : ~ is_bot t_sup.
    { destruct t_sup; try done; intro Hbt;
        apply wt_bot_inv in WT_e_sup_t_sup; subst e_sup; done. }
    have evB_t_sup : EvalRel B[N..] ρ t_sup
      by eapply EvalRel_Pi_app_type;
         [ exact evPi_copy | exact Vρ | exact Vu_arg
         | exact APP_f_pi_arg | exact NBt_sup | exact evA_arg ].

    (* Step 5: EvalRel_app_Comp — ER and evB_t_sup both witness EvalRel of
       B[N..] in ρ, so a1 and t_sup are compatible. *)
    have C_a1_t_sup : compatible a1 t_sup
      by eapply EvalRel_app_Comp; eauto.

    (* Universe witnesses for Val_transport.
       - WT_t_sup_univ via w2 (the wt_tpi's output-typing forall), which
         needs ~ is_bot t_sup. *)
    have WT_t_sup_univ : wt t_sup tuniv
      := w2 u_arg t_sup Vu_arg APP_f_pi_arg NBt_sup.
    have WT_a1_univ   : wt a1 tuniv by eapply wt_ty_tuniv; exact WT1.

    (* Step 8: Val_transport bridges
           Val ... (wt e_sup t_sup)  ↦  Val ... (wt u1 a1) = WT1.

       Since [a1] and [t_sup] are only compatible (not ordered), we go
       through their lub [c = a1 ⊔ t_sup]:
         pav_fun : Val (e_sup, t_sup)
                --upVal-->  Val (e_sup, c)
                --restrictVal--> Val (u1, c)        [using le u1 e_sup]
                --downVal--> Val (u1, a1) = WT1     [using le a1 c]   *)
    destruct (compatible_lub_exists C_a1_t_sup) as [c LUB_c].
    have Va1 : valid a1 by eauto with valid.
    have Vt_sup_v : valid t_sup by eauto with valid.
    have Vc : valid c by exact (valid_lub Va1 Vt_sup_v LUB_c).
    have WT_c_univ : wt c tuniv
      by eapply wt_lub; [exact WT_a1_univ | exact WT_t_sup_univ | exact LUB_c].
    have le_a1_c : le a1 c
      by eapply le_lub_left; eauto.
    have le_t_sup_c : le t_sup c
      by eapply le_lub_right; eauto.
    have WT_u1_c : wt u1 c
      by eapply wt_le; [exact WT1 | exact le_a1_c | exact WT_a1_univ | exact WT_c_univ].
    have WT_e_sup_c : wt e_sup c
      by eapply wt_le;
         [exact WT_e_sup_t_sup | exact le_t_sup_c | exact WT_t_sup_univ | exact WT_c_univ].

    have eq_subst : B[N .: var][σ] = B[N[σ] .: σ].
      { auto_unfold. rewrite substSubst_Tm. f_equal.
        apply functional_extensionality => -[j|] //=. }

    (* upVal needs Val Δ B[N..][σ] Core.tuniv at the witness c (i.e., ValTy
       of the result-type B[N..][σ] at c).  This follows from semantic_typing
       of B (s2) instantiated at the extended substitution (N[σ] .: σ)
       and the env extended by the typed-enlarged value of N.  The construction
       mirrors the [vt_ac] chain in Adequacy2.agda lines 1184-1213. *)
    have VT_c : Val Δ B[N..][σ] Core.tuniv WT_c_univ.
    { (* (1) Sup ER and evB_t_sup to get EvalRel B[N..] ρ c. *)
      have evB_c : EvalRel B[N..] ρ c
        by eapply EvalRel_sup with (u := a1) (u' := t_sup); eauto.
      (* (2) Forward witness for B[N..]. *)
      destruct (EvalRel_subst1_forward Vρ evB_c) as [v_fwd [evN_vfwd evB_vfwd_c]].
      have Vv_fwd : valid v_fwd by eapply EvalRel_valid; eauto.
      (* (3) Typed-enlarge v_fwd via T4 (typing N A). *)
      move: (typing_EvalRel T4 FR) => typedN.
      destruct (typedN _ evN_vfwd) as [u' [t' [wt_u' [Le_vu' [evN_u' evA_t']]]]].
      clear typedN.
      have Vu' : valid u' by eapply wt_valid_tm; eauto.
      have Vt' : valid t' by eauto with valid.
      have WTt'_univ : wt t' tuniv by eapply wt_ty_tuniv; exact wt_u'.
      (* (4) Lift evB to the env (u' .: ρ). *)
      have Vρext : valid_env (v_fwd .: ρ) by eapply valid_cons; eauto.
      have Vρext' : valid_env (u' .: ρ) by eapply valid_cons; eauto.
      have evB_u'_c : EvalRel B (u' .: ρ) c.
      { eapply EvalRel_mono_env; first exact evB_vfwd_c.
        - exact Vρext.
        - exact Vρext'.
        - move=> [j|]; cbn; auto using le_refl.
          apply le_refl, Vρ. }
      (* (5) Build extended substitution typing / fits / ValSub. *)
      have TS_ext : typing_subst Δ (N[σ] .: σ) (Γ ++ A)
        by eapply typing_subst_cons; eauto.
      have FR' : fits (Γ ++ A) (u' .: ρ)
        by eapply fits_cons; eauto.
      have VS' : ValSub Δ (Γ ++ A) (N[σ] .: σ) (u' .: ρ).
      { eapply ValSub_cons; [|exact VSl].
        intros uu Vuu Leu aa hwtu ERAu.
        have ERN_uu : EvalRel N ρ uu by eapply EvalRel_down; eauto.
        destruct (s4 uu aa hwtu ERN_uu ERAu) as [v _]; exact v. }
      (* (6) Apply s2 at extended substitution. *)
      have evU : EvalRel Core.tuniv (u' .: ρ) tuniv by [].
      move: (s2 (u' .: ρ) m Δ (N[σ] .: σ) (N[σ] .: σ) TS_ext TS_ext (ConvSub_refl TS_ext) FR' (ValSub_EqValSub VS') CD c tuniv WT_c_univ evB_u'_c evU) => [h_val _].
      asimpl in h_val.
      (* h_val : Val Δ B[N[σ] .: σ] Core.tuniv WT_c_univ
         Goal  : Val Δ B[N .: var][σ] Core.tuniv WT_c_univ
         Bridge by substSubst_Tm + pointwise equality of the two substitutions. *)

      auto_unfold in *. rewrite eq_subst. exact h_val.
    } 

    (* Bridge pav_fun's witness (built via wt_abs_inv2) to WT_e_sup_t_sup
       via wt_unique. *)
    erewrite (wt_unique _ WT_e_sup_t_sup) in pav_fun.

    move: (@upVal _ Δ _ _ _ _ _ WT_e_sup_t_sup WT_e_sup_c
                WT_t_sup_univ WT_c_univ le_t_sup_c pav_fun VT_c)=> Val_esup_c.


    (* restrictVal: Val (e_sup, c) → Val (u1, c). *)
    have Val_u1_c (* : Val Δ (Core.app M[σ] N[σ]) B[N..][σ] WT_u1_c *)
      := @restrictVal _ Δ _ _ _ _ _ WT_u1_c WT_e_sup_c
                       le_u1_e_sup Val_esup_c.

    (* ===== EqVal construction =====
       Build EqVal Δ (app M[σ] N[σ]) (app M[σ'] N[σ']) B[N..][σ] WT1.

       Strategy (mirrors Agda's adequacyConvSub2-App-core, transitivity
       through (app M[σ'] N[σ])):
         step1: EqVal (app M[σ] N[σ]) (app M[σ'] N[σ]) — paeqv_fun (fn-differs/arg-same)
         step2: EqVal (app M[σ'] N[σ]) (app M[σ'] N[σ']) — pae_fun_σ' (PiAppEq using
                 subst_conv_cross for the conv premise and EqVal_N from s4.2)
         trans → EqVal (app M[σ] N[σ]) (app M[σ'] N[σ']) at B[⇑σ][N[σ]..] (wt_e_sup_t_sup)
       Then upEqVal → restrictEqVal → downEqVal to reach WT1.                *)
    have conv_NN' : conv Δ N[σ] N[σ'] A[σ]
      by eapply subst_conv_cross; eauto.
    (* Step 1: paeqv_fun at (u_arg, e_sup, t_sup, ..., N[σ]). *)
    specialize (paeqv_fun u_arg e_sup t_sup Vu_arg APP_g_big_arg NBe_sup
                          APP_f_pi_arg N[σ] TD Val_N).
    (* paeqv_fun : EqVal Δ (app M[σ] N[σ]) (app M[σ'] N[σ]) B[⇑σ][N[σ]..]
                          (wt_abs_inv2 ...). *)
    rewrite subst_comm in paeqv_fun.
    erewrite (wt_unique _ WT_e_sup_t_sup) in paeqv_fun.
    (* Step 2: pae_fun_σ' at (u_arg, e_sup, t_sup, ..., N[σ], N[σ'], conv, EqVal). *)
    specialize (pae_fun_σ' u_arg e_sup t_sup Vu_arg APP_g_big_arg NBe_sup
                            APP_f_pi_arg N[σ] N[σ'] conv_NN' EqVal_N).
    (* pae_fun_σ' : EqVal Δ (app M[σ'] N[σ]) (app M[σ'] N[σ']) B[⇑σ][N[σ]..]
                          (wt_abs_inv2 ...). *)
    rewrite subst_comm in pae_fun_σ'.
    erewrite (wt_unique _ WT_e_sup_t_sup) in pae_fun_σ'.
    (* EqVal_trans: combine. *)
    have EqVal_esup_t_sup : EqVal Δ (Core.app M[σ] N[σ]) (Core.app M[σ'] N[σ']) B[N..][σ] WT_e_sup_t_sup
      by eapply EqVal_trans; [exact paeqv_fun | exact pae_fun_σ'].

    move: (@upEqVal _ Δ _ _ _ _ _ _ WT_e_sup_t_sup WT_e_sup_c
                WT_t_sup_univ WT_c_univ le_t_sup_c EqVal_esup_t_sup VT_c)
      => EqVal_esup_c.
    have EqVal_u1_c
      := @restrictEqVal _ Δ _ _ _ _ _ _ WT_u1_c WT_e_sup_c
                         le_u1_e_sup EqVal_esup_c.

    split.
    + (* Val Δ (app M[σ] N[σ]) B[N..][σ] WT1 — final downVal. *)
      exact (@downVal _ Δ _ _ _ _ _ WT1 WT_u1_c le_a1_c Val_u1_c).
    + (* EqVal Δ (app M[σ] N[σ]) (app M[σ'] N[σ']) B[N..][σ] WT1 — final downEqVal. *)
      exact (@downEqVal _ Δ _ _ _ _ _ _ WT1 WT_u1_c le_a1_c EqVal_u1_c).
Qed.

(* t_nat: ctx Γ ⟹ tnat : tuniv 0 *)
Lemma st_nat :
  ctx Γ ->
(* ------------------------- *)
  semantic_typing Γ Core.tnat Core.tuniv.
Proof.
  move=> _ ρ m Δ σ σ' TS TS' CS FR VS CD u a WT EM EA.
  asimpl.
  split; [|admit].
  destruct u; cbn in EM; try done.
  - apply Val_Bot.
  - (* u = tnat *)
    destruct a; cbn in EA; try done.
    + (* a = bot: wt tnat bot impossible *) inversion WT.
    + (* a = tuniv n0; le (tuniv n0) (tuniv 0) ⟹ n0 = 0 *)
      dependent destruction WT. done.
Admitted.

(* t_zero: ctx Γ ⟹ zero : tnat *)
Lemma st_zero :
  ctx Γ ->
(* ------------------------- *)
  semantic_typing Γ Core.zero Core.tnat.
Proof.
  move=> _ ρ m Δ σ σ' TS TS' CS FR VS CD u a WT EM EA.
  asimpl.
  split; [|admit].
  destruct u; cbn in EM; try done.
  - apply Val_Bot.
  - (* u = zero *)
    destruct a; cbn in EA; try done.
    + (* a = bot: wt zero bot impossible *) inversion WT.
    + (* a = tnat *)
      dependent destruction WT.
      cbn. exact ms_refl.
Admitted.

(* t_succ: M : tnat ⟹ succ M : tnat *)
Lemma st_succ M :
  typing Γ M Core.tnat ->
  semantic_typing Γ M Core.tnat ->
(* ------------------------- *)
  semantic_typing Γ (Core.succ M) Core.tnat.
Proof.
  move=> T1 ST ρ m Δ σ σ' TS TS' CS FR VS CD u a WT EM EA.
  asimpl.
  have VSl : ValSub Δ Γ σ ρ by exact (EqValSub_ValSub_left VS).
  split; [|admit].
  destruct (Raw.is_bot u) eqn:HU.
  { destruct u; try done. apply Val_Bot. }
  cbn in EM. rewrite HU in EM.
  move: EM => [Vu [a' [LEs EMa]]].
  destruct u as [| | | | | |]; cbn in HU; try done.
  destruct a; cbn in EA; try done.
  - (* a = bot: wt (succ v0) bot impossible *) inversion WT.
  - (* a = tnat *)
    dependent destruction WT.
    cbn.
    exists M[σ]. split; first by apply ms_refl.
    rewrite le_succ in LEs.
    have EvM_v : EvalRel M ρ u.
    { eapply EvalRel_down with (u := a'); eauto.
      apply fits_valid_env in FR. exact FR. }
    have EvT : EvalRel Core.tnat ρ tnat by [].
    move: (ST ρ m Δ σ σ TS TS (ConvSub_refl TS) FR (ValSub_EqValSub VSl) CD u tnat WT EvM_v EvT) => [val_M _].
    exact val_M.
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
  (* Following Adequacy2.agda's adequacySub2-Pi (lines 711-741):
     given EvalRel (Pi A B) ρ (tpi b f) and a wt witness wt_tpi ...,
     build ValTy at (tpi b f) by:
       - taking A0 := A[σ], B0 := B[⇑σ], HeadRed by reflexivity,
       - using s1 for the domain ValTy,
       - building PiEdgeVal via per-edge s2 application,
       - building PiEdgeEq similarly.                     *)
  move=> T1 T2 s1 s2.
  move=> ρ m Δ σ σ' TS TS' CS FR VS CD u_sem a_sem WT EvA1 EvA2.
  asimpl.
  cbn in EvA1, EvA2.
  have VSl : ValSub Δ Γ σ ρ by exact (EqValSub_ValSub_left VS).
  split; [|admit].
  dependent destruction WT.
  - (* wt_bot: u_sem = bot. *)
    apply Val_Bot.
  - (* wt_tuniv: EvA1 forces u_sem = tpi, but here u_sem = tuniv. *) done.
  - (* wt_tnat *) done.
  - (* wt_zero: a_sem = tnat, but our goal is at tuniv. Contradiction via EvA2. *)
    (* Wait — wt_zero gives a_sem = tnat, not tuniv. So this isn't the right case. *)
    done.
  - (* wt_succ *) done.
  - (* wt_tpi: main case.  Names after destruction:
       a (dom), g (codom fn = f),
       WT (the wt a tuniv arg), w (the dom forall), w0 (the codom forall),
       i (valid (tpi a g)).                                            *)
    rename a into b_dom, g into f_codom, w into w_dom, w0 into w_codom,
           i into V_tpi.
    (* EvA1 : EvalRel (Core.tpi A B) ρ (tpi b_dom f_codom). *)
    destruct EvA1 as [V_b [V_f [evA_b [a' [evA_a' body_pi]]]]].
    have Vρ : valid_env ρ by eauto with valid.
    (* Substitution typings. *)
    have TD_A : typing Δ A[σ] Core.tuniv.
    { have h := @substitution_tm _ Γ A Core.tuniv _ Δ σ T1 TS CD. exact h. }
    have ctx_ΔA : ctx (Δ ++ A[σ])
      by eapply c_cons; eauto.
    have TD_B : typing (Δ ++ A[σ]) B[⇑σ] Core.tuniv.
    { have TS_lift : typing_subst (Δ ++ A[σ]) (⇑σ) (Γ ++ A)
        by exact (@typing_subst_lift _ Δ _ σ Γ A ctx_ΔA TS).
      have h := @substitution_tm _ (Γ ++ A) B Core.tuniv _ (Δ ++ A[σ]) (⇑σ)
                  T2 TS_lift ctx_ΔA. exact h. }
    (* Goal: Val Δ (Core.tpi A[σ] B[⇑σ]) Core.tuniv (wt_tpi ...).
       Unfolds via Val (a = tuniv) to ValTy, then via ValTy (u = tpi)
       to the existential structure. *)
    cbn.
    exists A[σ], B[⇑σ].
    split; [eapply ms_refl; eauto|].
    split; [exact TD_A|].
    split; [exact TD_B|].
    split; [exact V_tpi|].
    split; [|split].
    { (* Val Δ A[σ] Core.tuniv (wt_tpi_dom (wt_tpi ...)) — domain ValTy. *)
      have evU_b : EvalRel Core.tuniv ρ tuniv by [].
      move: (s1 ρ m Δ σ σ TS TS (ConvSub_refl TS) FR (ValSub_EqValSub VSl) CD b_dom tuniv
               (wt_tpi_dom (wt_tpi WT w_dom w_codom V_tpi)) evA_b evU_b) => [v _].
      exact v. }
    + (* PiEdgeVal: forall u v Vu APP NB WTu N typing-N Val-N,
           ValTy Δ B[N..] (wt_tpi_inv2 (wt_tpi ...) Vu APP NB). *)
      intros u v_codom Vu APPfc NBv WTu_dom N TN VN.
      (* Apply s2 at extended env (u .: ρ). *)
      (* Find x via body_pi to get EvalRel B (x .: ρ) v_codom. *)
      destruct (body_pi u v_codom Vu APPfc) as [x [wtx [Lex evB_x_v]]].
      have Vx : valid x by eapply wt_valid_tm; eauto.
      have Vρext_x : valid_env (x .: ρ) by eapply valid_cons; eauto.
      have Vρext_u : valid_env (u .: ρ) by eapply valid_cons; eauto.
      have evB_u : EvalRel B (u .: ρ) v_codom.
      { eapply EvalRel_mono_env; first exact evB_x_v.
        - exact Vρext_x.
        - exact Vρext_u.
        - move=> [j|]; cbn; auto using le_refl.
          apply le_refl, Vρ. }
      have TS_ext : typing_subst Δ (N .: σ) (Γ ++ A)
        by eapply typing_subst_cons; eauto.
      have FR_ext : fits (Γ ++ A) (u .: ρ).
      { eapply fits_cons; first exact T1.
        - exact evA_b.
        - exact WT.
        - exact WTu_dom.
        - exact FR. }
      have VS_ext : ValSub Δ (Γ ++ A) (N .: σ) (u .: ρ).
      { eapply ValSub_cons; [|exact VSl].
        intros uu Vuu Leu aa hwtu ERAu.
        (* Same compatibility issue as in st_abs / st_app's VT_c.
           Admitted. *)
        admit. }
      have evU : EvalRel Core.tuniv (u .: ρ) tuniv by [].
      have [h_val _] := s2 (u .: ρ) m Δ (N .: σ) (N .: σ) TS_ext TS_ext
                       (ConvSub_refl TS_ext) FR_ext
                       (ValSub_EqValSub VS_ext) CD _ _
                       (wt_tpi_inv2 (wt_tpi WT w_dom w_codom V_tpi) Vu APPfc NBv)
                       evB_u evU.
      (* h_val : Val Δ B[N .: σ] Core.tuniv (wt_tpi_inv2 ...)
         Goal  : ValTy Δ B[N..] (wt_tpi_inv2 ...)
                 = Val Δ B[N..] Core.tuniv (wt_tpi_inv2 ...). *)
      apply Val_ValTy.
      asimpl in h_val.
      (* Bridge B[N .: σ] = B[⇑σ][N..] via substitution composition
         (same pattern as st_abs's eq_M).  The witness wt_tpi_inv2 (wt_tpi ...)
         from the s2 call may also differ from the goal's witness; bridge via
         wt_unique when needed.  Admitted for now. *)
      admit.
    + (* PiEdgeEq: similar to PiEdgeVal but for EqVal.  Same structure;
         admitted for now. *)
      admit.
Admitted.

Lemma st_univ :
  ctx Γ ->
(* ------------------------- *)
  semantic_typing Γ Core.tuniv Core.tuniv.
Proof.
  move=> _ ρ m Δ σ σ' TS TS' CS FR VS CD u a WT EM EA.
  asimpl.
  split; [|admit].
  destruct u; cbn in EM; try done.
  - apply Val_Bot.
  - (* u = tuniv n0; le (tuniv n0) (tuniv i) ⟹ n0 = i *)
    destruct a; cbn in EA; try done.
    + (* a = bot: wt (tuniv n0) bot impossible *) inversion WT.
    + (* a = tuniv n1; le (tuniv n1) (tuniv j) ⟹ n1 = j *)
      dependent destruction WT.
      cbn. done.
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
  move=> T1 h_typ.
  move=> ρ m Δ σ1 σ2 TS1 TS2 CS FR VS_eq CD u a WT EM EA.
  (* Step 1: get Val and EqVal at (σ1, σ2) from h_typ. *)
  have VS1 : ValSub Δ Γ σ1 ρ by exact (EqValSub_ValSub_left VS_eq).
  move: (h_typ ρ m Δ σ1 σ1 TS1 TS1 (ConvSub_refl TS1) FR (ValSub_EqValSub VS1) CD u a WT EM EA)
    => [val_M _].
  move: (h_typ ρ m Δ σ1 σ2 TS1 TS2 CS FR VS_eq CD u a WT EM EA)
    => [_ eq_M].
  split.
  - (* EqVal Δ M[σ1] M[σ1] A[σ1] WT — diagonal via Val_EqVal. *)
    apply Val_EqVal. exact val_M.
  - (* EqVal Δ M[σ1] M[σ2] A[σ1] WT — directly from h_typ at (σ1, σ2). *)
    exact eq_M.
Qed.

(* c_sym: M ≡ N : A ⟹ N ≡ M : A *)
Lemma sc_sym M N A :
  conv Γ M N A ->
  semantic_conv2 Γ M N A ->
(* ------------------------- *)
  semantic_conv2 Γ N M A.
Proof.
  (* Following Adequacy2.agda's conv-sym (lines 610-615):
       huN  = convSound-inv d → bridge EvalRel N ρ u to EvalRel M ρ u
       eq   = adequacyEqSub2 d ... huN → EqVal M[σ] N[σ] A[σ] WT
       result = EqVal2-sym eq → EqVal N[σ] M[σ] A[σ] WT
     Coq counterparts:
       conv_EvalRel CN's bwd direction ≈ convSound-inv
       hMN ≈ adequacyEqSub2 d
       EqVal_sym ≈ EqVal2-sym
     In Agda a single σ is used everywhere so swap is trivial.  Coq's
     semantic_conv2 carries (σ1, σ2) potentially different, which makes
     swapping require a σ1↔σ2 bridge on the type substitution. *)
  move=> CN hMN.
  move=> ρ m Δ σ1 σ2 TS1 TS2 CS FR VS_eq CD u a WT EN EA.
  (* Step 1: bridge EvalRel N ρ u → EvalRel M ρ u via conv_EvalRel's bwd. *)
  move: (conv_EvalRel CN FR) => [_ [_ [_ bwd]]].
  have EM : EvalRel M ρ u by apply bwd; exact EN.
  (* Step 2: apply hMN to get EqVal pair (M[σ1] N[σ1] and M[σ1] N[σ2]) at A[σ1]. *)
  move: (hMN ρ m Δ σ1 σ2 TS1 TS2 CS FR VS_eq CD u a WT EM EA) => [eq_MN_diag eq_MN_off].
  split.
  - (* EqVal Δ N[σ1] M[σ1] A[σ1] WT *)
    eapply EqVal_sym. exact eq_MN_diag.
  - (* EqVal Δ N[σ1] M[σ2] A[σ1] WT — σ1/σ2 crossed.  Requires bridging M[σ1]↔M[σ2]
       via the FTLR for the M-side, currently not directly derivable. *)
    admit.
Admitted.

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
  (* Following Adequacy2.agda's adequacyEqSub2-App-fun(-core) (lines 1789-...).
     Variable naming follows st_app, with Val replaced by EqVal at appropriate
     points and the function-typing hypothesis replaced by conv_EvalRel/scN.
     Agda → Coq:
       dB, dff', da     ↦ T2, CN, T4
       semantic_typings ↦ s1, s2, scN, s4
       v0, evA_v0       ↦ v0, evA_v0
       evF_sing         ↦ evF_sing (EvalRel N ρ singleton)
       typed_f          ↦ via conv_EvalRel CN's InvConv.InvTyped_N
       u_big, a_pi      ↦ u_big, a_pi
       g_big, b_pi, f_pi ↦ post-destruct names
       paeqv_fun        ↦ paeqv_fun (PiAppEqVal extracted from EqVal) *)
  move=> T1 T2 CN T4 s1 s2 scN s4.
  move=> ρ m Δ σ1 σ2 TS1 TS2 CS FR VS_eq CD u1 a1 WT1 Ex ER.
  have VSl : ValSub Δ Γ σ1 ρ by exact (EqValSub_ValSub_left VS_eq).
  specialize (s1 ρ m Δ σ1 σ1 TS1 TS1 (ConvSub_refl TS1) FR (ValSub_EqValSub VSl) CD).
  specialize (s4 ρ m Δ σ1 σ1 TS1 TS1 (ConvSub_refl TS1) FR (ValSub_EqValSub VSl) CD).
  specialize (scN ρ m Δ σ1 σ2 TS1 TS2 CS FR VS_eq CD).
  split; [|admit].
  cbn in Ex.
  destruct (Raw.is_bot u1) eqn:HB.
  - (* EvalRel (app N M) is bot *)
    destruct u1; try done.
    dependent destruction WT1. cbn.
    destruct a; try done.
  -
    have TD : typing Δ M[σ1] A[σ1].
    { eapply (substitution_tm); eauto. }

    move: Ex => [v0 [evF_sing evA_v0]].

    (* Typed enlargement of N via conv_EvalRel CN's InvConv. *)
    move: (conv_EvalRel CN FR) => [InvTypN [_ [_ _]]].
    unfold InvTyped in InvTypN.
    move: (InvTypN _ evF_sing) =>
      [u_big [a_pi [wt_big [le_sing [evF_big evPi]]]]].
    clear InvTypN.
    unfold singleton in le_sing. rewrite HB in le_sing.
    destruct u_big as [| | | | | | g_big]; try done.
    inversion wt_big. subst.
    rewrite le_abs in le_sing.
    cbn in le_sing.
    destruct (app g_big v0) eqn:APP_g_big_v0; try done.
    rewrite Bool.andb_true_r in le_sing.

    have Vg_big : valid_fun g_big by eauto with valid.
    have Vu1 : valid u1 by eapply wt_valid_tm; eauto.
    have Vv0 : valid v0 by eapply EvalRel_valid; eauto.

    (* Typed enlargement of M via T4. *)
    move: (typing_EvalRel T4 FR) => typed_a.
    move: (typed_a _ evA_v0) =>
      [u_arg [t_arg [wt_arg [le_arg [evA_arg evT_arg]]]]].
    clear typed_a.
    have Vu_arg : valid u_arg by eauto with valid.

    destruct (valid_app_exists Vg_big Vu_arg) as [e_sup [APP_g_big_arg Ve_sup]].
    move: (le_valid_compatible Vu_arg le_arg) => C_arg.
    move: (le_fun_mono_arg Vg_big Vv0 Vu_arg C_arg le_arg APP_g_big_v0 APP_g_big_arg)
      => [_ le_e_sup].

    have Vf_pi : valid_fun g by eauto with valid.
    destruct (valid_app_exists Vf_pi Vu_arg) as [t_sup [APP_f_pi_arg Vt_sup]].
    destruct (valid_app_exists Vf_pi Vv0) as [t_sup_v0 [APP_f_pi_v0 Vt_sup_v0]].
    move: (le_fun_mono_arg Vf_pi Vv0 Vu_arg C_arg le_arg
             APP_f_pi_v0 APP_f_pi_arg) => [_ le_t_sup].

    (* Apply scN (semantic_conv2 of N N') at the big witness — project diagonal. *)
    move: (scN _ _ wt_big evF_big evPi) => [scN_diag _].
    asimpl in scN_diag.
    dependent destruction wt_big.
    cbn in scN_diag.
    (* EqVal at (abs g_big, tpi b f) = ValTy /\ ValPi(M) /\ ValPi(N) /\ EqValPi. *)
    move: scN_diag => [vt_pi [vpi_N [vpi_N' eqvpi_fun]]].
    dependent destruction wt_big.
    apply ValTy_Val in vt_pi.
    cbn in vt_pi.
    destruct vt_pi as (A_pi & B_pi & red_pi & _ & _ & _ & vA_pi & piEV & piEE).
    unfold Rec.EqValPi in eqvpi_fun.
    destruct eqvpi_fun as (A0 & B0 & red_fun & paeqv_fun).
    have red_refl : HeadRed (Core.tpi A[σ1] B[⇑ (σ1)]) (Core.tpi A[σ1] B[⇑ (σ1)])
      by eapply ms_refl; eauto.
    move: (HeadRed_tpi_det red_fun red_refl) => [eqA_self eqB_self].
    move: (HeadRed_tpi_det red_fun red_pi)   => [eqA_pi   eqB_pi].
    subst.

    have NBu1 : ~ is_bot u1.
    { apply EvalRel_valid in evF_sing. unfold singleton in evF_sing.
      rewrite HB in evF_sing. cbn in evF_sing.
      destruct u1; try done. }
    have NBe   : ~ is_bot e by destruct u1; destruct e; try done.
    have Ve : valid e
      by eapply (@valid_app g_big v0); eauto.
    have le_u1_e_sup : le u1 e_sup
      by exact (le_trans Vu1 Ve Ve_sup le_sing le_e_sup).
    have NBe_sup : ~ is_bot e_sup.
    { destruct e_sup; try done; intro Hb;
        apply le_bot_inv in le_u1_e_sup; subst u1; done. }

    have evPi_copy : EvalRel (Core.tpi A B) ρ (tpi a g) by exact evPi.
    cbn in evPi.
    move: evPi => [_ [_ [evA_a _]]].

    (* Apply paeqv_fun (PiAppEqVal) at (u_arg, e_sup, t_sup) and M[σ1]. *)
    specialize (paeqv_fun u_arg e_sup t_sup Vu_arg APP_g_big_arg NBe_sup
                          APP_f_pi_arg M[σ1] TD).

    (* Discharge the Val premise via s4 (semantic_typing of M). *)
    have WT_u_arg_a : wt u_arg a
      := w u_arg e_sup Vu_arg APP_g_big_arg NBe_sup.
    move: (s4 u_arg a WT_u_arg_a evA_arg evA_a) => [Val_M _].
    erewrite (wt_unique WT_u_arg_a) in Val_M.
    specialize (paeqv_fun Val_M).

    (* Bridge B[⇑σ1][M[σ1]..] = B[M..][σ1]. *)
    have subst_comm : B[⇑ σ1][M[σ1]..] = B[M..][σ1].
    { asimpl. f_equal. apply functional_extensionality => -[j|] //=.
      change (subst_Tm (M[σ1] .: var) ((σ1 j)⟨↑⟩) = σ1 j).
      rewrite renSubst_Tm. exact: instId'_Tm. }
    rewrite subst_comm in paeqv_fun.

    have Vρ : valid_env ρ by eauto with valid.
    have WT_e_sup_t_sup : wt e_sup t_sup
      := w0 u_arg e_sup t_sup Vu_arg APP_g_big_arg NBe_sup APP_f_pi_arg.
    have NBt_sup : ~ is_bot t_sup.
    { destruct t_sup; try done; intro Hbt;
        apply wt_bot_inv in WT_e_sup_t_sup; subst e_sup; done. }
    have evB_t_sup : EvalRel B[M..] ρ t_sup
      by eapply EvalRel_Pi_app_type;
         [ exact evPi_copy | exact Vρ | exact Vu_arg
         | exact APP_f_pi_arg | exact NBt_sup | exact evA_arg ].

    have C_a1_t_sup : compatible a1 t_sup
      by eapply EvalRel_app_Comp; eauto.

    have WT_t_sup_univ : wt t_sup tuniv
      := w2 u_arg t_sup Vu_arg APP_f_pi_arg NBt_sup.
    have WT_a1_univ   : wt a1 tuniv by eapply wt_ty_tuniv; exact WT1.

    (* Transport EqVal (e_sup, t_sup) → (u1, a1) via Sup. *)
    destruct (compatible_lub_exists C_a1_t_sup) as [c LUB_c].
    have Va1 : valid a1 by eauto with valid.
    have Vt_sup_v : valid t_sup by eauto with valid.
    have Vc : valid c by exact (valid_lub Va1 Vt_sup_v LUB_c).
    have WT_c_univ : wt c tuniv
      by eapply wt_lub; [exact WT_a1_univ | exact WT_t_sup_univ | exact LUB_c].
    have le_a1_c : le a1 c
      by eapply le_lub_left; eauto.
    have le_t_sup_c : le t_sup c
      by eapply le_lub_right; eauto.
    have WT_u1_c : wt u1 c
      by eapply wt_le; [exact WT1 | exact le_a1_c | exact WT_a1_univ | exact WT_c_univ].
    have WT_e_sup_c : wt e_sup c
      by eapply wt_le;
         [exact WT_e_sup_t_sup | exact le_t_sup_c | exact WT_t_sup_univ | exact WT_c_univ].

    have eq_subst : B[M .: var][σ1] = B[M[σ1] .: σ1].
    { auto_unfold. rewrite substSubst_Tm. f_equal.
      apply functional_extensionality => -[j|] //=. }

    (* Build Val Δ B[M..][σ1] tuniv (wt_c_univ) — same as VT_c in st_app. *)
    have VT_c : Val Δ B[M..][σ1] Core.tuniv WT_c_univ.
    { have evB_c : EvalRel B[M..] ρ c
        by eapply EvalRel_sup with (u := a1) (u' := t_sup); eauto.
      destruct (EvalRel_subst1_forward Vρ evB_c) as [v_fwd [evN_vfwd evB_vfwd_c]].
      have Vv_fwd : valid v_fwd by eapply EvalRel_valid; eauto.
      move: (typing_EvalRel T4 FR) => typedN.
      destruct (typedN _ evN_vfwd) as [u' [t' [wt_u' [Le_vu' [evN_u' evA_t']]]]].
      clear typedN.
      have Vu' : valid u' by eapply wt_valid_tm; eauto.
      have Vt' : valid t' by eauto with valid.
      have WTt'_univ : wt t' tuniv by eapply wt_ty_tuniv; exact wt_u'.
      have Vρext : valid_env (v_fwd .: ρ) by eapply valid_cons; eauto.
      have Vρext' : valid_env (u' .: ρ) by eapply valid_cons; eauto.
      have evB_u'_c : EvalRel B (u' .: ρ) c.
      { eapply EvalRel_mono_env; first exact evB_vfwd_c.
        - exact Vρext.
        - exact Vρext'.
        - move=> [j|]; cbn; auto using le_refl.
          apply le_refl, Vρ. }
      have TS' : typing_subst Δ (M[σ1] .: σ1) (Γ ++ A)
        by eapply typing_subst_cons; eauto.
      have FR' : fits (Γ ++ A) (u' .: ρ)
        by eapply fits_cons; eauto.
      have VS' : ValSub Δ (Γ ++ A) (M[σ1] .: σ1) (u' .: ρ).
      { eapply ValSub_cons; [|exact VSl].
        intros uu Vuu Leu aa hwtu ERAu.
        have ERN_uu : EvalRel M ρ uu by eapply EvalRel_down; eauto.
        destruct (s4 uu aa hwtu ERN_uu ERAu) as [v _]; exact v. }
      have evU : EvalRel Core.tuniv (u' .: ρ) tuniv by [].
      move: (s2 (u' .: ρ) m Δ (M[σ1] .: σ1) (M[σ1] .: σ1) TS' TS'
                (ConvSub_refl TS') FR'
                (ValSub_EqValSub VS') CD c tuniv WT_c_univ evB_u'_c evU)
        => [h_val _].
      asimpl in h_val.
      auto_unfold in *. rewrite eq_subst. exact h_val. }

    (* Bridge paeqv_fun's witness to WT_e_sup_t_sup. *)
    erewrite (wt_unique _ WT_e_sup_t_sup) in paeqv_fun.

    (* upEqVal: EqVal (e_sup, t_sup) → EqVal (e_sup, c). *)
    move: (@upEqVal _ Δ _ _ _ _ _ _ WT_e_sup_t_sup WT_e_sup_c
                    WT_t_sup_univ WT_c_univ le_t_sup_c paeqv_fun VT_c) => EqVal_esup_c.

    (* restrictEqVal: EqVal (e_sup, c) → EqVal (u1, c). *)
    have EqVal_u1_c
      := @restrictEqVal _ Δ _ _ _ _ _ _ WT_u1_c WT_e_sup_c
                         le_u1_e_sup EqVal_esup_c.

    (* downEqVal: EqVal (u1, c) → EqVal (u1, a1). With diagonal scN projection,
       paeqv_fun produces EqVal (app N[σ1] M[σ1]) (app N'[σ1] M[σ1]) — both
       sides at σ1 — matching the diagonal goal. *)
    asimpl.
    exact (@downEqVal _ Δ _ _ _ _ _ _ WT1 WT_u1_c le_a1_c EqVal_u1_c).
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
  (* Following Adequacy2.agda's adequacyEqSub2-App-arg(-core) (lines 1983-2200).
     Variable naming follows st_app/sc_app1.  Differences from sc_app1:
       - N is typed (not conv'd) — use sN to get Val of N[σ1] at (tpi A B)[σ1].
       - M is conv'd to M' — use scM to get EqVal of M[σ1] M'[σ2] at A[σ1].
       - Result is EqVal of (app N M)[σ1] (app N M')[σ2] at (B[M..])[σ1].
     The combining step needs PiAppEq (one function applied to two conv'd
     args), which is defined in Rec but not exposed by the Val structure
     of N at (tpi b_pi f_pi).  Bridging requires either:
       (a) An ad-hoc derivation of PiAppEq from PiAppVal + conv, or
       (b) Combining two PiAppVal applications (for M and M') via a separate
           Val→EqVal step.
     Either route is structural work not currently provided by the Val
     fixpoint.  Below we set up the typed-enlargement scaffold and admit
     at the combining step. *)
  move=> T1 T2 T3 CM s1 s2 sN scM.
  move=> ρ m Δ σ1 σ2 TS1 TS2 CS FR VS_eq CD u1 a1 WT1 Ex ER.
  have VS1 : ValSub Δ Γ σ1 ρ by exact (EqValSub_ValSub_left VS_eq).
  specialize (s1 ρ m Δ σ1 σ1 TS1 TS1 (ConvSub_refl TS1) FR (ValSub_EqValSub VS1) CD).
  specialize (sN ρ m Δ σ1 σ1 TS1 TS1 (ConvSub_refl TS1) FR (ValSub_EqValSub VS1) CD).
  specialize (scM ρ m Δ σ1 σ2 TS1 TS2 CS FR VS_eq CD).
  split; [|admit].
  cbn in Ex.
  destruct (Raw.is_bot u1) eqn:HB.
  - (* EvalRel (app N M) is bot — EqVal_Bot. *)
    destruct u1; try done.
    dependent destruction WT1. cbn.
    destruct a; try done.
  -
    (* For PiAppEq-style use, we would need typing of M[σ1] at A[σ1].
       The hypothesis CM : conv Γ M M' A only gives conv, not direct typing.
       This is the structural mismatch with PiAppVal's typing premise. *)
    move: Ex => [v0 [evF_sing evA_v0]].
    (* Typed enlargement of N via T3 (typing Γ N (tpi A B)). *)
    move: (typing_EvalRel T3 FR) => typed_f.
    unfold InvTyped in typed_f.
    move: (typed_f _ evF_sing) =>
      [u_big [a_pi [wt_big [le_sing [evF_big evPi]]]]].
    clear typed_f.
    unfold singleton in le_sing. rewrite HB in le_sing.
    destruct u_big as [| | | | | | g_big]; try done.
    inversion wt_big. subst.
    rewrite le_abs in le_sing.
    cbn in le_sing.
    destruct (app g_big v0) eqn:APP_g_big_v0; try done.
    rewrite Bool.andb_true_r in le_sing.

    have Vg_big : valid_fun g_big by eauto with valid.
    have Vu1 : valid u1 by eapply wt_valid_tm; eauto.
    have Vv0 : valid v0 by eapply EvalRel_valid; eauto.

    (* Typed enlargement of M via conv_EvalRel CM (using forward direction
       on InvConv). *)
    move: (conv_EvalRel CM FR) => [InvTypM [InvTypM' _]].
    move: (InvTypM _ evA_v0) =>
      [u_arg [t_arg [wt_arg [le_arg [evA_arg evT_arg]]]]].
    clear InvTypM.
    have Vu_arg : valid u_arg by eauto with valid.

    destruct (valid_app_exists Vg_big Vu_arg) as [e_sup [APP_g_big_arg Ve_sup]].
    move: (le_valid_compatible Vu_arg le_arg) => C_arg.
    move: (le_fun_mono_arg Vg_big Vv0 Vu_arg C_arg le_arg APP_g_big_v0 APP_g_big_arg)
      => [_ le_e_sup].

    have Vf_pi : valid_fun g by eauto with valid.
    destruct (valid_app_exists Vf_pi Vu_arg) as [t_sup [APP_f_pi_arg Vt_sup]].
    destruct (valid_app_exists Vf_pi Vv0) as [t_sup_v0 [APP_f_pi_v0 Vt_sup_v0]].
    move: (le_fun_mono_arg Vf_pi Vv0 Vu_arg C_arg le_arg
             APP_f_pi_v0 APP_f_pi_arg) => [_ le_t_sup].

    (* Apply sN (semantic_typing of N) at the big witness — project Val. *)
    move: (sN _ _ wt_big evF_big evPi) => [sNval _].
    asimpl in sNval.
    dependent destruction wt_big.
    cbn in sNval.
    move: sNval => [vt_pi vpi_fun].
    dependent destruction wt_big.
    apply ValTy_Val in vt_pi.
    cbn in vt_pi.
    destruct vt_pi as (A_pi & B_pi & red_pi & _ & _ & _ & vA_pi & piEV & piEE).
    unfold Rec.ValPi in vpi_fun.
    destruct vpi_fun as (A0 & B0 & red_fun & pav_fun & pae_fun).
    have red_refl : HeadRed (Core.tpi A[σ1] B[⇑ (σ1)]) (Core.tpi A[σ1] B[⇑ (σ1)])
      by eapply ms_refl; eauto.
    move: (HeadRed_tpi_det red_fun red_refl) => [eqA_self eqB_self].
    move: (HeadRed_tpi_det red_fun red_pi)   => [eqA_pi   eqB_pi].
    subst.

    (* From here, combining requires PiAppEq (one function, two conv'd args).
       The Val structure of N only exposes PiAppVal.  To finish:
         - Apply pav_fun with M[σ1]'s Val to get Val of (app N[σ1] M[σ1]).
         - Apply pav_fun (transported through CM) with M'[σ2]'s Val to get
           Val of (app N[σ1] M'[σ2]).
         - Combine via the EqVal-of-arg (from scM) into the desired EqVal
           of (app N[σ1] M[σ1]) (app N[σ1] M'[σ2]).
       The combining step has no direct support in the current Val/EqVal
       structure and requires adding a "PiAppEq-from-Val+conv" lemma.
       Admitted. *)
    admit.
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
  dependent destruction h.
  cbn.
  destruct a; done.
Qed.


Lemma EqValSub_id n (Γ:Ctx n) :
  EqValSub Γ Γ var var bot_env.
Proof.
  unfold EqValSub.
  move=> i u Vu LE a ER h.
  unfold bot_env in LE.
  apply le_bot_inv in LE. subst.
  dependent destruction h.
  cbn.
  destruct a; done.
Qed.

(* evalRel_Pi_trivial: every Pi type evaluates to (tpi bot nil).
   Mirrors evalRel-Pi-trivial in PiInjectivity.agda. *)
Lemma evalRel_Pi_trivial {n} (A : Tm n) (B : Tm (S n)) (ρ : Env n) :
  EvalRel (Core.tpi A B) ρ (tpi bot nil).
Proof.
  cbn.
  split; first by [].                      (* valid bot *)
  split; first by [].                      (* valid_fun nil *)
  split.                                    
  apply EvalRel_bot.
  exists bot.
  split.
  apply EvalRel_bot. 
  move=> u v IN APP. 
  exists bot. split.
  eapply wt_bot. eapply wt_bot. eapply wt_tuniv.
  split.
  rewrite le_bot. done.
  cbn in APP. inversion APP.
  apply EvalRel_bot.
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
  move=> Cv.
  pose ρ : Env n := bot_env.
  pose σ : Sub n n := var.
  have CΓ : ctx Γ. 
  { eapply conv_ctx; eauto. } 
  have Fρ  : fits Γ ρ.
  { eapply fits_bot_env. eapply CΓ. }
  have TSσ : typing_subst Γ σ Γ.
  { apply typing_subst_id. eauto. }
  have VSσ : ValSub Γ Γ σ ρ.
  { eapply ValSub_id. }
  have EVSσ: EqValSub Γ Γ σ σ ρ.
  { eapply EqValSub_id. } 

  (* Pick the witness u = (tpi bot nil) at type (tuniv i). *)
  pose u := tpi bot nil.
  have Vpi : valid (tpi bot nil) by [].
  have Hwt : wt u (tuniv).
  { rewrite /u. apply: (@wt_tpi bot nil ).
    - econstructor; eauto. eapply wt_tuniv.
    - move => ui vi Vu APP NB.
      cbn in APP. inversion APP. subst. done.
    - move => ui vi Vu APP NB.
      cbn in APP. inversion APP. subst. done.
    - exact: Vpi. }

  (* EvalRel for (tpi B1 F1) and (transported via conv) for A0. *)
  have EvalPi : EvalRel (Core.tpi B1 F1) ρ u.
  { rewrite /u. exact: evalRel_Pi_trivial. }
  have EvA0 : EvalRel A0 ρ u.
  { have IC : InvConv Γ A0 (Core.tpi B1 F1) Core.tuniv ρ.
    { eapply conv_EvalRel; eauto. }
    move: IC => [_ [_ [_ bwd]]]. apply: bwd. exact: EvalPi. }
  have EvUni : EvalRel Core.tuniv ρ (tuniv).
  { cbn. auto. }

  (* Apply adequacyEqSub2 to the conversion at the chosen witness. *)
  move:
    (@adequacyEqSub _ Γ A0 (Core.tpi B1 F1) Core.tuniv Cv) => ev2.
  unfold semantic_conv2 in ev2.
  specialize (ev2 ρ _ Γ σ σ TSσ TSσ (ConvSub_id CΓ) Fρ EVSσ CΓ
       u tuniv Hwt EvA0 EvUni) as ev2.
  (* ev2 : EqVal Γ A0[σ] (tpi B1 F1)[σ] (tuniv i)[σ] Hwt *)

  asimpl in ev2.

  (* EqVal at (tuniv i) unfolds to (ValTy /\ ValTy /\ EqValTy);
     EqValTy at u = (tpi bot nil) exposes the head reductions and
     the domain/codomain conversions. *)
  dependent destruction Hwt.
  cbn in ev2.

  destruct ev2 as [[_ [_ EQTy]] _].
  cbn in EQTy.
  destruct EQTy as [_ [_ ExA]].
  destruct ExA as [A [B [HRA0 [A' [B' rest]]]]].
  destruct rest as [HRpi [convA [convB _]]].

  (* HRpi : HeadRed (tpi B1 F1) (tpi A' B') — Pi is a head-normal
     form, so A' = B1 and B' = F1 by determinacy. *)
  have [EQ1 EQ2] : A' = B1[σ] /\ B' = F1[⇑σ].
  { eapply HeadRed_tpi_det; first exact: HRpi. exact: ms_refl. }
  subst A' B'.

  exists A, B. repeat split. 
  subst σ. asimpl in HRA0. done.
  subst σ. asimpl in convA. done.
  subst σ. asimpl in convB. done.
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

