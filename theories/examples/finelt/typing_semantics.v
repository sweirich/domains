(** * typing_semantics.v: Typing/conversion soundness for [EvalRel]

    (See [MIN/Model/Soundness.agda] and [MIN/Model/SoundnessLemmas.agda].)

    This file proves that the denotational meaning [EvalRel] respects the
    syntactic typing and conversion judgments — the model's "Theorem 1":
    - [typing_EvalRel] (Agda [theorem1]): a derivation [Γ ⊢ M : A] makes [M]
      *invertibly typed* ([InvTyped]) under any environment that [fits Γ];
    - [conv_EvalRel] (Agda [convSound']): a derivation [Γ ⊢ M ≡ N : A] makes
      [M] and [N] *invertibly convertible* ([InvConv]) — invertibly typed on
      both sides plus mutual approximation.
    They are proven by simultaneous induction on the two judgments.

    The bulk of the file is the supporting inversion lemmas ([InvTyp_Lam],
    [InvTyp_App], [InvTyp_Pi], [InvConv_beta], [InvConv_eta], …) that extract
    the semantic content of each typing/conversion rule. *)

(* See LemmaForTS.agda/TypingSemantics.agda *)

(* Prove that well typed syntax produces well typed interpretations.

   Theorem 1 (typing_EvalRel):
       Γ ⊢ M : A   and forall ρ, Fits Γ ρ  implies InvTyped Γ M A ρ

       i.e. for every u s.t. EvalRel M ρ u, there exist v a such that
       u ≤ v, EvalRel M ρ v, wt v a, and EvalRel A ρ a.

   NOTE: why is InvTyped not the simpler
            exists a, EvalRel A ρ a and wt v a ?

   because, the definition of EvalRel_fun says that for any argument u 
   there is some well-typed x that approximates it that can be added 
   to the body.

         interpretation includes ill-typed fin elts?

   Conversion soundness (conv_EvalRel):
       Γ ⊢ M = N : A   and   Fits Γ ρ
       implies   InvConv Γ M N A ρ
       i.e. InvTyped for both sides plus bidirectional EvalRel.

   This is the Rocq translation of the lemmas in
       agda/domain-semantics/TypingSemantics.agda
       agda/domain-semantics/LemmaForTS.agda

*)

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
Require Import eval_substitution.

Import SyntaxNotations.
Import SubstNotations.
Import typing.Notations.

Open Scope syntax_scope.

Import Raw.

(* =====================================================================
   Part 1: Fits — well-typed finite environments

       ρ fits Γ if for all x : A in Γ we have
                [[A]]ρ in Type and ρ(x) in [[A]]ρ.

   See LemmaForTS.agda Part 1.
   ===================================================================== *)

(** [fits Γ ρ] ([Fits]): the environment [ρ] is well-typed for context [Γ] —
    each [ρ x] is a member of the (evaluated) type of [x] in [Γ].  This is the
    standing hypothesis under which the soundness theorems quantify. *)
Inductive fits : forall {n} (Γ:Ctx n) (ρ : Env n), Prop :=
  | fits_empty : fits ctx_empty null
  | fits_cons n (Γ : Ctx n) A ρ a u :
       typing Γ A Core.tuniv ->
       EvalRel A ρ a ->
       wt a tuniv ->
       wt u a ->
       fits Γ ρ ->
       fits (Γ ++ A) (u .: ρ).

Lemma fits_ctx {n} (Γ : Ctx n)(ρ : Env n) :
  fits Γ ρ -> ctx Γ.
Proof.
  induction 1; eauto using ctx.
Qed.

Lemma scons_inj {A} {u1 u2:A} {n} {ρ1 ρ2 : fin n -> A} :
  (u1 .: ρ1) = (u2 .: ρ2) -> ρ1 = ρ2.
Proof.
  move=> h.
  apply functional_extensionality.
  move=> f.
  have: (u1 .: ρ1) (Some f) = (u2 .: ρ2) (Some f) by rewrite h.
  cbn. by [].
Qed.

Lemma fits_tail {n} (Γ : Ctx n) (ρ : Env n) A u :
  fits (Γ ++ A) (u .: ρ) -> fits Γ ρ.
Proof.
  move=> h. dependent destruction h; eauto.
  move: (scons_inj x) => EQ. subst; auto.
Qed.

Lemma fits_valid_env {n} (Γ : Ctx n)(ρ : Env n) :
  fits Γ ρ -> valid_env ρ.
Proof.
  induction 1.
  - eapply valid_nil.
  - eapply valid_cons; eauto.
    eapply wt_valid_tm; eauto.
Qed.

Hint Resolve fits_valid_env : valid typing.

(* Fits-var: the value at every variable is well-typed
   at the lookup of its type. *)

(** Variable case ([Fits-var]): in a fitting environment each [ρ x] is a
    member of the evaluated type of [x].  This is the semantic content of the
    [ty-var] rule. *)
Lemma fits_var {n} (Γ : Ctx n)(ρ : Env n) :
  fits Γ ρ ->
  forall x,
  exists a (h: wt a tuniv) (h2 : wt (ρ x) a),
    typing Γ (lookup x Γ) Core.tuniv /\
    EvalRel (lookup x Γ) ρ a.
Proof.
  move=> h.
  induction h. done.
  auto_case.
  + destruct (IHh f) as [b [WT1 [WT2 [Ht E]]]].
    exists b. exists WT1. exists WT2.
    repeat split; auto.
    eapply renaming_typing with (A := Core.tuniv);
      eauto with renaming.
    eapply c_cons; eauto using typing_ctx.
    eapply EvalRel_wk; eauto.
  + exists a.
    repeat split; eauto.
    eapply renaming_typing with (A := Core.tuniv);
      eauto with renaming.
    eapply c_cons; eauto using typing_ctx.
    eapply EvalRel_wk; eauto.
Qed.

(* =====================================================================
   Part 2: Named invariants — Typed, InvTyped, InvConv.

   Typed M A ρ u  : there exists v ≥ u with EvalRel M ρ v that has a type:
                    wt v a  and  EvalRel A ρ a.
   InvTyped Γ M A ρ : for every u with EvalRel M ρ u, Typed M A ρ u.
   InvConv  Γ M N A ρ : InvTyped for both sides + bidirectional EvalRel.

   See LemmaForTS.agda Part 2.
   ===================================================================== *)


(** [Typed M A ρ u]: the approximation [u] of [M] is dominated by some
    *well-typed* approximation [v] (with [wt v a] and [a] an approximation of
    the type [A]).  Stated this way — "some larger typed [v]" rather than
    "[u] itself is typed" — because [EvalRel] on functions ranges over
    not-necessarily-typed arguments. *)
Definition Typed {n:nat} (M : Tm n) (A : Tm n) ρ u :=
  exists v , exists a, exists (h : wt v a),
    le u v /\ EvalRel M ρ v /\ EvalRel A ρ a.


(* This is not flexible enough. 
Definition Typed {n:nat} (M : Tm n) (A : Tm n) ρ u :=
  exists a, exists (h : wt u a), EvalRel A ρ a.
*)

(** [InvTyped Γ M A ρ]: *every* approximation of [M] is [Typed].  This is the
    conclusion of typing soundness. *)
Definition InvTyped
  {n:nat} (Γ: Ctx n) (M : Tm n) (A : Tm n) (ρ : Env n) :=
  forall u, EvalRel M ρ u -> Typed M A ρ u.

(** [InvConv Γ M N A ρ]: invertible typing of both [M] and [N], together with
    mutual approximation ([M] and [N] have the same approximations).  This is
    the conclusion of conversion soundness. *)
Definition InvConv
  {n:nat} (Γ: Ctx n) (M : Tm n) (N: Tm n) (A : Tm n) (ρ : Env n) :=
  InvTyped Γ M A ρ
  /\ InvTyped Γ N A ρ
  /\ (forall u, EvalRel M ρ u -> EvalRel N ρ u)
  /\ (forall u, EvalRel N ρ u -> EvalRel M ρ u).


Reserved Notation "Γ ⊨ M ∈ A" (at level 70).
Reserved Notation "Γ ⊨ M ≡ N ∈ A" (at level 70).

Local Notation "Γ ⊨ M ∈ A" := (forall ρ, fits Γ ρ -> InvTyped Γ M A ρ).
Local Notation "Γ ⊨ M ≡ N ∈ A" := (forall ρ, fits Γ ρ -> InvConv Γ M N A ρ).


Lemma Typed_bot {n} (M A : Tm n) (ρ : Env n) :
  Typed M A ρ bot.
Proof.
  exists bot, bot, (wt_bot (wt_bot wt_tuniv)).
  eauto using EvalRel_bot.
Qed.


(* =====================================================================
   InvConv combinators (LemmaForTS / TypingSemantics).

   These are pure logic: they correspond to convSound' for c_refl, c_sym
   (no Coq c_sym since the relation is symmetric by induction), c_trans,
   and c_conv. They use only the InvConv structure.
   ===================================================================== *)

Lemma InvConv_refl {n} (Γ : Ctx n) (M A : Tm n) :
  Γ ⊨ M ∈ A -> Γ ⊨ M ≡ M ∈ A.
Proof.
  move=> h ρ fρ. unfold InvConv. repeat split; eauto.
Qed.


(* convSound' (conv-refl dM) — from a typing derivation we get the
   reflexivity InvConv. *)
Lemma InvConv_refl' {n} (Γ : Ctx n) (M A : Tm n) ρ :
  InvTyped Γ M A ρ -> InvConv Γ M M A ρ.
Proof.
  move=> h. unfold InvConv. repeat split; eauto.
Qed.

(* convSound' (conv-trans d1 d2) *)
Lemma InvConv_trans {n} (Γ : Ctx n) (M N P A : Tm n) ρ :
  InvConv Γ M N A ρ -> InvConv Γ N P A ρ -> InvConv Γ M P A ρ.
Proof.
  move=> [iM [iN [fwd1 bwd1]]] [iN' [iP [fwd2 bwd2]]].
  unfold InvConv. repeat split; eauto.
Qed.

(* convSound' (conv-conv d dAB _): transport InvTyp through type
   conversion. We need that conversion preserves EvalRel of types. *)
Lemma InvConv_conv {n} (Γ : Ctx n) (M N A B : Tm n) :
  conv Γ M N A -> 
  conv Γ A B Core.tuniv -> 
  Γ ⊨ M ≡ N ∈ A -> 
  Γ ⊨ A ≡ B ∈ Core.tuniv -> 
  Γ ⊨ M ≡ N ∈ B.
Proof.
  move=> cMN CAB HMN HAB.
  unfold InvConv.
  intros ρ Fρ.
  specialize (HMN ρ Fρ). unfold InvConv in HMN.
  move: HMN => [iM [iN [h1 h2]]].
  specialize (HAB ρ Fρ). unfold InvConv in HAB.
  move: HAB => [iA [iB [h3 h4]]].
  unfold InvTyped in *.
  repeat split; eauto.
  + intros u EM. specialize (iM u EM). unfold Typed in iM.
  move: iM => [v [a [WTv [LE [EMv EA]]]]].
    exists v, a. repeat split; eauto.
  + intros u EN. specialize (iN u EN). unfold Typed in iN.
    move: iN => [v [a [WTv [LE [EMv EA]]]]].
    exists v, a. repeat split; eauto.
Qed. 

(* =====================================================================
   Lam_L1 (LemmaForTS.agda): Lam inversion with typed keys.

   If u ≤ ⟦Lam A M⟧ρ and u is not Bot, then there exists a, g, i such
   that EvalRel A ρ a, wt a tuniv, le u (abs g),
   EvalRel (abs A M) ρ (abs g), and for every g x = y, wt x a and
   EvalRel M (x .: ρ) y.

   ===================================================================== *)

Lemma valid_abs f :
  valid_fun f -> ~~ is_nil f -> valid (abs f).
Proof.
  move=> h1 h2.
  apply /andP. split; eauto.
Qed.

Hint Resolve valid_abs : valid.

(* ---------------------------------------------------------------------
   sigT-refactored Lam_L1.

   The existing [EvalRel_fun] returns a Prop-valued existential:
     forall u v, valid u -> app g u = Some v -> exists x, ...
   Extracting a per-edge witness function from this into a sigT requires
   the axiom of choice.  Instead, we introduce a Type-valued companion

       EvalRel_funT M ρ a g :=
         forall p, In p g ->
           { z & wt z a * le z (fst p) * EvalRel M (z .: ρ) (snd p) }

   and prove Lam_L1 by structural induction on the list.  No choice axiom
   is used.  Bridging to the existing Prop-valued EvalRel would itself
   require either choice or a refactor of EvalRel's abs case to return
   sigT instead of exists — left as a separate concern.
   --------------------------------------------------------------------- *)

Definition EvalRel_funT {n} (M : Tm (S n))
  (ρ : Env n) (a : elt) (g : list (elt * elt)) : Type :=
  forall p, In p g ->
    { z : elt & ((wt z a * (le z (fst p) = true)) *
                 EvalRel M (z .: ρ) (snd p))%type }.

(** [Lam_L1] (Agda: [Lam-L1]): from a [EvalRel_funT] table for body [M], each
    entry comes with a typed enlargement of its key and an [EvalRel] witness for
    its value — the per-edge data assembled into the value graph of a lambda. *)
Lemma Lam_L1 {n} (M : Tm (S n)) (ρ : Env n) (a : elt)
  (l : list (elt * elt))
  (ER_T : EvalRel_funT M ρ a l) :
  forall p, In p l ->
    { z : elt & ((wt z a * (le z (fst p) = true)) *
                 EvalRel M (z .: ρ) (snd p))%type }.
Proof.
  exact ER_T.
Qed.

(* Structural variant: if you have EvalRel_funT for a cons, you can
   restrict to the tail.  Used in the inductive step of InvTyp_Lam. *)
Lemma EvalRel_funT_tail {n} (M : Tm (S n)) ρ a (p : elt * elt) (ps : list (elt * elt)) :
  EvalRel_funT M ρ a (p :: ps) ->
  EvalRel_funT M ρ a ps.
Proof.
  move=> ER q Hq. apply ER. right. exact Hq.
Qed.

(* And the head witness extracts directly from the cons. *)
Lemma EvalRel_funT_head {n} (M : Tm (S n)) ρ a (p : elt * elt) (ps : list (elt * elt)) :
  EvalRel_funT M ρ a (p :: ps) ->
  { z : elt & ((wt z a * (le z (fst p) = true)) *
               EvalRel M (z .: ρ) (snd p))%type }.
Proof.
  move=> ER. apply ER. left. reflexivity.
Qed.


(* [valid_fun] of an append splits componentwise. *)
Lemma valid_fun_app_inv f g :
  valid_fun (f ++ g) -> valid_fun f /\ valid_fun g.
Proof.
  move=> H.
  have Cfg := @valid_fun_compatible (f ++ g) H.
  have Nfg := @valid_fun_no_bot (f ++ g) H.
  have Vfg := @valid_fun_subterms (f ++ g) H.
  rewrite compatible_fun_spec forallb_app in Cfg. apply andb_prop in Cfg. destruct Cfg as [Cf Cg].
  rewrite /no_bot_result forallb_app in Nfg. apply andb_prop in Nfg. destruct Nfg as [Nf Ng].
  rewrite forallb_app in Vfg. apply andb_prop in Vfg. destruct Vfg as [Vf Vg].
  split; apply /andP; (split; [apply /andP; split|]); auto.
  - rewrite compatible_fun_spec. apply /forallb_forall => -[u v] Hp.
    move: Cf => /forallb_forall Cf. move: (Cf _ Hp).
    rewrite /coherent_with forallb_app.
    move=> Hc; apply andb_prop in Hc; destruct Hc; assumption.
  - rewrite compatible_fun_spec. apply /forallb_forall => -[u v] Hp.
    move: Cg => /forallb_forall Cg. move: (Cg _ Hp).
    rewrite /coherent_with forallb_app.
    move=> Hc; apply andb_prop in Hc; destruct Hc; assumption.
Qed.

Lemma Typed_append {n}{A : Tm n} M B ρ f g :
  Typed (Core.abs A M) (Core.tpi A B) ρ (abs f) ->
  Typed (Core.abs A M) (Core.tpi A B) ρ (abs g) ->
  valid_fun (f ++ g) ->
  valid_env ρ ->
  Typed (Core.abs A M) (Core.tpi A B) ρ (abs (f ++ g)).
Proof.
  intros T1 T2 Vapp Vr.
  unfold Typed in *.
  destruct T1 as [v1 [a1 [WT1 [LE1 [EM1 EA1]]]]].
  destruct T2 as [v2 [a2 [WT2 [LE2 [EM2 EA2]]]]].
  apply le_abs_inv in LE1. destruct LE1 as [f1 [-> LF1]].
  apply le_abs_inv in LE2. destruct LE2 as [g1 [-> LF2]].
  move: (EvalRel_compatible Vr EM1 EM2) => Cfg.
  move: (EvalRel_compatible Vr EA1 EA2) => Ca.
  have Cf1g1 : compatible_fun f1 g1 by (move: Cfg; rewrite /= //).
  (* validity / nonemptiness of the two function bodies *)
  move: (EM1) => /= [Vf1 [NEf1 _]].
  move: (EM2) => /= [Vg1 [NEg1 _]].
  have Vabsf1 : valid (abs f1) by (apply valid_abs; auto).
  have Vabsg1 : valid (abs g1) by (apply valid_abs; auto).
  have Va1 : valid a1 by (eapply EvalRel_valid; exact EA1).
  have Va2 : valid a2 by (eapply EvalRel_valid; exact EA2).
  have WTa1 : wt a1 tuniv by (eapply wt_ty_tuniv; exact WT1).
  have WTa2 : wt a2 tuniv by (eapply wt_ty_tuniv; exact WT2).
  (* merged type a := lub a1 a2 *)
  set a := lub a1 a2.
  have WTa : wt a tuniv by (eapply wt_lub; [exact WTa1 | exact Ca | exact WTa2]).
  have Va : valid a by (apply (valid_lub Ca); auto).
  have le_a1_a : le a1 a by (apply le_lub_left; auto).
  have le_a2_a : le a2 a by (apply le_lub_right; auto).
  (* widen both function bodies to the merged type *)
  have WT1a : wt (abs f1) a by (eapply wt_le; [exact WT1 | exact le_a1_a | exact WTa1 | exact WTa]).
  have WT2a : wt (abs g1) a by (eapply wt_le; [exact WT2 | exact le_a2_a | exact WTa2 | exact WTa]).
  have WTmerge : wt (abs (f1 ++ g1)) a.
  { move: (wt_lub WT1a Cfg WT2a). rewrite /= Cf1g1 //. }
  have absfg : abs (f1 ++ g1) = lub (abs f1) (abs g1) by (rewrite /= Cf1g1 //).
  have [Vff Vfg] := valid_fun_app_inv Vapp.
  have V11 : valid_fun (f1 ++ g1) by (apply valid_append; auto).
  exists (abs (f1 ++ g1)), a, WTmerge.
  split; [|split].
  - (* le (abs (f++g)) (abs (f1++g1)) *)
    have Cfg0 : compatible_fun f g.
    { have HC := @valid_fun_compatible (f ++ g) Vapp.
      rewrite compatible_fun_spec in HC.
      rewrite compatible_fun_spec. apply /forallb_forall => -[u v] Hp.
      move: HC => /forallb_forall HC.
      have Hp' : In (u, v) (f ++ g) by (apply in_or_app; left).
      move: (HC _ Hp'). rewrite /coherent_with forallb_app.
      move=> Hc; apply andb_prop in Hc; destruct Hc; assumption. }
    have -> : abs (f ++ g) = lub (abs f) (abs g) by (rewrite /= Cfg0 //).
    apply le_sup_lub.
    + have lef : le_fun f (f1 ++ g1).
      { eapply le_fun_trans; [ exact Vff | exact Vf1 | exact V11 | exact LF1 |].
        rewrite -le_abs absfg. apply le_lub_left; auto. }
      by rewrite le_abs.
    + have leg : le_fun g (f1 ++ g1).
      { eapply le_fun_trans; [ exact Vfg | exact Vg1 | exact V11 | exact LF2 |].
        rewrite -le_abs absfg. apply le_lub_right; auto. }
      by rewrite le_abs.
  - (* EvalRel (abs A M) ρ (abs (f1++g1)) *)
    move: (EvalRel_compatible_lub Vr EM1 EM2) => [_ hm].
    exact (hm _ (esym absfg)).
  - (* EvalRel (tpi A B) ρ a *)
    move: (EvalRel_compatible_lub Vr EA1 EA2) => [_ hc].
    by apply (hc a).
Qed.

(* Single-edge construction: given a typed key [x] (an enlargement of
   [ui]) with [EvalRel M (x .: ρ) t] and the codomain typing [t : tx],
   the original edge [(ui, vi)] is Typed (i.e. [abs [(x,t)]] is a typed
   enlargement of [abs [(ui,vi)]]). *)
Lemma Typed_edge {n} (Γ : Ctx n) (A : Tm n) (B M : Tm (S n)) ρ a ui vi x t tx :
  typing Γ A Core.tuniv ->
  fits Γ ρ ->
  wt a tuniv -> EvalRel A ρ a ->
  wt x a -> le x ui ->
  wt t tx -> le vi t -> ~~ le vi bot ->
  EvalRel M (x .: ρ) t ->
  EvalRel B (x .: ρ) tx ->
  Typed (Core.abs A M) (Core.tpi A B) ρ (abs ((ui, vi) :: nil)).
Proof.
  move=> tA Fρ WTa ERa WTx LExui WTt LEvit NBvi ERMt ERBtx.
  have Vρ : valid_env ρ by eauto with valid.
  have Va : valid a by (eapply EvalRel_valid; exact ERa).
  have Vx : valid x by (eapply wt_valid_tm; exact WTx).
  have Vt : valid t by (eapply wt_valid_tm; exact WTt).
  have Vtx : valid tx by (eapply wt_valid_ty; exact WTt).
  have WTtx : wt tx tuniv by (eapply wt_ty_tuniv; exact WTt).
  have NBt : ~~ le t bot.
  { apply /negP => Hb. move: Hb => /le_bot_inv Et. subst t.
    move: NBvi => /negP NB. apply NB. exact LEvit. }
  have NBtx : ~~ le tx bot.
  { apply /negP => Hb. move: Hb => /le_bot_inv Etx. subst tx.
    move: WTt => /wt_bot_inv Et. subst t. move: NBt. by rewrite le_bot'. }
  have Vff : valid_fun ((x, t) :: nil).
  { apply /andP; split; [apply /andP; split|]; cbn;
      rewrite ?(compatible_refl Vx) ?(compatible_refl Vt) ?Vx ?Vt //.
    move: NBt; by case: (le t bot). }
  have Vfg : valid_fun ((x, tx) :: nil).
  { apply /andP; split; [apply /andP; split|]; cbn;
      rewrite ?(compatible_refl Vx) ?(compatible_refl Vtx) ?Vx ?Vtx //.
    move: NBtx; by case: (le tx bot). }
  have Vgpi : valid (tpi a ((x, tx) :: nil)) by (apply /andP; split; [exact Va | exact Vfg]).
  have WTpi : wt (tpi a ((x, tx) :: nil)) tuniv.
  { eapply wt_tpi; [exact WTa | | | exact Vgpi].
    - move=> u0 v0 [E|F]; [inversion E; subst; exact WTx | inversion F].
    - move=> u0 v0 [E|F]; [inversion E; subst; exact WTtx | inversion F]. }
  have WTabs : wt (abs ((x, t) :: nil)) (tpi a ((x, tx) :: nil)).
  { eapply wt_abs.
    - move=> u0 v0 Hin. destruct Hin as [E|F]; [|inversion F].
      inversion E; subst; exact WTx.
    - move=> u0 v0 Hin. destruct Hin as [E|F]; [|inversion F].
      inversion E; subst u0 v0.
      rewrite app_cons_eq app_nil_eq lub_bot_r (le_refl Vx). exact WTt.
    - apply valid_abs; [exact Vff | done].
    - exact WTpi. }
  exists (abs ((x, t) :: nil)), (tpi a ((x, tx) :: nil)), WTabs.
  split; [|split].
  - (* le (abs [(ui,vi)]) (abs [(x,t)]) *)
    rewrite le_abs le_fun_cons le_fun_nil andbT.
    rewrite app_cons_eq app_nil_eq lub_bot_r LExui. exact LEvit.
  - (* EvalRel (abs A M) ρ (abs [(x,t)]) *)
    split; [exact Vff|]. split; [done|].
    exists a, WTa. split; [exact ERa|].
    move=> u v Vu APP.
    rewrite app_cons_eq app_nil_eq lub_bot_r in APP.
    destruct (le x u) eqn:Lxu; subst v.
    + exists x, WTx. by split; [|exact ERMt].
    + exists bot, (wt_bot WTa). split; [by rewrite le_bot' | apply EvalRel_bot].
  - (* EvalRel (tpi A B) ρ (tpi a [(x,tx)]) *)
    split; [exact Va|]. split; [exact Vfg|]. split; [exact ERa|].
    exists a. split; [exact ERa|].
    move=> u v Vu APP.
    rewrite app_cons_eq app_nil_eq lub_bot_r in APP.
    destruct (le x u) eqn:Lxu; subst v.
    + exists x, WTx. by split; [|exact ERBtx].
    + exists bot, (wt_bot WTa). split; [by rewrite le_bot' | apply EvalRel_bot].
Qed.

(** Soundness of the lambda rule ([InvTyp-Lam]): given semantic typing of the
    domain, codomain, and body, the abstraction [abs A M] is invertibly typed
    at [tpi A B]. *)
Lemma InvTyp_Lam {n} (Γ : Ctx n) (A : Tm n) (B : Tm (S n)) (M : Tm (S n)) :
  typing Γ A Core.tuniv ->
  typing (Γ ++ A) B  Core.tuniv ->
  typing (Γ ++ A) M B ->
  Γ ⊨ A ∈ Core.tuniv ->
  Γ ++ A ⊨ B ∈ Core.tuniv ->
  Γ ++ A ⊨ M ∈ B ->
  Γ ⊨ (Core.abs A M) ∈ Core.tpi A B.
Proof.
  move=> tA tB tM TA TB TM ρ Fρ u EL.
  have Vρ : valid_env ρ by eauto with valid.
  destruct (~~ is_bot u) eqn:Bu.
  2: { destruct u; try done. by apply Typed_bot. }
  destruct u; try done.
  destruct EL as [Vl [NBl [a [WTa [ERa ERl]]]]].
  have Va : valid a by (eapply EvalRel_valid; exact ERa).
  clear Bu.
  (* Build [Typed (abs l)] by induction on the (non-empty) function body [l]. *)
  move: Vl ERl NBl. elim: l => [|[ui vi] l IHl] Vl ERl NBl.
  - (* empty: excluded by [NBl] *)
    done.
  - (* cons: head edge + tail (Typed_append) *)
    have Hui : In (ui, vi) ((ui, vi) :: l) by (left; reflexivity).
    have [Vui Vvi] := @valid_fun_subterms_prop ((ui, vi) :: l) Vl ui vi Hui.
    have NBvi : ~~ le vi bot.
    { move: (valid_fun_no_bot Vl) => /forallb_forall H.
      move: (H (ui, vi) Hui) => /=. done. }
    set w := app ((ui, vi) :: l) ui.
    have APPw : app ((ui, vi) :: l) ui = w by rewrite /w.
    have LEviw : le vi w by (rewrite /w; apply le_in_app; [exact Vl|exact Hui]).
    have Vw : valid w by (rewrite /w; apply valid_app; [exact Vl|exact Vui]).
    destruct (ERl ui w Vui APPw) as [x [WTx [LExui ERMw]]].
    have Vx : valid x by (eapply wt_valid_tm; exact WTx).
    have FE : fits (Γ ++ A) (x .: ρ) by (eapply fits_cons; eauto).
    move: (TM _ FE _ ERMw) => [t [tx [WTt [LEwt [ERMt ERBtx]]]]].
    have LEvit : le vi t by (eapply le_trans; [exact Vvi|exact Vw|eapply wt_valid_tm; exact WTt|exact LEviw|exact LEwt]).
    have Hd : Typed (Core.abs A M) (Core.tpi A B) ρ (abs ((ui, vi) :: nil)).
    { eapply Typed_edge with (x := x) (t := t) (tx := tx); eauto. }
    destruct l as [|p l'].
    + (* singleton: head is the whole function *)
      exact Hd.
    + (* nonempty tail: combine via Typed_append *)
      have Vtl : valid_fun (p :: l') by (eapply valid_fun_tail; exact Vl).
      (* restrict ERl to the tail *)
      have ERl' : EvalRel_fun M ρ a (p :: l').
      { move=> u v Vu APP.
        have Vapl : valid v by (rewrite -APP; apply valid_app; [exact Vtl | exact Vu]).
        destruct (le ui u) eqn:Luiu.
        - have C : compatible vi v.
          { rewrite -APP. eapply compatible_coherent_app.
            - eapply le_compatible; [exact Vu|exact Luiu].
            - eapply compat. eapply valid_fun_head; exact Vl. }
          have APP2 : app ((ui, vi) :: (p :: l')) u = lub vi v
            by (rewrite app_cons_eq Luiu APP).
          destruct (ERl u (lub vi v) Vu APP2) as [z [WTz [LEz ERz]]].
          have Vz : valid z by (eapply wt_valid_tm; exact WTz).
          exists z, WTz. split; [exact LEz|].
          eapply EvalRel_down;
            [ by apply valid_cons | exact Vapl | exact ERz
            | apply le_lub_right; [exact C | exact Vvi | exact Vapl] ].
        - have APP2 : app ((ui, vi) :: (p :: l')) u = v
            by (rewrite app_cons_eq Luiu APP).
          exact (ERl u v Vu APP2). }
      have Ht : Typed (Core.abs A M) (Core.tpi A B) ρ (abs (p :: l'))
        by (apply IHl; [exact Vtl | exact ERl' | done]).
      have := Typed_append (f := (ui, vi) :: nil) (g := p :: l') Hd Ht.
      rewrite /=. apply; [exact Vl | exact Vρ].
Qed.



(* [le_fun] is preserved by appending compatible extensions. *)
Lemma le_fun_append_merge f g f1 g1 :
  valid_fun (f ++ g) -> valid_fun f1 -> valid_fun g1 -> compatible_fun f1 g1 ->
  le_fun f f1 -> le_fun g g1 ->
  le_fun (f ++ g) (f1 ++ g1).
Proof.
  move=> Vapp Vf1 Vg1 Cf1g1 LF1 LF2.
  have [Vff Vfg] := valid_fun_app_inv Vapp.
  have V11 : valid_fun (f1 ++ g1) by (apply valid_append; auto).
  apply le_fun_extend.
  - eapply le_fun_trans; [exact Vff | exact Vf1 | exact V11 | exact LF1 |].
    apply /forallb_forall => -[ui vi] Hin.
    apply le_in_app; [exact V11 | apply in_or_app; left; exact Hin].
  - eapply le_fun_trans; [exact Vfg | exact Vg1 | exact V11 | exact LF2 |].
    apply /forallb_forall => -[ui vi] Hin.
    apply le_in_app; [exact V11 | apply in_or_app; right; exact Hin].
Qed.

(* Merge two typed enlargements of a Pi-type value (same domain code [b]).
   The two enlargements may use different domain enlargements [b1],[b2];
   we merge them through their [lub]. *)
Lemma Typed_pi_append {n} (A : Tm n) (B : Tm (S n)) ρ b f g :
  Typed (Core.tpi A B) Core.tuniv ρ (tpi b f) ->
  Typed (Core.tpi A B) Core.tuniv ρ (tpi b g) ->
  valid b ->
  valid_fun (f ++ g) ->
  valid_env ρ ->
  Typed (Core.tpi A B) Core.tuniv ρ (tpi b (f ++ g)).
Proof.
  intros T1 T2 Vb Vapp Vr.
  destruct T1 as [v1 [c1 [WT1 [LE1 [EM1 EA1]]]]].
  destruct T2 as [v2 [c2 [WT2 [LE2 [EM2 EA2]]]]].
  apply le_tpi_inv in LE1. destruct LE1 as [b1 [f1 [E1 [LEb1 LFf1]]]]. subst v1.
  apply le_tpi_inv in LE2. destruct LE2 as [b2 [g1 [E2 [LEb2 LFg1]]]]. subst v2.
  have WT1u : wt (tpi b1 f1) tuniv by (dependent destruction WT1; eapply wt_tpi; eauto).
  have WT2u : wt (tpi b2 g1) tuniv by (dependent destruction WT2; eapply wt_tpi; eauto).
  move: (EvalRel_compatible Vr EM1 EM2) => Cv.
  have Cdom : compatible b1 b2.
  { have C := Cv. cbn [compatible] in C. apply andb_prop in C. tauto. }
  have Cfun : compatible_fun f1 g1.
  { have C := Cv. cbn [compatible] in C. apply andb_prop in C. tauto. }
  move: (EM1) => /= [Vb1 [Vfun_f1 [ERAb1 _]]].
  move: (EM2) => /= [Vb2 [Vfun_g1 [ERAb2 _]]].
  have V11 : valid_fun (f1 ++ g1) by (apply valid_append; auto).
  set v := lub (tpi b1 f1) (tpi b2 g1).
  have WTv : wt v tuniv by (rewrite /v; eapply wt_lub; [exact WT1u | exact Cv | exact WT2u]).
  have Veq : v = tpi (lub b1 b2) (f1 ++ g1) by (rewrite /v /= Cfun).
  exists v, tuniv, WTv.
  split; [|split].
  - (* le (tpi b (f++g)) v *)
    rewrite Veq le_tpi. apply /andP; split.
    + have Vlub : valid (lub b1 b2) by (apply valid_lub; auto).
      apply (@le_trans b b1 (lub b1 b2));
        [ exact Vb | exact Vb1 | exact Vlub | exact LEb1 | apply le_lub_left; auto ].
    + apply le_fun_append_merge; auto.
  - (* EvalRel (tpi A B) ρ v *)
    move: (EvalRel_compatible_lub Vr EM1 EM2) => [_ hm].
    by apply (hm v).
  - (* EvalRel tuniv ρ tuniv *)
    by [].
Qed.

(* =====================================================================
   InvTyp_Pi (LemmaForTS.agda): Pi case at universe level.

       If A has InvTyp at (tuniv i) and the body B has InvTyp at
       (tuniv i) in every typed extended environment, then (Pi A B) has
       InvTyp at (tuniv i).
   ===================================================================== *)

(* Single codomain-edge construction for a Pi type.  [b''] is a typed
   domain enlargement that dominates both the Pi-domain code [b] and the
   codomain-function domain code [u'] (where the edge key [x] is typed). *)
Lemma Typed_pi_edge {n} (A : Tm n) (B : Tm (S n)) ρ b u' b'' ui vi x t :
  EvalRel A ρ b -> EvalRel A ρ u' -> EvalRel A ρ b'' ->
  wt b'' tuniv -> le b b'' -> le u' b'' ->
  wt x u' -> le x ui ->
  wt t tuniv -> le vi t -> ~~ le vi bot ->
  EvalRel B (x .: ρ) t ->
  valid_env ρ ->
  Typed (Core.tpi A B) Core.tuniv ρ (tpi b ((ui, vi) :: nil)).
Proof.
  move=> ERb ERu' ERb'' WTb'' LEbb'' LEu'b'' WTx LExui WTt LEvit NBvi ERBt Vr.
  have Vb'' : valid b'' by (eapply EvalRel_valid; exact ERb'').
  have Vx : valid x by (eapply wt_valid_tm; exact WTx).
  have Vt : valid t by (eapply wt_valid_tm; exact WTt).
  have WTu' : wt u' tuniv by (eapply wt_ty_tuniv; exact WTx).
  have WTxb'' : wt x b'' by (eapply wt_le; [exact WTx | exact LEu'b'' | exact WTu' | exact WTb'']).
  have NBt : ~~ le t bot.
  { apply /negP => Hb. move: Hb => /le_bot_inv Et. subst t.
    move: NBvi => /negP NB. apply NB. exact LEvit. }
  have Vff : valid_fun ((x, t) :: nil).
  { apply /andP; split; [apply /andP; split|]; cbn;
      rewrite ?(compatible_refl Vx) ?(compatible_refl Vt) ?Vx ?Vt //.
    move: NBt; by case: (le t bot). }
  have Vgpi : valid (tpi b'' ((x, t) :: nil)) by (apply /andP; split; [exact Vb'' | exact Vff]).
  have WTpi : wt (tpi b'' ((x, t) :: nil)) tuniv.
  { eapply wt_tpi; [exact WTb'' | | | exact Vgpi].
    - move=> u0 v0 Hin. destruct Hin as [E|F]; [|inversion F]. inversion E; subst; exact WTxb''.
    - move=> u0 v0 Hin. destruct Hin as [E|F]; [|inversion F]. inversion E; subst; exact WTt. }
  exists (tpi b'' ((x, t) :: nil)), tuniv, WTpi.
  split; [|split].
  - (* le (tpi b [(ui,vi)]) (tpi b'' [(x,t)]) *)
    rewrite le_tpi. apply /andP; split; [exact LEbb''|].
    rewrite le_fun_cons le_fun_nil andbT.
    rewrite app_cons_eq app_nil_eq lub_bot_r LExui. exact LEvit.
  - (* EvalRel (tpi A B) ρ (tpi b'' [(x,t)]) *)
    split; [exact Vb''|]. split; [exact Vff|]. split; [exact ERb''|].
    exists u'. split; [exact ERu'|].
    move=> u v Vu APP.
    rewrite app_cons_eq app_nil_eq lub_bot_r in APP.
    destruct (le x u) eqn:Lxu; subst v.
    + exists x, WTx. by split; [|exact ERBt].
    + exists bot, (wt_bot WTu'). split; [by rewrite le_bot' | apply EvalRel_bot].
  - by [].
Qed.

(** Soundness of the Π-formation rule ([InvTyp-Pi]): from semantic typing of
    the domain and codomain, the type [tpi A B] is invertibly typed in the
    universe. *)
Lemma InvTyp_Pi {n} (Γ : Ctx n) (A : Tm n) (B : Tm (S n)) :
  typing Γ A Core.tuniv ->
  typing (Γ ++ A) B Core.tuniv ->
  Γ ⊨ A ∈ Core.tuniv ->
  (Γ ++ A) ⊨ B ∈ Core.tuniv ->
  Γ ⊨ (Core.tpi A B) ∈ Core.tuniv.
Proof.
  move=> TA TB IHA IHB ρ Fρ u Eu.
  have Vρ : valid_env ρ by eauto with valid.
  destruct u as [ | | | | u0 | b l | f0 ]; try solve [cbn in Eu; done].
  { (* u = bot *) apply Typed_bot. }
  (* u = tpi b l *)
  cbn in Eu.
  destruct Eu as [Vb [Vf [EAb [u' [EAu' Hbody]]]]].
  have Vu' : valid u' by (eapply EvalRel_valid; exact EAu').
  (* enlarge b -> b1, u' -> u1 (both typed); the typed domain is b'' = lub b1 u1 *)
  destruct (IHA _ Fρ _ EAb) as [b1 [c1 [WTb1c1 [LEbb1 [EAb1 LEc1]]]]].
  destruct (IHA _ Fρ _ EAu') as [u1 [c2 [WTu1c2 [LEu'u1 [EAu1 LEc2]]]]].
  cbn in LEc1, LEc2.
  have Vb1 : valid b1 by (eapply EvalRel_valid; exact EAb1).
  have Vu1 : valid u1 by (eapply EvalRel_valid; exact EAu1).
  have WTb1 : wt b1 tuniv
    by (eapply wt_le; [exact WTb1c1 | exact LEc1 | eapply wt_ty_tuniv; exact WTb1c1 | apply wt_tuniv]).
  have WTu1 : wt u1 tuniv
    by (eapply wt_le; [exact WTu1c2 | exact LEc2 | eapply wt_ty_tuniv; exact WTu1c2 | apply wt_tuniv]).
  have Cb1u1 : compatible b1 u1 by (eapply EvalRel_compatible; [exact Vρ | exact EAb1 | exact EAu1]).
  set b'' := lub b1 u1.
  have Vb'' : valid b'' by (rewrite /b''; apply valid_lub; auto).
  have WTb'' : wt b'' tuniv by (rewrite /b''; eapply wt_lub; [exact WTb1 | exact Cb1u1 | exact WTu1]).
  have EAb'' : EvalRel A ρ b''.
  { move: (EvalRel_compatible_lub Vρ EAb1 EAu1) => [_ h]. by apply (h b''). }
  have LEbb'' : le b b''
    by (eapply le_trans;
        [exact Vb | exact Vb1 | exact Vb'' | exact LEbb1 | rewrite /b''; apply le_lub_left; auto]).
  have LEu'b'' : le u' b''
    by (eapply le_trans;
        [exact Vu' | exact Vu1 | exact Vb'' | exact LEu'u1 | rewrite /b''; apply le_lub_right; auto]).
  (* induction on the codomain function l *)
  move: Vf Hbody. elim: l => [|[ui vi] l IHl] Vf Hbody.
  - (* nil: tpi b nil, enlarged to tpi b'' nil *)
    exists (tpi b'' nil), tuniv.
    have WTpi : wt (tpi b'' nil) tuniv.
    { eapply wt_tpi; [exact WTb'' | move=> ?? [] | move=> ?? [] |].
      by apply /andP; split; [exact Vb''|]. }
    exists WTpi. split; [|split].
    + by rewrite le_tpi LEbb'' le_fun_nil.
    + split; [exact Vb''|]. split; [done|]. split; [exact EAb''|].
      exists b''. split; [exact EAb''|].
      move=> uu vv _ APP. rewrite app_nil_eq in APP. subst vv.
      exists bot, (wt_bot WTb''). split; [by rewrite le_bot' | apply EvalRel_bot].
    + by [].
  - (* cons: head edge (Typed_pi_edge) + tail (Typed_pi_append) *)
    have Hui : In (ui, vi) ((ui, vi) :: l) by (left; reflexivity).
    have [Vui Vvi] := @valid_fun_subterms_prop ((ui, vi) :: l) Vf ui vi Hui.
    have NBvi : ~~ le vi bot.
    { move: (valid_fun_no_bot Vf) => /forallb_forall H.
      move: (H (ui, vi) Hui) => /=. done. }
    set w := app ((ui, vi) :: l) ui.
    have APPw : app ((ui, vi) :: l) ui = w by rewrite /w.
    have LEviw : le vi w by (rewrite /w; apply le_in_app; [exact Vf|exact Hui]).
    have Vw : valid w by (rewrite /w; apply valid_app; [exact Vf|exact Vui]).
    destruct (Hbody ui w Vui APPw) as [x [WTx [LExui ERBw]]].
    have Vx : valid x by (eapply wt_valid_tm; exact WTx).
    have FE : fits (Γ ++ A) (x .: ρ)
      by (eapply fits_cons; [exact TA | exact EAu' | eapply wt_ty_tuniv; exact WTx | exact WTx | exact Fρ]).
    move: (IHB _ FE _ ERBw) => [t [tt [WTt [LEwt [ERBt ERuniv]]]]].
    have WTt' : wt t tuniv
      by (eapply wt_le; [exact WTt | exact ERuniv | eapply wt_ty_tuniv; exact WTt | apply wt_tuniv]).
    have LEvit : le vi t
      by (eapply le_trans; [exact Vvi|exact Vw|eapply wt_valid_tm; exact WTt|exact LEviw|exact LEwt]).
    have Hd : Typed (Core.tpi A B) Core.tuniv ρ (tpi b ((ui, vi) :: nil)).
    { eapply Typed_pi_edge with (u' := u') (b'' := b'') (x := x) (t := t); eauto. }
    destruct l as [|p l'].
    + exact Hd.
    + have Vtl : valid_fun (p :: l') by (eapply valid_fun_tail; exact Vf).
      have Hbody' : EvalRel_fun B ρ u' (p :: l').
      { move=> uu vv Vuu APP.
        have Vvv : valid vv by (rewrite -APP; apply valid_app; [exact Vtl | exact Vuu]).
        destruct (le ui uu) eqn:Luiuu.
        - have C : compatible vi vv.
          { rewrite -APP. eapply compatible_coherent_app.
            - eapply le_compatible; [exact Vuu|exact Luiuu].
            - eapply compat. eapply valid_fun_head; exact Vf. }
          have APP2 : app ((ui, vi) :: (p :: l')) uu = lub vi vv
            by (rewrite app_cons_eq Luiuu APP).
          destruct (Hbody uu (lub vi vv) Vuu APP2) as [z [WTz [LEz ERz]]].
          have Vz : valid z by (eapply wt_valid_tm; exact WTz).
          exists z, WTz. split; [exact LEz|].
          eapply EvalRel_down;
            [ by apply valid_cons | exact Vvv | exact ERz
            | apply le_lub_right; [exact C | exact Vvi | exact Vvv] ].
        - have APP2 : app ((ui, vi) :: (p :: l')) uu = vv
            by (rewrite app_cons_eq Luiuu APP).
          exact (Hbody uu vv Vuu APP2). }
      have Ht : Typed (Core.tpi A B) Core.tuniv ρ (tpi b (p :: l'))
        by (apply IHl; [exact Vtl | exact Hbody']).
      have := Typed_pi_append (b := b) (f := (ui, vi) :: nil) (g := p :: l') Hd Ht.
      rewrite /=. apply; [exact Vb | exact Vf | exact Vρ].
Qed.

(* =====================================================================
   InvTyp_App (LemmaForTS.agda): Application case.

       If M has InvTyp at (Pi A B) and N has InvTyp at A, then
       (App M N) has InvTyp at B[N..].
   ===================================================================== *)

(** Soundness of the application rule ([InvTyp-App]): if [M] is invertibly
    typed at [tpi A B] and [N] at [A], then [app M N] is invertibly typed at
    the substituted codomain [B[N..]]. *)
Lemma InvTyp_App {n} (Γ : Ctx n) (A : Tm n) (B : Tm (S n))
  (M : Tm n) (N : Tm n) ρ :
  fits Γ ρ ->
  InvTyped Γ M (Core.tpi A B) ρ ->
  InvTyped Γ N A ρ ->
  InvTyped Γ (Core.app M N) B[N..] ρ.
Proof.
  move=> Fρ InvM InvN.
  have Vρ : valid_env ρ by eauto with valid.
  move=> u Eu.
  destruct (is_bot u) eqn:Bu.
  { destruct u; cbn in Bu; try discriminate. apply Typed_bot. }
  (* u is not bot *)
  cbn [EvalRel] in Eu. rewrite Bu in Eu.
  destruct Eu as [w [EMw ENw]].
  have Vw : valid w by (eapply EvalRel_valid; exact ENw).
  (* w ↦ u = abs [(w,u)] *)
  have Esing : (w ↦ u) = abs ((w, u) :: nil) by (rewrite /singleton Bu).
  rewrite Esing in EMw.
  (* InvM gives a typed enlargement abs g : tpi a f *)
  destruct (InvM _ EMw) as [vM [avM [WTvM [LEvM [EMvM EAvM]]]]].
  apply le_abs_inv in LEvM. destruct LEvM as [g [E LFg]]. subst vM.
  move: LFg. rewrite le_fun_cons le_fun_nil andbT => LEug.   (* LEug : le u (app g w) *)
  (* the semantic type [avM] must be a [tpi] *)
  destruct avM as [ | | | | | a f | ];
    try solve [ cbn in EAvM; done
              | (move: (wt_bot_inv WTvM); discriminate) ].
  destruct EAvM as [Va [Vfun_f [EAa [a' [EAa' EBfun]]]]].
  (* the result value/type: app g w  /  app f w *)
  have WTres : wt (app g w) (app f w) by (eapply wt_app_valid; [exact WTvM | exact Vw]).
  have NBv : ~~ is_bot (app g w).
  { apply /negP => Hb.
    have Eb : app g w = bot by (move: Hb; by case: (app g w)).
    move: LEug. rewrite Eb. move=> /le_bot_inv Eu. subst u. by rewrite /= in Bu. }
  have Vgw : valid (app g w) by (eapply wt_valid_tm; exact WTres).
  have NBlev : ~~ le (app g w) bot.
  { apply /negP => H. move: H => /le_bot_inv E. rewrite E in NBv. cbn in NBv. done. }
  exists (app g w), (app f w), WTres.
  split; [|split].
  - (* le u (app g w) *) exact LEug.
  - (* EvalRel (app M N) ρ (app g w) *)
    cbn [EvalRel]. rewrite (negbTE NBv).
    exists w. split; [|exact ENw].
    have Esing2 : (w ↦ app g w) = abs ((w, app g w) :: nil) by (rewrite /singleton (negbTE NBv)).
    rewrite Esing2.
    have Vsing : valid (abs ((w, app g w) :: nil)).
    { apply valid_abs; [|done].
      apply /andP; split; [apply /andP; split|]; cbn;
        rewrite ?(compatible_refl Vw) ?(compatible_refl Vgw) ?Vw ?Vgw //.
      move: NBlev; by case: (le (app g w) bot). }
    eapply EvalRel_down; [exact Vρ | exact Vsing | exact EMvM |].
    rewrite le_abs le_fun_cons le_fun_nil andbT.
    exact (le_refl Vgw).
  - (* EvalRel B[N..] ρ (app f w) *)
    have [x [WTx [LExw EBx]]] :
      exists x (_ : wt x a'), le x w /\ EvalRel B (x .: ρ) (app f w).
    { apply (EBfun w (app f w) Vw); reflexivity. }
    have Vx : valid x by (eapply wt_valid_tm; exact WTx).
    eapply EvalRel_subst1_backwards; [exact Vρ | | exact EBx].
    eapply EvalRel_down; [exact Vρ | exact Vx | exact ENw | exact LExw].
Qed.

(* =====================================================================
   InvConv_App_fun (LemmaForTS.agda): App congruence on the function.

       If M = N : Pi A B and a : A, then App M a = App N a : B[a..].

   This one *is* tractable in the current Coq formulation, because the
   forward/backward EvalRel directions are pure unfolding of EvalRel for
   App — no graph reconstruction is needed.
   ===================================================================== *)

(** Conversion congruence in the function position ([InvConv-App-fun]): if
    [M ≡ N : tpi A B] and [a : A], then [app M a ≡ app N a : B[a..]]. *)
Lemma InvConv_App_fun {n} (Γ : Ctx n) (A : Tm n) (B : Tm (S n))
  (M N a : Tm n) ρ :
  fits Γ ρ ->
  InvConv Γ M N (Core.tpi A B) ρ ->
  InvTyped Γ a A ρ ->
  InvConv Γ (Core.app M a) (Core.app N a) B[a..] ρ.
Proof.
  move=> Fρ [iM [iN [fwd bwd]]] iA.
  unfold InvConv. repeat split.
  - eapply InvTyp_App; eauto.
  - eapply InvTyp_App; eauto.
  - move=> u E. cbn in E. cbn.
    destruct (is_bot u) eqn:Hb; first done.
    move: E => [w [EM EN]]. exists w. split; auto.
  - move=> u E. cbn in E. cbn.
    destruct (is_bot u) eqn:Hb; first done.
    move: E => [w [EN EM]]. exists w. split; auto.
Qed.

(* =====================================================================
   InvConv_App_arg (LemmaForTS.agda): App congruence on the argument.

       If M : Pi A B and a = a' : A, then App M a = App M a' : B[a..].
   ===================================================================== *)

(** Conversion congruence in the argument position ([InvConv-App-arg]): if
    [M : tpi A B] and [a ≡ a' : A], then [app M a ≡ app M a' : B[a..]]. *)
Lemma InvConv_App_arg {n} (Γ : Ctx n) (A : Tm n) (B : Tm (S n))
  (M a a' : Tm n) ρ :
  fits Γ ρ ->
  InvTyped Γ M (Core.tpi A B) ρ ->
  InvConv Γ a a' A ρ ->
  InvConv Γ (Core.app M a) (Core.app M a') B[a..] ρ.
Proof.
  move=> Fρ iM [iA [iA' [fwd bwd]]].
  have invLHS : InvTyped Γ (Core.app M a) B[a..] ρ
    by eapply InvTyp_App; eauto.
  have appfwd : forall u, EvalRel (Core.app M a) ρ u ->
                          EvalRel (Core.app M a') ρ u.
  { move=> u E. cbn in E. cbn.
    destruct (is_bot u) eqn:Hb; first done.
    move: E => [w [Ea EM]]. exists w. split; eauto. }
  have appbwd : forall u, EvalRel (Core.app M a') ρ u ->
                          EvalRel (Core.app M a) ρ u.
  { move=> u E. cbn in E. cbn.
    destruct (is_bot u) eqn:Hb; first done.
    move: E => [w [Ea' EM]]. exists w. split; eauto. }
  unfold InvConv. repeat split; auto.
  (* RHS: InvTyped (App M a') by routing through (App M a). *)
  move=> u E.
  specialize (invLHS u (appbwd _ E)).
  move: invLHS => [v [t [LE [EMa [Wv EBa]]]]].
  exists v, t. repeat split; eauto.
Qed.

(* =====================================================================
   InvConv_beta (LemmaForTS.agda): Beta conversion.

       Γ ⊢ A : U_i, (Γ++A) ⊢ B : U_j, (Γ++A) ⊢ M : B, Γ ⊢ N : A
       ⟹  app (abs A M) N  =  M[N..]  :  B[N..]

   Proof structure.  The hypotheses are *specific-ρ* semantic facts
   (InvTyped at this ρ, plus the body hypothesis [iM]), NOT typing /
   all-ρ judgments, so [InvTyp_App]/[InvTyp_Lam] are not applicable —
   everything is built directly.  [InvConv] = InvTyped of both sides +
   the two EvalRel directions; we prove:

     - fwd  (app (abs A M) N → M[N..]):  unfold the App; the function
       value [abs g] with the singleton edge [(w,u)] yields, via the
       [EvalRel_fun] edge, a [z ≤ w] with [EvalRel M (z.:ρ) u]; then
       [EvalRel N ρ z] (down from [EvalRel N ρ w]) and
       [EvalRel_subst1_backwards].

     - bwd  (M[N..] → app (abs A M) N):  [EvalRel_subst1_forward] gives
       [v] with [EvalRel N ρ v] and [EvalRel M (v.:ρ) u]; type-enlarge
       [v] to [vbig] via [iN] and build a singleton-graph Lam witness
       [abs [(vbig,u)]] (its body edge is [EvalRel M (vbig.:ρ) u], by
       [EvalRel_mono_env] from [v ≤ vbig]).

     - inv_subst (InvTyped of the reduct M[N..]):  [EvalRel_subst1_forward]
       + [iN] (enlarge) + [iM] (type the body) + [EvalRel_subst1_backwards]
       on both the term and the codomain type.

     - inv_app:  route InvTyped of the application through [inv_subst]
       using the fwd/bwd EvalRel equivalence.

   Key idiom: to expose [EvalRel (App (abs..) N)]/[EvalRel (abs..) (w↦u)]
   without [cbn] over-reducing the literal [abs] / leaf [EvalRel]s, unfold
   with a [have ... = ... by (cbn [EvalRel]; rewrite Hu; reflexivity)]
   equation (keeping the inner [EvalRel]s folded) and let [destruct]
   whnf-reduce [EvalRel (abs..) (abs g)] to its conjunction.
   ===================================================================== *)

(** Soundness of beta ([InvConv-beta]): the redex [app (abs A M) N] is
    invertibly convertible to its contractum [M[N..]] at type [B[N..]].  The
    forward direction uses [EvalRel_subst1_forward], the backward direction
    [EvalRel_subst1_backwards]. *)
Lemma InvConv_beta {n} (Γ : Ctx n) (A : Tm n) (B : Tm (S n))
  (M : Tm (S n)) (N : Tm n) ρ :
  fits Γ ρ ->
  InvTyped Γ N A ρ ->
  InvTyped Γ A Core.tuniv ρ ->
  (forall x a, wt x a -> wt a tuniv -> EvalRel A ρ a ->
    InvTyped (Γ ++ A) M B (x .: ρ)) ->
  InvConv Γ (Core.app (Core.abs A M) N) M[N..] B[N..] ρ.
Proof.
  move=> Fρ iN iA iM.
  have Vρ : valid_env ρ := fits_valid_env Fρ.
  (* EvalRel equivalence: [app (abs A M) N]  ≡  [M[N..]] *)
  have fwd : forall u, EvalRel (Core.app (Core.abs A M) N) ρ u -> EvalRel M[N..] ρ u.
  { move=> u E.
    destruct (is_bot u) eqn:Hu.
    { destruct u; cbn in Hu; try discriminate; apply EvalRel_bot. }
    have Eunf : EvalRel (Core.app (Core.abs A M) N) ρ u
              = (exists w, EvalRel (Core.abs A M) ρ (w ↦ u) /\ EvalRel N ρ w)
      by (cbn [EvalRel]; rewrite Hu; reflexivity).
    rewrite Eunf in E. move: E => [w [Eabs EN]].
    have Vw : valid w := EvalRel_valid EN.
    have Esing : (w ↦ u) = abs ((w, u) :: nil) by (rewrite /singleton Hu).
    rewrite Esing in Eabs.
    destruct Eabs as [Vf [Nnil [a0 [Wa0 [EA0 EFun]]]]].
    have APPa : app ((w, u) :: nil) w = u
      by (rewrite app_cons_eq !app_nil_eq lub_bot_r (le_refl Vw)).
    destruct (EFun w u Vw APPa) as [x [Wx [Lxw EMx]]].
    have Vx : valid x := wt_valid_tm Wx.
    have ENx : EvalRel N ρ x
      by (eapply EvalRel_down; [ exact Vρ | exact Vx | exact EN | exact Lxw ]).
    eapply EvalRel_subst1_backwards; [ exact Vρ | exact ENx | exact EMx ]. }
  have bwd : forall u, EvalRel M[N..] ρ u -> EvalRel (Core.app (Core.abs A M) N) ρ u.
  { move=> u E.
    destruct (is_bot u) eqn:Hu.
    { destruct u; cbn in Hu; try discriminate; apply EvalRel_bot. }
    have Vu : valid u := EvalRel_valid E.
    have NBu : ~~ le u bot.
    { apply /negP => H. move/le_bot_inv: H => H. rewrite H /= in Hu. discriminate Hu. }
    move: (EvalRel_subst1_forward Vρ E) => [v [EN EM]].
    have [vbig [abig [hwt [Lvvbig [ENbig EAbig]]]]] := iN v EN.
    have Vvbig : valid vbig := wt_valid_tm hwt.
    have Vv : valid v := EvalRel_valid EN.
    have EMbig : EvalRel M (vbig .: ρ) u.
    { eapply EvalRel_mono_env;
        [ exact EM | apply valid_cons; [ exact Vv | exact Vρ ]
        | apply valid_cons; [ exact Vvbig | exact Vρ ]
        | apply le_env_cons; [ exact Lvvbig | apply le_env_refl; exact Vρ ] ]. }
    have Vfun : valid_fun ((vbig, u) :: nil).
    { apply /andP; split; [ apply /andP; split | ]; cbn;
        rewrite ?(compatible_refl Vvbig) ?(compatible_refl Vu) ?Vvbig ?Vu //.
      move: NBu; by case: (le u bot). }
    have Eunf : EvalRel (Core.app (Core.abs A M) N) ρ u
              = (exists w, EvalRel (Core.abs A M) ρ (w ↦ u) /\ EvalRel N ρ w)
      by (cbn [EvalRel]; rewrite Hu; reflexivity).
    rewrite Eunf. exists vbig. split; [ | exact ENbig ].
    rewrite /singleton Hu.
    split; [ exact Vfun | split; [ done | ] ].
    exists abig, (wt_ty_tuniv hwt). split; [ exact EAbig | ].
    move=> u' v' Vu' APP.
    rewrite app_cons_eq !app_nil_eq lub_bot_r in APP.
    destruct (le vbig u') eqn:LE; cbn in APP; subst v'.
    - exists vbig, hwt. split; [ exact LE | exact EMbig ].
    - exists bot, (wt_bot (wt_ty_tuniv hwt)). split; [ apply le_bot' | apply EvalRel_bot ]. }
  (* InvTyped of the reduct [M[N..]], directly from [iN]/[iM] *)
  have inv_subst : InvTyped Γ M[N..] B[N..] ρ.
  { move=> u E.
    move: (EvalRel_subst1_forward Vρ E) => [v [EN EM]].
    have [vbig [abig [hwt [Lvvbig [ENbig EAbig]]]]] := iN v EN.
    have Vvbig : valid vbig := wt_valid_tm hwt.
    have Vv : valid v := EvalRel_valid EN.
    have EMbig : EvalRel M (vbig .: ρ) u.
    { eapply EvalRel_mono_env;
        [ exact EM | apply valid_cons; [ exact Vv | exact Vρ ]
        | apply valid_cons; [ exact Vvbig | exact Vρ ]
        | apply le_env_cons; [ exact Lvvbig | apply le_env_refl; exact Vρ ] ]. }
    move: (iM vbig abig hwt (wt_ty_tuniv hwt) EAbig u EMbig)
      => [w [c [hwc [Luw [EMw EBc]]]]].
    exists w, c, hwc. split; [ exact Luw | split ].
    - eapply EvalRel_subst1_backwards; [ exact Vρ | exact ENbig | exact EMw ].
    - eapply EvalRel_subst1_backwards; [ exact Vρ | exact ENbig | exact EBc ]. }
  (* InvTyped of the application, routed through the reduct *)
  have inv_app : InvTyped Γ (Core.app (Core.abs A M) N) B[N..] ρ.
  { move=> u E.
    move: (inv_subst u (fwd u E)) => [w [c [hwc [Luw [EMw EBc]]]]].
    exists w, c, hwc. split; [ exact Luw | split; [ exact (bwd w EMw) | exact EBc ] ]. }
  unfold InvConv.
  split; [ exact inv_app | split; [ exact inv_subst | split; [ exact fwd | exact bwd ] ] ].
Qed.

(* =====================================================================
   InvConv_funext (LemmaForTS.agda): Function extensionality.

       Γ ⊢ A : U, (Γ++A) ⊢ B : U, Γ ⊢ M : Pi A B, Γ ⊢ N : Pi A B
       (Γ++A) ⊢ App M⟨↑⟩ var0 = App N⟨↑⟩ var0 : B
       ⟹  M = N : Pi A B
   ===================================================================== *)

(* (un)folding [EvalRel] at an [app] value (non-bot), inner [EvalRel] folded. *)
Lemma EvalRel_app_inv {n} {P Q : Tm n} {ρ u} :
  is_bot u = false -> EvalRel (Core.app P Q) ρ u ->
  exists a, EvalRel P ρ (a ↦ u) /\ EvalRel Q ρ a.
Proof. move=> H E. cbn in E. rewrite H in E. exact E. Qed.

Lemma EvalRel_app_intro {n} {P Q : Tm n} {ρ u} :
  is_bot u = false ->
  (exists a, EvalRel P ρ (a ↦ u) /\ EvalRel Q ρ a) ->
  EvalRel (Core.app P Q) ρ u.
Proof. move=> H E. cbn. rewrite H. exact E. Qed.

(* Edgewise reassembly: a function value [abs g] is in [⟦M⟧] as soon as each
   of its single-edge restrictions [(ui ↦ vi)] is.  Inner compatibility is
   recovered for free from [EvalRel_compatible] (both edges are ≤ ⟦M⟧). *)
Lemma EvalRel_reassemble {n} (M : Tm n) ρ g :
  valid_env ρ -> valid_fun g -> ~~ is_nil g ->
  (forall ui vi, In (ui, vi) g -> EvalRel M ρ (ui ↦ vi)) ->
  EvalRel M ρ (abs g).
Proof.
  move=> Vρ. elim: g => [|[u0 v0] g' IH] Vfun Nnil Hedge; first done.
  have Hhead : EvalRel M ρ (u0 ↦ v0) by (apply Hedge; left; reflexivity).
  have NBv0 : ~~ le v0 bot.
  { move: (valid_fun_no_bot Vfun) => /forallb_forall H.
    move: (H (u0, v0) (or_introl erefl)) => /=. done. }
  have Hv0bot : is_bot v0 = false
    by (destruct v0; cbn in NBv0; solve [ reflexivity | done ]).
  destruct g' as [|p g''].
  - have -> : abs ((u0, v0) :: nil) = (u0 ↦ v0) by (rewrite /singleton Hv0bot).
    exact Hhead.
  - have Htail : EvalRel M ρ (abs (p :: g'')).
    { apply IH; [ eapply valid_fun_tail; exact Vfun | done
                | move=> ui vi Hin; apply Hedge; right; exact Hin ]. }
    have Vhead : valid (u0 ↦ v0) := EvalRel_valid Hhead.
    have Vtail : valid (abs (p :: g'')) := EvalRel_valid Htail.
    have Comp : compatible (u0 ↦ v0) (abs (p :: g'')) := EvalRel_compatible Vρ Hhead Htail.
    have CF : compatible_fun ((u0, v0) :: nil) (p :: g'').
    { move: Comp. rewrite /singleton Hv0bot => H. exact H. }
    have Elub : lub (u0 ↦ v0) (abs (p :: g'')) = abs ((u0, v0) :: p :: g'').
    { rewrite /singleton Hv0bot. cbn [lub]. rewrite CF. reflexivity. }
    rewrite -Elub.
    eapply EvalRel_sup;
      [ exact Vρ | exact Vhead | exact Vtail | exact Comp | reflexivity
      | exact Hhead | exact Htail ].
Qed.

(* =====================================================================
   InvConv_eta (LemmaForTS.InvConv-funext): function extensionality.

   Plan.  Prove [InvConv Γ N N' (tpi A B) ρ] for each [ρ ⊨ Γ].  The two
   [InvTyped] components come directly from [⊨N]/[⊨N'].  The interesting
   content is the bidirectional [EvalRel] equality of [N] and [N'], which
   we factor into one generic direction [gen P Q]:

     gen P Q (⊨P : Γ ⊨ P ∈ tpi A B)
             (body : ∀ρ' w, fits (Γ.A) ρ' →
                EvalRel (app P⟨↑⟩ var0) ρ' w → EvalRel (app Q⟨↑⟩ var0) ρ' w)
       : ∀u, EvalRel P ρ u → EvalRel Q ρ u.

   [fwd] is [gen N N'] using the forward edge of the body IH; [bwd] is
   [gen N' N] using its backward edge.

   Proof of [gen] (given [EvalRel P ρ u], [u] non-bot):
     1. [⊨P] gives a typed enlargement: [v ≥ u], [wt v c], [EvalRel P ρ v],
        [EvalRel (tpi A B) ρ c].  Since [P : tpi A B], [c = tpi b f] and
        [v = abs g] (the bot subcases force [u = bot]).
     2. Reduce the goal to [EvalRel Q ρ (abs g)] via [EvalRel_down] (using
        [u ≤ abs g]).
     3. [EvalRel_reassemble]: it suffices to put each edge [(ui,vi) ∈ g]
        into [⟦Q⟧], i.e. [EvalRel Q ρ (ui ↦ vi)]:
          - [EvalRel P ρ (ui ↦ vi)]            (down from [EvalRel P ρ (abs g)]);
          - [EvalRel (app P⟨↑⟩ var0) (ui.:ρ) vi]   (eta-application of P);
          - [EvalRel (app Q⟨↑⟩ var0) (ui.:ρ) vi]   (body IH at [fits (Γ.A)(ui.:ρ)]);
          - decompose: [EvalRel Q ρ (a ↦ vi)] with [a ≤ ui], then
            [EvalRel Q ρ (ui ↦ vi)] (down along [ui↦vi ≤ a↦vi]).
   ===================================================================== *)

(** Soundness of function extensionality / eta ([InvConv-funext]): two functions
    that agree on a fresh argument ([app N⟨↑⟩ x ≡ app N'⟨↑⟩ x]) are convertible
    at the Π-type.  Reassembles agreement on every value-graph edge via
    [EvalRel_reassemble]. *)
Lemma InvConv_eta {n} (Γ : Ctx n) (A : Tm n) (B : Tm (S n))
  (N N' : Tm n) :
  typing Γ A Core.tuniv ->
  typing Γ N (Core.tpi A B) ->
  typing Γ N' (Core.tpi A B) ->
  conv (Γ ++ A) (Core.app (⟨↑⟩ N) (var var_zero)) (Core.app (⟨↑⟩ N') (var var_zero)) B ->
  Γ ⊨ A ∈ Core.tuniv ->
  Γ ⊨ N ∈ (Core.tpi A B) ->
  Γ ⊨ N' ∈ (Core.tpi A B) ->
  Γ ++ A ⊨ (Core.app (⟨↑⟩ N) (var var_zero)) ≡ (Core.app (⟨↑⟩ N') (var var_zero)) ∈ B ->
  Γ ⊨ N ≡ N' ∈ (Core.tpi A B).
Proof.
  move=> TA TN TN' Cbody iA iN iN' ibody ρ Fρ.
  have Vρ : valid_env ρ by eauto with valid.
  have gen : forall (P Q : Tm n),
      Γ ⊨ P ∈ (Core.tpi A B) ->
      (forall ρ' w, fits (Γ ++ A) ρ' ->
         EvalRel (Core.app P⟨↑⟩ (var var_zero)) ρ' w ->
         EvalRel (Core.app Q⟨↑⟩ (var var_zero)) ρ' w) ->
      forall u, EvalRel P ρ u -> EvalRel Q ρ u.
  { move=> P Q iP body u E.
    destruct (is_bot u) eqn:Hu.
    { destruct u; try done; apply EvalRel_bot. }
    have Vu : valid u := EvalRel_valid E.
    move: (iP ρ Fρ u E) => [v [c [hwc [Luv [EPv ETc]]]]].
    destruct c as [ | | | | | b f | ]; try solve [ cbn in ETc; done ].
    - (* c = bot ⇒ v = bot ⇒ u = bot, contradiction *)
      have Ev := wt_bot_inv hwc. subst v.
      move: Luv => /le_bot_inv Eu. subst u. by rewrite /= in Hu.
    - (* c = tpi b f *)
      destruct v as [ | | | | | | g ]; try solve [ exfalso; clear -hwc; inversion hwc ].
      + (* v = bot ⇒ u = bot *) move: Luv => /le_bot_inv Eu. subst u. by rewrite /= in Hu.
      + (* v = abs g *)
        have Vabsg : valid (abs g) := wt_valid_tm hwc.
        have Vfun : valid_fun g := proj1 (andb_prop _ _ Vabsg).
        have Nnil : ~~ is_nil g := proj2 (andb_prop _ _ Vabsg).
        have EAb : EvalRel A ρ b := proj1 (proj2 (proj2 ETc)).
        have Wbt : wt b tuniv := wt_tpi_dom (wt_ty_tuniv hwc).
        eapply EvalRel_down; [ exact Vρ | exact Vu | | exact Luv ].
        apply EvalRel_reassemble; [ exact Vρ | exact Vfun | exact Nnil | ].
        move=> ui vi Hin.
        have [Vui Vvi] := valid_fun_subterms_prop g Vfun ui vi Hin.
        have Wui : wt ui b := wt_abs_inv1 hwc Hin.
        have NBvi : ~~ le vi bot.
        { move: (valid_fun_no_bot Vfun) => /forallb_forall H.
          move: (H (ui, vi) Hin) => /=. done. }
        have Hvibot : is_bot vi = false
          by (destruct vi; cbn in NBvi; solve [ reflexivity | done ]).
        have Vsing : valid (ui ↦ vi).
        { rewrite /singleton Hvibot /= /_valid_fun /= !Bool.andb_true_r.
          apply /andP; split. 2: by rewrite Vui Vvi.
          apply /andP; split. 2: exact NBvi.
          apply /implyP => _. by apply compatible_refl. }
        have HleAbs : le (ui ↦ vi) (abs g).
        { rewrite /singleton Hvibot le_abs le_fun_cons le_fun_nil andbT.
          apply le_in_app; [ exact Vfun | exact Hin ]. }
        have EP_edge : EvalRel P ρ (ui ↦ vi)
          := EvalRel_down Vρ Vsing EPv HleAbs.
        have EappP : EvalRel (Core.app P⟨↑⟩ (var var_zero)) (ui .: ρ) vi.
        { apply EvalRel_app_intro; first exact Hvibot.
          exists ui. split.
          - apply EvalRel_wk; exact EP_edge.
          - cbn. split; [ exact Vui | apply le_refl; exact Vui ]. }
        have FE : fits (Γ ++ A) (ui .: ρ)
          by (eapply fits_cons; [ exact TA | exact EAb | exact Wbt | exact Wui | exact Fρ ]).
        have EappQ : EvalRel (Core.app Q⟨↑⟩ (var var_zero)) (ui .: ρ) vi
          := body (ui .: ρ) vi FE EappP.
        move: (EvalRel_app_inv Hvibot EappQ) => [a [EQwk EvarA]].
        have [Va Lea] : valid a /\ le a ui by (move: EvarA; cbn).
        have EQ_a : EvalRel Q ρ (a ↦ vi) := EvalRel_unwk EQwk.
        have Hle2 : le (ui ↦ vi) (a ↦ vi).
        { rewrite /singleton Hvibot le_abs le_fun_cons le_fun_nil andbT.
          rewrite app_cons_eq app_nil_eq lub_bot_r Lea /=. apply le_refl; exact Vvi. }
        exact (EvalRel_down Vρ Vsing EQ_a Hle2). }
  unfold InvConv.
  split; [ exact (iN ρ Fρ) | ].
  split; [ exact (iN' ρ Fρ) | ].
  split.
  - exact (gen N N' iN (fun ρ' w Fρ' => proj1 (proj2 (proj2 (ibody ρ' Fρ'))) w)).
  - exact (gen N' N iN' (fun ρ' w Fρ' => proj2 (proj2 (proj2 (ibody ρ' Fρ'))) w)).
Qed.

(*
Lemma InvConv_nrec_Z : forall (n : nat) (Γ : Ctx n) (M0 M1 : Tm n) (T : Tm (S n)),
    typing (Γ ++ Core.tnat) T Core.tuniv ->
    typing Γ M0 T[Core.zero..] ->
    typing Γ M1 (Core.tpi Core.tnat (Core.tpi T (⟨↑⟩ T[rho]))) ->
    (Γ ++ Core.tnat)  ⊨ T ∈ Core.tuniv ->
    Γ  ⊨ M0 ∈ T[Core.zero..] ->
    Γ  ⊨ M1 ∈ (Core.tpi Core.tnat (Core.tpi T (⟨↑⟩ T[rho]))) ->
    Γ  ⊨ (Core.app (nrec T M0 M1) Core.zero) ≡ M0 ∈ T[Core.zero..].

Lemma InvConv_nrec_S : forall (n : nat) (Γ : Ctx n) (T : Tm (S n)) (M0 M1 n0 : Tm n),    
    typing (Γ ++ Core.tnat) T Core.tuniv ->
    typing Γ M0 T[Core.zero..] ->
    typing Γ M1 (Core.tpi Core.tnat (Core.tpi T (⟨↑⟩ T[rho]))) ->
    (Γ ++ Core.tnat) ⊨ T ∈ Core.tuniv ->
    Γ ⊨ M0 ∈ T[Core.zero..] ->
    Γ ⊨ M1 ∈ (Core.tpi Core.tnat (Core.tpi T (⟨↑⟩ T[rho]))) ->
    Γ ⊨ (Core.app (nrec T M0 M1) (Core.succ n0)) ≡ 
      (Core.app (Core.app M1 n0) (Core.app (nrec T M0 M1) n0)) ∈ T[(Core.succ n0)..].
*)

(* One-step (un)folding of [EvalRel] at a [tpi] value, keeping the inner
   [EvalRel] occurrences folded (plain [cbn] over-unfolds them, and [rewrite]
   chokes on the [EvalRel] fixpoint).  Both directions hold definitionally. *)
Lemma EvalRel_tpi_inv {n} {X : Tm n} {Y : Tm (S n)} {ρ a g} :
  EvalRel (Core.tpi X Y) ρ (tpi a g) ->
  (valid a /\ valid_fun g /\ EvalRel X ρ a
   /\ exists a', EvalRel X ρ a'
      /\ (forall u v, valid u -> app g u = v
           -> exists x (_ : wt x a'), le x u /\ EvalRel Y (x .: ρ) v)).
Proof. exact (fun h => h). Qed.

Lemma EvalRel_tpi_intro {n} {X : Tm n} {Y : Tm (S n)} {ρ a g} :
  (valid a /\ valid_fun g /\ EvalRel X ρ a
   /\ exists a', EvalRel X ρ a'
      /\ (forall u v, valid u -> app g u = v
           -> exists x (_ : wt x a'), le x u /\ EvalRel Y (x .: ρ) v)) ->
  EvalRel (Core.tpi X Y) ρ (tpi a g).
Proof. exact (fun h => h). Qed.

(* (un)folding [EvalRel] at a [succ] value (non-bot), inner [EvalRel] folded. *)
Lemma EvalRel_succ_inv {n} {M : Tm n} {ρ u} :
  is_bot u = false -> EvalRel (Core.succ M) ρ u ->
  valid u /\ exists a, le u (succ a) /\ EvalRel M ρ a.
Proof. move=> H E. cbn in E. rewrite H in E. exact E. Qed.

Lemma EvalRel_succ_intro {n} {M : Tm n} {ρ u} :
  is_bot u = false ->
  (valid u /\ exists a, le u (succ a) /\ EvalRel M ρ a) ->
  EvalRel (Core.succ M) ρ u.
Proof. move=> H E. cbn. rewrite H. exact E. Qed.

(* [succ] preserves [InvTyped] at [tnat] (the [t_succ] reasoning, factored). *)
Lemma InvTyp_succ {n} (Γ : Ctx n) (M : Tm n) ρ :
  InvTyped Γ M Core.tnat ρ -> InvTyped Γ (Core.succ M) Core.tnat ρ.
Proof.
  move=> ihM u Eu.
  destruct (Raw.is_bot u) eqn:HU.
  { destruct u; try done. apply Typed_bot. }
  move: (EvalRel_succ_inv HU Eu) => [Vu [a [LE EMa]]].
  specialize (ihM a EMa).
  destruct ihM as [v [a' [WTva [LEav [EMv EA]]]]].
  have Vv : valid v by eapply wt_valid_tm; eauto.
  have Va : valid a by eapply EvalRel_valid; eauto.
  have WTv_tnat : wt v tnat.
  { destruct a'; try done.
    apply wt_bot_inv in WTva. subst v. eapply wt_bot; eapply wt_tnat. }
  have LEsv : le u (succ v).
  { destruct u; try done. cbn in Vu.
    rewrite le_succ. rewrite le_succ in LE.
    eapply le_trans; [ exact Vu | exact Va | exact Vv | exact LE | exact LEav ]. }
  exists (succ v), tnat, (wt_succ WTv_tnat).
  split; first exact LEsv.
  split.
  { apply EvalRel_succ_intro; first by [].
    split; first exact Vv.
    exists v. split; first by eapply le_refl. exact EMv. }
  cbn. done.
Qed.

Lemma InvConv_succ {n} (Γ : Ctx n) (M N : Tm n) ρ :
  InvConv Γ M N Core.tnat ρ -> InvConv Γ (Core.succ M) (Core.succ N) Core.tnat ρ.
Proof.
  move=> [iM [iN [fwd bwd]]].
  unfold InvConv. split; [ apply InvTyp_succ; exact iM | ].
  split; [ apply InvTyp_succ; exact iN | ].
  split.
  - move=> u E. destruct (is_bot u) eqn:HU.
    { destruct u; try done; apply EvalRel_bot. }
    move: (EvalRel_succ_inv HU E) => [Vu [a [LE EMa]]].
    apply EvalRel_succ_intro; first exact HU.
    split; [ exact Vu | exists a; split; [ exact LE | exact (fwd a EMa) ] ].
  - move=> u E. destruct (is_bot u) eqn:HU.
    { destruct u; try done; apply EvalRel_bot. }
    move: (EvalRel_succ_inv HU E) => [Vu [a [LE EMa]]].
    apply EvalRel_succ_intro; first exact HU.
    split; [ exact Vu | exists a; split; [ exact LE | exact (bwd a EMa) ] ].
Qed.

Lemma InvConv_tpi : forall (n : nat) (Γ : Ctx n) (A0 A1 : Tm n) (B0 B1 : Tm (S n)),
    conv Γ A0 A1 Core.tuniv ->
    conv (Γ ++ A0) B0 B1 Core.tuniv ->
    Γ ⊨ A0 ≡ A1 ∈ Core.tuniv ->
    (Γ ++ A0) ⊨ B0 ≡ B1 ∈ Core.tuniv ->
    Γ ⊨ (Core.tpi A0 B0) ≡ (Core.tpi A1 B1) ∈ Core.tuniv.
Proof.
  move=> n Γ A0 A1 B0 B1 cA cB ihA ihB ρ Fρ.
  have Vρ : valid_env ρ by eauto with valid.
  have [TA0 TA1] := conv_typing cA.
  have [TB0 TB1] := conv_typing cB.
  move: (ihA ρ Fρ) => [_ [_ [fwdA bwdA]]].
  (* the [σ0]-side Pi is well-typed (InvTyp_Pi) *)
  have iTpi0 : InvTyped Γ (Core.tpi A0 B0) Core.tuniv ρ.
  { eapply InvTyp_Pi; [ exact TA0 | exact TB0 | | | exact Fρ ].
    - move=> ρ' Fρ'. exact (proj1 (ihA ρ' Fρ')).
    - move=> ρ' Fρ'. exact (proj1 (ihB ρ' Fρ')). }
  (* forward EvalRel: [tpi A0 B0] → [tpi A1 B1] *)
  have fwd : forall u, EvalRel (Core.tpi A0 B0) ρ u -> EvalRel (Core.tpi A1 B1) ρ u.
  { move=> u E. destruct u as [ | | | | | a g | ];
      try solve [ cbn in E; done | apply EvalRel_bot ].
    move: (EvalRel_tpi_inv E) => [Va [Vg [EA0a [a' [EA0a' Hbody]]]]].
    apply EvalRel_tpi_intro.
    split; [ exact Va | ]. split; [ exact Vg | ]. split; [ exact (fwdA a EA0a) | ].
    exists a'. split; [ exact (fwdA a' EA0a') | ].
    move=> u' v' Vu' APP.
    destruct (Hbody u' v' Vu' APP) as [x [WTx [LExu' EB0]]].
    have FE : fits (Γ ++ A0) (x .: ρ)
      by (eapply fits_cons; [ exact TA0 | exact EA0a' | eapply wt_ty_tuniv; exact WTx | exact WTx | exact Fρ ]).
    exists x, WTx. split; [ exact LExu' | ].
    exact (proj1 (proj2 (proj2 (ihB (x .: ρ) FE))) v' EB0). }
  (* backward EvalRel: [tpi A1 B1] → [tpi A0 B0] *)
  have bwd : forall u, EvalRel (Core.tpi A1 B1) ρ u -> EvalRel (Core.tpi A0 B0) ρ u.
  { move=> u E. destruct u as [ | | | | | a g | ];
      try solve [ cbn in E; done | apply EvalRel_bot ].
    move: (EvalRel_tpi_inv E) => [Va [Vg [EA1a [a' [EA1a' Hbody]]]]].
    have EA0a : EvalRel A0 ρ a := bwdA a EA1a.
    have EA0a' : EvalRel A0 ρ a' := bwdA a' EA1a'.
    apply EvalRel_tpi_intro.
    split; [ exact Va | ]. split; [ exact Vg | ]. split; [ exact EA0a | ].
    exists a'. split; [ exact EA0a' | ].
      move=> u' v' Vu' APP.
      destruct (Hbody u' v' Vu' APP) as [x [WTx [LExu' EB1]]].
      have FE : fits (Γ ++ A0) (x .: ρ)
        by (eapply fits_cons; [ exact TA0 | exact EA0a' | eapply wt_ty_tuniv; exact WTx | exact WTx | exact Fρ ]).
      exists x, WTx. split; [ exact LExu' | ].
      exact (proj2 (proj2 (proj2 (ihB (x .: ρ) FE))) v' EB1). }
  (* the [σ1]-side Pi is well-typed by routing through the [σ0]-side *)
  have iTpi1 : InvTyped Γ (Core.tpi A1 B1) Core.tuniv ρ.
  { move=> u E. move: (iTpi0 u (bwd u E)) => [v [c [h [Luv [E0 Ec]]]]].
    exists v, c, h. split; [ exact Luv | split; [ exact (fwd v E0) | exact Ec ] ]. }
  unfold InvConv.
  split; [ exact iTpi0 | split; [ exact iTpi1 | split; [ exact fwd | exact bwd ] ] ].
Qed.

(* (un)folding [EvalRel] at an [abs] value, inner [EvalRel] folded. *)
Lemma EvalRel_abs_inv {n} {A : Tm n} {M : Tm (S n)} {ρ g} :
  EvalRel (Core.abs A M) ρ (abs g) ->
  (valid_fun g /\ ~~ is_nil g /\ exists a (_ : wt a tuniv), EvalRel A ρ a
   /\ (forall u v, valid u -> app g u = v
        -> exists x (_ : wt x a), le x u /\ EvalRel M (x .: ρ) v)).
Proof. exact (fun h => h). Qed.

Lemma EvalRel_abs_intro {n} {A : Tm n} {M : Tm (S n)} {ρ g} :
  (valid_fun g /\ ~~ is_nil g /\ exists a (_ : wt a tuniv), EvalRel A ρ a
   /\ (forall u v, valid u -> app g u = v
        -> exists x (_ : wt x a), le x u /\ EvalRel M (x .: ρ) v)) ->
  EvalRel (Core.abs A M) ρ (abs g).
Proof. exact (fun h => h). Qed.

(* Lambda congruence at the [EvalRel] level. *)
Lemma InvConv_abs {n} (Γ : Ctx n) (A A' : Tm n) (B M M' : Tm (S n)) :
  typing Γ A Core.tuniv ->
  typing (Γ ++ A) B Core.tuniv ->
  typing (Γ ++ A) M B ->
  conv Γ A A' Core.tuniv ->
  conv (Γ ++ A) M M' B ->
  Γ ⊨ A ≡ A' ∈ Core.tuniv ->
  (Γ ++ A) ⊨ B ∈ Core.tuniv ->
  (Γ ++ A) ⊨ M ≡ M' ∈ B ->
  Γ ⊨ (Core.abs A M) ≡ (Core.abs A' M') ∈ (Core.tpi A B).
Proof.
  move=> TA TB TM cA cM ihA ihMB ihM ρ Fρ.
  have Vρ : valid_env ρ by eauto with valid.
  move: (ihA ρ Fρ) => [_ [_ [fwdA bwdA]]].
  (* [abs A M : tpi A B] via [InvTyp_Lam] *)
  have iLam0 : InvTyped Γ (Core.abs A M) (Core.tpi A B) ρ.
  { apply InvTyp_Lam;
      [ exact TA | exact TB | exact TM
      | (move=> ρ' Fρ'; exact (proj1 (ihA ρ' Fρ')))
      | exact ihMB
      | (move=> ρ' Fρ'; exact (proj1 (ihM ρ' Fρ')))
      | exact Fρ ]. }
  have fwd : forall u, EvalRel (Core.abs A M) ρ u -> EvalRel (Core.abs A' M') ρ u.
  { move=> u E. destruct u as [ | | | | | | g ];
      try solve [ cbn in E; done | apply EvalRel_bot ].
    move: (EvalRel_abs_inv E) => [Vg [Nnil [a [Wa [EAa Hbody]]]]].
    apply EvalRel_abs_intro.
    split; [ exact Vg | ]. split; [ exact Nnil | ].
    exists a, Wa. split; [ exact (fwdA a EAa) | ].
    move=> u' v' Vu' APP.
    destruct (Hbody u' v' Vu' APP) as [x [WTx [LExu' EM0]]].
    have FE : fits (Γ ++ A) (x .: ρ)
      by (eapply fits_cons; [ exact TA | exact EAa | exact Wa | exact WTx | exact Fρ ]).
    exists x, WTx. split; [ exact LExu' | ].
    exact (proj1 (proj2 (proj2 (ihM (x .: ρ) FE))) v' EM0). }
  have bwd : forall u, EvalRel (Core.abs A' M') ρ u -> EvalRel (Core.abs A M) ρ u.
  { move=> u E. destruct u as [ | | | | | | g ];
      try solve [ cbn in E; done | apply EvalRel_bot ].
    move: (EvalRel_abs_inv E) => [Vg [Nnil [a [Wa [EA'a Hbody]]]]].
    have EAa : EvalRel A ρ a := bwdA a EA'a.
    apply EvalRel_abs_intro.
    split; [ exact Vg | ]. split; [ exact Nnil | ].
    exists a, Wa. split; [ exact EAa | ].
    move=> u' v' Vu' APP.
    destruct (Hbody u' v' Vu' APP) as [x [WTx [LExu' EM'0]]].
    have FE : fits (Γ ++ A) (x .: ρ)
      by (eapply fits_cons; [ exact TA | exact EAa | exact Wa | exact WTx | exact Fρ ]).
    exists x, WTx. split; [ exact LExu' | ].
    exact (proj2 (proj2 (proj2 (ihM (x .: ρ) FE))) v' EM'0). }
  have iLam1 : InvTyped Γ (Core.abs A' M') (Core.tpi A B) ρ.
  { move=> u E. move: (iLam0 u (bwd u E)) => [v [c [h [Luv [E0 Ec]]]]].
    exists v, c, h. split; [ exact Luv | split; [ exact (fwd v E0) | exact Ec ] ]. }
  unfold InvConv.
  split; [ exact iLam0 | split; [ exact iLam1 | split; [ exact fwd | exact bwd ] ] ].
Qed.

(* =====================================================================
   Theorem 1 (TypingSemantics.agda):
       Γ ⊢ M : A  ==> Γ ⊨ M ∈ A.
   Conversion soundness:
       Γ ⊢ M ≡ N : A  ⟹  Γ ⊨ M ≡ N ∈ A.

   These are mutually defined, since:
     - typing's t_conv case calls conv (for the type conversion).
     - conv's c_app1 / c_app2 / c_beta / c_eta cases call typing.

   See TypingSemantics.agda's mutual block.
   ===================================================================== *)

(** Theorem 1 — typing soundness (Agda: [theorem1]): a typing derivation
    [Γ ⊢ M : A] yields [Γ ⊨ M ∈ A], i.e. [M] is invertibly typed under every
    fitting environment.  Mutually defined with [conv_EvalRel] — conversion
    soundness (Agda: [convSound']): [Γ ⊢ M ≡ N : A] yields [Γ ⊨ M ≡ N ∈ A].  The
    mutual recursion is essential: the [t_conv] typing case appeals to
    conversion, while the [c_app]/[c_beta]/[c_eta] conversion cases appeal to
    typing.  Each rule is discharged by the corresponding [InvTyp_*]/[InvConv_*]
    lemma above. *)
Fixpoint typing_EvalRel {n} (Γ : Ctx n) (M : Tm n) (A : Tm n)
   (h : typing Γ M A) {struct h} :
   Γ ⊨ M ∈ A
with conv_EvalRel {n} (Γ : Ctx n) (M N : Tm n) (A : Tm n)
   (h : conv Γ M N A) {struct h} :
  Γ ⊨ M ≡ N ∈ A.
Proof.
  - destruct h.
    all: move=> ρ Fρ.
    + (* t_var *)
      unfold InvTyped, Typed.
      move=> u E.
      move: E => [Vu Lu].
      move: (fits_var Fρ x) => [a [hT [Ea [WT1 WT2]]]].
      exists (ρ x). exists a.
      repeat split;
      eauto using le_refl, EvalRel_valid with valid.
    + (* t_conv *)
      have ihM : InvTyped Γ M A ρ by eapply typing_EvalRel; eauto.
      have ihAB : InvConv Γ A B Core.tuniv ρ
        by eapply conv_EvalRel; eauto.
      move: ihAB => [_ [_ [fwdAB _]]].
      move=> u Eu. specialize (ihM u Eu).
      move: ihM => [v [a [LE [EM [Wv EA]]]]].
      exists v, a. repeat split; eauto.
    + (* t_abs *)
      move: ρ Fρ.
      eapply InvTyp_Lam; try eassumption.
      eapply typing_EvalRel; eauto.
      eapply typing_EvalRel; eauto.
      eapply typing_EvalRel; eauto.
    + (* t_app *)
      apply (@InvTyp_App _ Γ A B N M ρ Fρ).
      * exact (typing_EvalRel _ _ _ _ h3 ρ Fρ).
      * exact (typing_EvalRel _ _ _ _ h4 ρ Fρ).
    + (* t_nat: tnat : tuniv.  EvalRel tnat ρ u = le u tnat, so u ∈ {bot, tnat}.
         Take Typed witness (tnat, tuniv, wt_tnat). *)
      move=> u Eu. cbn in Eu.
      exists tnat, tuniv, wt_tnat.
      repeat split; cbn; auto.
    + (* t_zero: similar. EvalRel zero ρ u = le u zero. *)
      move=> u Eu. cbn in Eu.
      exists zero, tnat, wt_zero.
      repeat split; cbn; auto.
    + (* t_succ M : tnat (given M : tnat). *)
      have ihM : InvTyped Γ M Core.tnat ρ by eapply typing_EvalRel; eauto.
      move=> u Eu.
      destruct (Raw.is_bot u) eqn:HU.
      { (* u = bot *) destruct u; try done. apply Typed_bot. }
      cbn in Eu. rewrite HU in Eu.
      destruct Eu as [Vu [a [LE EMa]]].
      (* u non-bot, le u (succ a), EvalRel M ρ a. *)
      specialize (ihM a EMa).
      destruct ihM as [v [a' [WTva [LEav [EMv EA]]]]].
      cbn in EA.
      (* a' is the type-elt for M, EvalRel tnat ρ a' = le a' tnat, so a' ∈ {bot, tnat}.
         We need to take v' = succ v, a'' = tnat. *)
      have Vv : valid v by eapply wt_valid_tm; eauto.
      have Va : valid a by eapply EvalRel_valid; eauto.
      (* Get wt v tnat: a' is bot or tnat.  Either gives wt v tnat by cumulativity
         (wt_le).  Since wt v a' with a' ≤ tnat and wt tnat tuniv (and a' tuniv too),
         we get wt v tnat. *)
      have WTv_tnat : wt v tnat.
      { destruct a'; try done.
        apply wt_bot_inv in WTva. subst v.
        eapply wt_bot; eapply wt_tnat. }
      have LEsv : le u (succ v).
      { (* u is non-bot succ-something (from le u (succ a)), and v ≥ a (LEav). *)
        destruct u; try done.
        cbn in Vu.
        rewrite le_succ. rewrite le_succ in LE.
        eapply le_trans; [exact Vu | exact Va | exact Vv | exact LE | exact LEav]. }
      exists (succ v), tnat, (wt_succ WTv_tnat).
      split; first exact LEsv.
      split.
      { (* EvalRel (succ M) ρ (succ v) *)
        cbn.
        split; first by rewrite Vv.
        exists v. split; first by eapply le_refl. exact EMv. }
      cbn. done.
    + (* t_case — soundness of case analysis (InvTyped for ncase). *)
      have Vρ : valid_env ρ := fits_valid_env Fρ.
      move=> u Eu.
      move: Eu => [w [EM Hb]].
      destruct w as [ | | | | vp | | ]; cbn in Hb; try contradiction.
      * (* bot: u = bot *)
        move: Hb => [_ Lu]. apply le_bot_inv in Lu; subst u. apply Typed_bot.
      * (* zero: use the zero-branch soundness, bridging T[M..] <-> T[zero..]
           since the scrutinee M evaluates to zero. *)
        have ihM0 : InvTyped Γ M0 (T[Core.zero..]) ρ by (eapply typing_EvalRel; eauto).
        move: (ihM0 u Hb) => [v0 [a0 [h0 [Lu0 [EM0v0 ETa0]]]]].
        move: (EvalRel_subst1_forward Vρ ETa0) => [vz [Ezvz ETvz]].
        have Vvz : valid vz := EvalRel_valid Ezvz.
        cbn in Ezvz.
        have EMvz : EvalRel M ρ vz
          by (eapply EvalRel_down; [ exact Vρ | exact Vvz | exact EM | exact Ezvz ]).
        have ETM : EvalRel (T[M..]) ρ a0 := EvalRel_subst1_backwards Vρ EMvz ETvz.
        exists v0, a0, h0. split; [ exact Lu0 | split; [ | exact ETM ] ].
        cbn. eexists. split; [ exact EM | exact EM0v0 ].
      * (* succ vp — TODO: needs the [rho] lift-substitution semantics
           (T[rho] at (vp .: ρ) vs T[M..] at ρ) and the predecessor's typing. *)
        admit.
    + (* t_tpi: tpi A B : tuniv *)
      move: ρ Fρ.
      eapply InvTyp_Pi; eauto.
    + (* t_univ: tuniv : tuniv (type-in-type). *)
      move=> u Eu. cbn in Eu.
      exists tuniv, tuniv, wt_tuniv.
      repeat split; cbn; auto.
  - destruct h as
      [ ?n ?Γ ?M ?N ?A ?B hMNA hAB
      | ?n ?Γ ?M ?A hM
      | ?n ?Γ ?M ?N ?A hMN
      | ?n ?Γ ?M ?N ?P ?A hMN hNP
      | ?n ?Γ ?A ?B ?N ?N' ?M hA hB hNN' hM
      | ?n ?Γ ?A ?B ?N ?M ?M' hA hB hN hMM'
      | ?n ?Γ ?A ?B ?M ?N hA hB hM hN
      | ?n ?Γ ?A ?B ?N ?N' hA hN hN' hbody
      | ?n ?Γ ?M0 ?M1 ?T hT hM0 hM1
      | ?n ?Γ ?T ?M0 ?M1 ?N hT hN hM0 hM1
      | ?n ?Γ ?T ?M ?M0 ?M1 ?M' ?M0' ?M1' hT hMc hM0c hM1c
      | ?n ?Γ ?M ?N hMN
      | ?n ?Γ ?A ?A' ?B ?M ?M' TAc TA'c TBc TMc TM'c hAconv hMconv
      | ?n ?Γ ?A0 ?A1 ?B0 ?B1 hA hB ].
    all: move=> ρ Fρ.
    + (* c_conv: M = N : A, A = B : U_i ⟹ M = N : B *)
      move: ρ Fρ.
      eapply InvConv_conv; eauto. 
    + (* c_refl *)
      eapply InvConv_refl'. exact (typing_EvalRel _ _ _ _ hM ρ Fρ).
    + (* c_sym: from conv Γ M N A get InvConv Γ N M A by swapping components. *)
      have ih : InvConv Γ M N A ρ by eapply conv_EvalRel; eauto.
      move: ih => [iM [iN [fwd bwd]]].
      unfold InvConv. repeat split; eauto.
    + (* c_trans *)
      apply (@InvConv_trans _ Γ M N P A ρ).
      * exact (conv_EvalRel _ _ _ _ _ hMN ρ Fρ).
      * exact (conv_EvalRel _ _ _ _ _ hNP ρ Fρ).
    + (* c_app1: N = N' : Pi A B, M : A ⟹ app N M = app N' M : B[M..] *)
      apply (@InvConv_App_fun _ Γ A B N N' M ρ Fρ).
      * exact (conv_EvalRel _ _ _ _ _ hNN' ρ Fρ).
      * exact (typing_EvalRel _ _ _ _ hM ρ Fρ).
    + (* c_app2: N : Pi A B, M = M' : A ⟹ app N M = app N M' : B[M..] *)
      apply (@InvConv_App_arg _ Γ A B N M M' ρ Fρ).
      * exact (typing_EvalRel _ _ _ _ hN ρ Fρ).
      * exact (conv_EvalRel _ _ _ _ _ hMM' ρ Fρ).
    + (* c_beta: M is the argument (Tm n), N is the body (Tm (S n));
         destruct order follows the rule c_beta's variables. *)
      apply (@InvConv_beta _ Γ A B N M ρ Fρ).
      * exact (typing_EvalRel _ _ _ _ hN ρ Fρ).
      * exact (typing_EvalRel _ _ _ _ hA ρ Fρ).
      * move=> x a Wx Wa EA.
        apply (typing_EvalRel _ _ _ _ hM (x .: ρ)).
        eapply fits_cons; eauto.
    + (* c_eta: function extensionality (rests on the admitted [InvConv_eta]) *)
      move: ρ Fρ. eapply InvConv_eta;
        [ exact hA | exact hN | exact hN' | exact hbody
        | exact (typing_EvalRel _ _ _ _ hA)
        | exact (typing_EvalRel _ _ _ _ hN)
        | exact (typing_EvalRel _ _ _ _ hN')
        | exact (conv_EvalRel _ _ _ _ _ hbody) ].
    + (* c_ncase_Z: ncase zero M0 M1 ≡ M0 : T[zero..].  Conversion soundness for
         case reduction — TODO (mirrors the InvConv computation lemmas). *)
      admit.
    + (* c_ncase_S: ncase (succ N) M0 M1 ≡ M1[N..] : T[(succ N)..].  TODO. *)
      admit.
    + (* c_ncase: congruence on the scrutinee/branches.  TODO. *)
      admit.
    + (* c_succ *)
      apply InvConv_succ. exact (conv_EvalRel _ _ _ _ _ hMN ρ Fρ).
    + (* c_abs: lambda congruence *)
      move: ρ Fρ. eapply InvConv_abs; try eassumption.
      * exact (conv_EvalRel _ _ _ _ _ hAconv).
      * exact (typing_EvalRel _ _ _ _ TBc).
      * exact (conv_EvalRel _ _ _ _ _ hMconv).
    + (* c_tpi: tpi A0 B0 = tpi A1 B1 : tuniv i *)
      move: ρ Fρ.
      eapply InvConv_tpi; eauto.
(* [c_nrec_Z]/[c_nrec_S] cases admitted: nrec's EvalRel is a bot-only
   placeholder, so conversion soundness for nrec is not yet available. *)
Admitted.

