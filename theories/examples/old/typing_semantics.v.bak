(* See LemmaForTS.agda/TypingSemantics.agda *)

(* Prove that well typed syntax produces well typed interpretations.

   Theorem 1 (typing_EvalRel):
       Γ ⊢ M : A   and forall ρ, Fits Γ ρ  implies InvTyped Γ M A ρ
       i.e. for every u with EvalRel M ρ u, there exist v, a such that
       u ≤ v, EvalRel M ρ v, wt v a, and EvalRel A ρ a.

   Conversion soundness (conv_EvalRel):
       Γ ⊢ M = N : A   and   Fits Γ ρ
       implies   InvConv Γ M N A ρ
       i.e. InvTyped for both sides plus bidirectional EvalRel.

   This is the Rocq translation of the lemmas in
       agda/domain-semantics/TypingSemantics.agda
       agda/domain-semantics/LemmaForTS.agda

   Note: the Coq formulation differs from the Agda one in that we use
   [wt u a] (well-typedness) directly instead of the Agda [FinMem u a]
   relation against codes. This means many helper lemmas (Selection,
   replaceKeys, mapEdges, Pi-edgewise, etc.) from the Agda development
   are inlined into the EvalRel definitions and need not be repeated.
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

Open Scope syntax_scope.

Import Raw.

(* =====================================================================
   Part 1: Fits — well-typed finite environments

       ρ fits Γ if for all x : A in Γ we have
                [[A]]ρ in Type and ρ(x) in [[A]]ρ.

   See LemmaForTS.agda Part 1.
   ===================================================================== *)

Inductive fits : forall {n} (Γ:Ctx n) (ρ : Env n), Prop :=
  | fits_empty : fits ctx_empty null
  | fits_cons n (Γ : Ctx n) A ρ a u i :
       typing Γ A (Core.tuniv i) ->
       EvalRel A ρ a ->
       wt a (tuniv i) ->
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

(* Fits-var (LemmaForTS.agda): the value at every variable is well-typed
   at the lookup of its type. *)

Lemma fits_var {n} (Γ : Ctx n)(ρ : Env n) :
  fits Γ ρ ->
  forall x,
  exists a i (h: wt a (tuniv i)) (h2 : wt (ρ x) a),
    typing Γ (lookup x Γ) (Core.tuniv i) /\
    EvalRel (lookup x Γ) ρ a.
Proof.
  move=> h.
  induction h. done.
  auto_case.
  + destruct (IHh f) as [b [j [WT1 [WT2 [Ht E ]]]]].
    exists b. exists j. exists WT1. exists WT2.
    repeat split; auto.
    eapply renaming_typing with (A := Core.tuniv j);
      eauto with renaming.
    eapply c_cons; eauto using typing_ctx.
    eapply EvalRel_wk; eauto.
  + exists a. exists i. 
    repeat split; eauto.
    eapply renaming_typing with (A := Core.tuniv i);
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

Definition Typed {n:nat} (M : Tm n) (A : Tm n) ρ u :=
  exists v , exists a, exists (h : wt v a),
    le u v /\ EvalRel M ρ v /\ EvalRel A ρ a.

Definition InvTyped
  {n:nat} (Γ: Ctx n) (M : Tm n) (A : Tm n) (ρ : Env n) :=
  forall u, EvalRel M ρ u -> Typed M A ρ u.

Definition InvConv
  {n:nat} (Γ: Ctx n) (M : Tm n) (N: Tm n) (A : Tm n) (ρ : Env n) :=
  InvTyped Γ M A ρ
  /\ InvTyped Γ N A ρ
  /\ (forall u, EvalRel M ρ u -> EvalRel N ρ u)
  /\ (forall u, EvalRel N ρ u -> EvalRel M ρ u).

Local Notation "Γ ⊨ M ∈ A" := (forall ρ, fits Γ ρ -> InvTyped Γ M A ρ) (at level 70).
Local Notation "Γ ⊨ M ≡ N ∈ A" := (forall ρ, fits Γ ρ -> InvConv Γ M N A ρ) (at level 70).


Lemma Typed_bot {n} (M A : Tm n) (ρ : Env n) :
  Typed M A ρ bot.
Proof.
  exists bot. exists bot.
  repeat split; eauto using EvalRel_bot, wt_bot.
(*  eapply wt_bot. eapply wt_bot. eapply (@wt_tuniv 0 1). lia. *)
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
Lemma InvConv_conv {n} (Γ : Ctx n) (M N A B : Tm n) ρ :
  InvConv Γ M N A ρ ->
  (forall u, EvalRel A ρ u -> EvalRel B ρ u) ->
  InvConv Γ M N B ρ.
Proof.
  move=> [iM [iN [fwd bwd]]] convAB.
  unfold InvConv, InvTyped, Typed. repeat split.
  - move=> u Eu. specialize (iM u Eu).
    move: iM => [v [a [LE [EM [Wv EA]]]]].
    exists v, a. repeat split; eauto.
  - move=> u Eu. specialize (iN u Eu).
    move: iN => [v [a [LE [EN [Wv EA]]]]].
    exists v, a. repeat split; eauto.
  - eauto.
  - eauto.
Qed.

(* =====================================================================
   Lam_L1 (LemmaForTS.agda): Lam inversion with typed keys.

   If u ≤ ⟦Lam A M⟧ρ and u is not Bot, then there exists a, g, i such
   that EvalRel A ρ a, wt a (tuniv i), le u (abs g),
   EvalRel (abs A M) ρ (abs g), and for every (x,y) ∈ g, wt x a and
   EvalRel M (x .: ρ) y.

   This corresponds to the Lam-L1 lemma in LemmaForTS.agda which builds
   a replacement graph from the original via replaceKeys.

   In the Coq formulation EvalRel (abs A M) ρ (abs g) already gives us
   the "edgewise" property directly via lam_edgewise — the witness keys
   are already typed. So this lemma is essentially repackaging.
   ===================================================================== *)

(* Weaker form (matches what Coq's EvalRel for Lam directly provides):
   the per-edge witnesses give us, for each edge (x,y) in g, *some*
   z ≤ x with [wt z a] and EvalRel M (z .: ρ) y. The Agda Lam-L1 uses a
   replacement-graph construction to upgrade these to the keys
   themselves; that construction is not yet in the Coq development. *)

Lemma valid_abs f : 
  valid_fun f -> ~~ is_nil f -> valid (abs f).
Proof.
  move=> h1 h2.
  apply /andP. split; eauto.
Qed.

Hint Resolve valid_abs : valid.

Lemma Lam_L1 u {n} (A : Tm n) M ρ :
  EvalRel (Core.abs A M) ρ u ->
  valid_env ρ ->
  ~~ is_bot u ->
  exists a g i (h : wt a (tuniv i)),
    EvalRel A ρ a 
    /\ le u (abs g)
    /\ valid (abs g)
    /\ (forall x y, In (x,y) g ->
         exists z (hz: wt z a), le z x /\ EvalRel M (z .: ρ) y).
Proof.
  destruct u; try done.
  move=> h Vρ _.
  cbn in h.
  destruct h as [Vf [Nf [i [a [WT [E1 body]]]]]].
  exists a, l, i.
  repeat split; auto.
  - eapply le_refl. eauto with valid.
  - eauto with valid.
Qed.

(* =====================================================================
   Pi_L1 (LemmaForTS.agda): Pi inversion with typed keys.

   If EvalRel (Pi A B) ρ (tpi b f), then there exist a, f' with
   EvalRel A ρ a, wt a (tuniv i), le_fun f f',
   EvalRel (Pi A B) ρ (tpi a f'), and for every (x,y) ∈ f',
   wt x a and EvalRel B (x .: ρ) y.

   Just like Lam_L1, the Coq EvalRel for tpi already gives us the
   witnesses directly — but with key z ≤ ui rather than at ui itself.
   ===================================================================== *)

(* Weaker form (matches what Coq's EvalRel for Pi directly provides):
   the type-code witness [a] of the input [b] is just [b] itself, and
   per-edge witnesses give us, for each edge (x,y) in f, *some* z ≤ x
   with [wt z a] and EvalRel B (z .: ρ) y. *)

Lemma Pi_L1 {n} (A : Tm n) (B : Tm (S n)) ρ b f :
  EvalRel (Core.tpi A B) ρ (tpi b f) ->
  valid_env ρ ->
  exists a i (h : wt a (tuniv i)),
    EvalRel A ρ a /\ 
    le (tpi b f) (tpi a f) /\
    valid (tpi a f) /\
    (forall x y, In (x,y) f ->
       exists z (hz: wt z a), le z x /\ EvalRel B (z .: ρ) y).
Proof.
  move=> h Vρ.
  cbn in h.
  destruct h as [Vb [Vf [i [EA [Wb Hbody]]]]].
  exists b, i.
  have Vtpi : valid (tpi b f).
  { eapply valid_tpi_intro; eauto. } 
  split; first exact EA.
  split; first exact Wb.
  split; first by eapply le_refl; exact Vtpi.
  split; first exact Vtpi.
  move=> x y In_xy.
  eapply Hbody; eauto.
Qed.

(* =====================================================================
   InvTyp_Pi (LemmaForTS.agda): Pi case at universe level.

       If A has InvTyp at (tuniv i) and the body B has InvTyp at
       (tuniv i) in every typed extended environment, then (Pi A B) has
       InvTyp at (tuniv i).
   ===================================================================== *)

Lemma InvTyp_Pi {n} (Γ : Ctx n) (A : Tm n) (B : Tm (S n)) i ρ :
  fits Γ ρ ->
  InvTyped Γ A (Core.tuniv i) ρ ->
  (forall x a, wt x a -> wt a (tuniv i) -> EvalRel A ρ a ->
    InvTyped (Γ ++ A) B (Core.tuniv i) (x .: ρ)) ->
  InvTyped Γ (Core.tpi A B) (Core.tuniv i) ρ.
Proof.
  move=> Fρ IHA IHB u Eu.
  destruct u; try solve [cbn in Eu; done].
  { (* u = bot *) apply Typed_bot. }
  (* u = tpi b f *)
  cbn in Eu.
  destruct Eu as [Vb [Vf [j [WTbj [EAb Hbody]]]]].
  (* Apply IHA to enlarge the type code b to b', well-typed at tuniv i *)
  destruct (IHA _ EAb) as [b' [c [WTb'c [LEbb' [EAb'  LEcuniv]]]]].
  cbn in LEcuniv.
  have Vb' : valid b' by eapply EvalRel_valid; exact EAb'.
  have Vti : valid (tuniv i) by [].
  have WTb' : wt b' (tuniv i). eapply wt_le; eauto. admit. admit.
  (* For each edge (ui, vi) ∈ l, the per-edge witness xi has wt xi b,
     hence wt xi b' by wt_le. Applying IHB at (xi, b') gives a typed
     enlargement vi' of vi with wt vi' (tuniv i).
     Building a coherent replacement graph f' = [(xi, vi') | ...] then
     yields the witness v = tpi b' f' for the InvTyp goal. The graph
     properties (compatibility, no_bot_result, le_fun f f') need
     replaceKeys-style helpers from the Agda development that have not
     yet been ported to Coq. *)
Admitted.

(* =====================================================================
   InvTyp_Lam (LemmaForTS.agda): Lambda case.

       If for every typed extended environment, the body M has InvTyp
       at B, then (Lam A M) has InvTyp at (Pi A B).
   ===================================================================== *)



Lemma InvTyp_Lam' {n} (Γ : Ctx n) (A : Tm n) (B : Tm (S n)) (M : Tm (S n))
  i :
  Γ ⊨ A ∈ Core.tuniv i ->
  Γ ++ A ⊨ B ∈ Core.tuniv i ->
  Γ ++ A ⊨ M ∈ B ->
  Γ ⊨ (Core.abs A M) ∈ Core.tpi A B.
Proof.
  move=> TA TB TM.
  move=> ρ Fρ u EL.
  specialize (TA _ Fρ). unfold InvTyped in TA.
  have Vρ : valid_env ρ. eauto with valid.
  destruct (~~ is_bot u) eqn:Bu.
  - destruct (Lam_L1 EL Vρ Bu) as 
      (a & g & i0 & WTa & EA &  LEu & Vg & h).
    clear EL.
    specialize (TA _ EA). unfold Typed in TA.
Admitted.

Lemma InvTyp_Lam {n} (Γ : Ctx n) (A : Tm n) (B : Tm (S n)) (M : Tm (S n))
  i ρ :
  fits Γ ρ ->
  InvTyped Γ A (Core.tuniv i) ρ ->
  (forall x a, wt x a -> wt a (tuniv i) -> EvalRel A ρ a ->
    InvTyped (Γ ++ A) B (Core.tuniv i) (x .: ρ)) ->
  (forall x a, wt x a -> wt a (tuniv i) -> EvalRel A ρ a ->
    InvTyped (Γ ++ A) M B (x .: ρ)) ->
  InvTyped Γ (Core.abs A M) (Core.tpi A B) ρ.
Proof.
  (* Translates LemmaForTS.InvTyp-Lam.

     Outline:
       - Case u = bot: Typed_bot.
       - Case u = abs g: by Lam_L1 we can replace the keys of g with
         typed witnesses; then for each (xi,yi) we apply the body IH to
         get a typed enlargement (yi', bi). The graph of (xi, yi') is
         the witness, and (Pi A (a, f)) is its type code. *)
Admitted.

(* =====================================================================
   InvTyp_App (LemmaForTS.agda): Application case.

       If M has InvTyp at (Pi A B) and N has InvTyp at A, then
       (App M N) has InvTyp at B[N..].
   ===================================================================== *)

Lemma InvTyp_App {n} (Γ : Ctx n) (A : Tm n) (B : Tm (S n))
  (M : Tm n) (N : Tm n) ρ :
  fits Γ ρ ->
  InvTyped Γ M (Core.tpi A B) ρ ->
  InvTyped Γ N A ρ ->
  InvTyped Γ (Core.app M N) B[N..] ρ.
Proof.
  (* Translates LemmaForTS.InvTyp-App.

     Outline:
       Given EvalRel (app M N) ρ u with u not bot, there is some w
       with EvalRel N ρ w and EvalRel M ρ (w ↦ u). Apply InvM to get
       a typed enlargement (h, piaf) of (w ↦ u). Case-split on h and
       piaf: must be h = abs g' and piaf = tpi a f. Then apply Lemma 4
       (lemma4_2 / wt_app) to the typed graph to get
       wt v0 (EvalFun f w0) where w0 ≤ w. Conclude with
       EvalRel_subst1_backwards. *)
Admitted.

(* =====================================================================
   InvConv_App_fun (LemmaForTS.agda): App congruence on the function.

       If M = N : Pi A B and a : A, then App M a = App N a : B[a..].

   This one *is* tractable in the current Coq formulation, because the
   forward/backward EvalRel directions are pure unfolding of EvalRel for
   App — no graph reconstruction is needed.
   ===================================================================== *)

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
   InvConv_Pi (TypingSemantics.agda conv-Pi case):
       A = A' : U and B = B' : U  ⟹  Pi A B = Pi A' B' : U.
   ===================================================================== *)

Lemma InvConv_Pi {n} (Γ : Ctx n) (A A' : Tm n) (B B' : Tm (S n)) i ρ :
  fits Γ ρ ->
  InvConv Γ A A' (Core.tuniv i) ρ ->
  (forall x a, wt x a -> wt a (tuniv i) -> EvalRel A ρ a ->
    InvConv (Γ ++ A) B B' (Core.tuniv i) (x .: ρ)) ->
  InvConv Γ (Core.tpi A B) (Core.tpi A' B') (Core.tuniv i) ρ.
Proof.
  (* Translates TypingSemantics.convSound' for conv-Pi.

     Forward/backward use convSound-Pi-fwd which case-splits on the Pi
     witness and applies the IH on A and B (inside the extended context)
     pointwise. InvTyp uses InvTyp_Pi. *)
Admitted.

(* =====================================================================
   InvConv_beta (LemmaForTS.agda): Beta conversion.

       Γ ⊢ A : U_i, (Γ++A) ⊢ B : U_j, (Γ++A) ⊢ M : B, Γ ⊢ N : A
       ⟹  app (abs A M) N  =  M[N..]  :  B[N..]
   ===================================================================== *)

Lemma InvConv_beta {n} (Γ : Ctx n) (A : Tm n) (B : Tm (S n))
  (M : Tm (S n)) (N : Tm n) i ρ :
  fits Γ ρ ->
  InvTyped Γ N A ρ ->
  InvTyped Γ A (Core.tuniv i) ρ ->
  (forall x a, wt x a -> wt a (tuniv i) -> EvalRel A ρ a ->
    InvTyped (Γ ++ A) M B (x .: ρ)) ->
  InvConv Γ (Core.app (Core.abs A M) N) M[N..] B[N..] ρ.
Proof.
  (* Translates LemmaForTS.InvConv-beta.

     Forward (subst1 M N → App (Lam A M) N):
       From EvalRel M[N..] ρ u, EvalRel_subst1_forward gives v with
       EvalRel N ρ v and EvalRel M (v .: ρ) u. Build a singleton-graph
       Lam witness FunEl [(y, u)] from typed enlargement of v.

     Backward (App (Lam A M) N → subst1 M N):
       App-decompose plus lam_edgewise gives a typed witness z ≤ v with
       EvalRel M (z .: ρ) u, then EvalRel_subst1_backwards.

     InvTyp pieces: chain InvTyp_Lam → InvTyp_App and use the conversion
     between App and subst1 on the typed enlargements. *)
Admitted.

(* =====================================================================
   InvConv_funext (LemmaForTS.agda): Function extensionality.

       Γ ⊢ A : U, (Γ++A) ⊢ B : U, Γ ⊢ M : Pi A B, Γ ⊢ N : Pi A B
       (Γ++A) ⊢ App M⟨↑⟩ var0 = App N⟨↑⟩ var0 : B
       ⟹  M = N : Pi A B
   ===================================================================== *)

Lemma InvConv_funext {n} (Γ : Ctx n) (A : Tm n) (B : Tm (S n))
  (M N : Tm n) i ρ :
  fits Γ ρ ->
  InvTyped Γ A (Core.tuniv i) ρ ->
  InvTyped Γ M (Core.tpi A B) ρ ->
  InvTyped Γ N (Core.tpi A B) ρ ->
  (forall x a, wt x a -> wt a (tuniv i) -> EvalRel A ρ a ->
    InvConv (Γ ++ A) (Core.app M⟨↑⟩ (var var_zero))
                     (Core.app N⟨↑⟩ (var var_zero))
                     B (x .: ρ)) ->
  InvConv Γ M N (Core.tpi A B) ρ.
Proof.
  (* Translates LemmaForTS.InvConv-funext.

     The forward direction (M → N): from u ≤ ⟦M⟧ρ, use InvM to get a
     typed enlargement at (Pi A B). Case-split on the witness; in the
     non-bot case it must be (abs g'); for each edge (ui, vi) of g',
     build per-edge App evidence at M, apply the IH (App-conversion at
     edge), then decompose to get edge evidence at N. Re-assemble via
     EvalRel_sup.

     Backward (N → M) is symmetric. *)
Admitted.

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
      move: (fits_var Fρ x) => [a [i [hT [Ea [WT1 WT2]]]]].
      exists (ρ x). exists a.
      repeat split;
      eauto using le_refl, EvalRel_valid with valid.
    + (* t_conv *)
      have ihM : InvTyped Γ M A ρ by eapply typing_EvalRel; eauto.
      have ihAB : InvConv Γ A B (Core.tuniv i) ρ
        by eapply conv_EvalRel; eauto.
      move: ihAB => [_ [_ [fwdAB _]]].
      move=> u Eu. specialize (ihM u Eu).
      move: ihM => [v [a [LE [EM [Wv EA]]]]].
      exists v, a. repeat split; eauto.
    + (* t_abs *)
      apply (@InvTyp_Lam _ _ _ _ _ i _ Fρ).
      * exact (typing_EvalRel _ _ _ _ h1 ρ Fρ).
      * move=> x a Wx Wa EA.
        apply (typing_EvalRel _ _ _ _ h2 (x .: ρ)).
        eapply fits_cons; eauto.
      * move=> x a Wx Wa EA.
        apply (typing_EvalRel _ _ _ _ h3 (x .: ρ)).
        eapply fits_cons; eauto.
    + (* t_app *)
      apply (@InvTyp_App _ Γ A B N M ρ Fρ).
      * exact (typing_EvalRel _ _ _ _ h3 ρ Fρ).
      * exact (typing_EvalRel _ _ _ _ h4 ρ Fρ).
    + (* t_nat: tnat : tuniv 0 — natural numbers cases not in Agda;
         they require additional invariant for the type code (the
         "self-typing" of tnat at every universe level). Admit. *)
      admit.
    + (* t_zero *)
      admit.
    + (* t_succ *)
      admit.
    + (* t_nrec — nrec is a fake case in EvalRel: only produces bot. *)
      admit.
    + (* t_tpi: tpi A B : tuniv i *)
      apply (@InvTyp_Pi _ Γ A B i ρ Fρ).
      * exact (typing_EvalRel _ _ _ _ h1 ρ Fρ).
      * move=> x a Wx Wa EA.
        apply (typing_EvalRel _ _ _ _ h2 (x .: ρ)).
        eapply fits_cons; eauto.
    + (* t_cum: A : tuniv i, i < j ⟹ A : tuniv j — requires that the
         universe code Tuniv j can be enlarged from Tuniv i. Admit. *)
      admit.
    + (* t_univ *)
      admit.
  - destruct h as
      [ ?n ?Γ ?M ?N ?A ?B ?i hMNA hAB
      | ?n ?Γ ?M ?A hM
      | ?n ?Γ ?M ?N ?A hMN
      | ?n ?Γ ?M ?N ?P ?A hMN hNP
      | ?n ?Γ ?A ?B ?N ?N' ?M ?i hA hB hNN' hM
      | ?n ?Γ ?A ?B ?N ?M ?M' ?i hA hB hN hMM'
      | ?n ?Γ ?A ?B ?M ?N ?i hA hB hM hN
      | ?n ?Γ ?A ?B ?N ?N' ?i hA hB hN hN' hbody
      | ?n ?Γ ?M0 ?M1 ?T ?i hT hM0 hM1
      | ?n ?Γ ?T ?M0 ?M1 ?z ?i hT hM0 hM1
      | ?n ?Γ ?M ?N ?i ?j hMN ?Lij
      | ?n ?Γ ?A0 ?A1 ?B0 ?B1 ?i hA hB ].
    all: move=> ρ Fρ.
    + (* c_conv: M = N : A, A = B : U_i ⟹ M = N : B *)
      apply (@InvConv_conv _ Γ M N A B ρ).
      * exact (conv_EvalRel _ _ _ _ _ hMNA ρ Fρ).
      * move: (conv_EvalRel _ _ _ _ _ hAB ρ Fρ) => [_ [_ [fwd _]]].
        exact fwd.
    + (* c_refl *)
      eapply InvConv_refl'. exact (typing_EvalRel _ _ _ _ hM ρ Fρ).
    + (* c_sym *)
      admit.
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
      apply (@InvConv_beta _ Γ A B N M i ρ Fρ).
      * exact (typing_EvalRel _ _ _ _ hN ρ Fρ).
      * exact (typing_EvalRel _ _ _ _ hA ρ Fρ).
      * move=> x a Wx Wa EA.
        apply (typing_EvalRel _ _ _ _ hM (x .: ρ)).
        eapply fits_cons; eauto.
    + (* c_eta: function extensionality at type A⟨↑⟩, see Admitted note. *)
      admit.
    + (* c_nrec_Z and c_nrec_S: nrec is fake, so both sides only produce
         bot in EvalRel. *)
      admit.
    + admit.
    + (* c_tuniv *)
      admit.
    + (* c_tpi: tpi A0 B0 = tpi A1 B1 : tuniv i *)
      apply (@InvConv_Pi _ Γ A0 A1 B0 B1 i ρ Fρ).
      * exact (conv_EvalRel _ _ _ _ _ hA ρ Fρ).
      * move=> x a Wx Wa EA.
        apply (conv_EvalRel _ _ _ _ _ hB (x .: ρ)).
        (* Need a typing of A0 to extend the context via fits_cons. The
           rule c_tpi only provides conv Γ A0 A1 (tuniv i), not a typing.
           Recovering the typing requires inverting conv into a typing of
           A0, which the conv rules in the system don't directly give. *)
        admit.
Admitted.

(*
Lemma typing_EvalRel' {n} (Γ : Ctx n) (M : Tm n) (A : Tm n)
  (h : typing Γ M A) :
  forall ρ, fits Γ ρ -> exists a, EvalRel M ρ a.
Proof.
  move=> ρ F.
  move: (typing_EvalRel h F) => h1. 
  unfold InvTyped in h1. unfold Typed in h1.
*)
