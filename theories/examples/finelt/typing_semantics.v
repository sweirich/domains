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

(* Fits-var (LemmaForTS.agda): the value at every variable is well-typed
   at the lookup of its type. *)

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


Definition Typed {n:nat} (M : Tm n) (A : Tm n) ρ u :=
  exists v , exists a, exists (h : wt v a),
    le u v /\ EvalRel M ρ v /\ EvalRel A ρ a.


(* This is not flexible enough. 
Definition Typed {n:nat} (M : Tm n) (A : Tm n) ρ u :=
  exists a, exists (h : wt u a), EvalRel A ρ a.
*)

Definition InvTyped
  {n:nat} (Γ: Ctx n) (M : Tm n) (A : Tm n) (ρ : Env n) :=
  forall u, EvalRel M ρ u -> Typed M A ρ u.

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
Admitted.
(*
    move: iM => [v [a [LE [EM [Wv EA]]]]].
    exists v, a. repeat split; eauto.
  - move=> u Eu. specialize (iN u Eu).
    move: iN => [v [a [LE [EN [Wv EA]]]]].
    exists v, a. repeat split; eauto.
  - eauto.
  - eauto.
Qed. *)

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
  destruct (compatible_lub_exists Ca) as [a LUBa].
  destruct (compatible_lub_exists Cfg) as [h LUBh].
  cbn [compatible] in Cfg.
  fold (compatible_fun f1 g1) in Cfg.
  destruct a1; try done. inversion WT1.
  destruct a2; try done. inversion WT2.
  destruct EA1 as [Va1 [Vl1 [Ea1 [a1' [Ea1' h1]]]]].
  destruct EA2 as [Va2 [Vl2 [Ea2 [a2' [Ea2' h2]]]]].
  cbn in Ca. move: Ca => /andP. move=> [Ca Cl].
  fold (compatible_fun l l0) in Cl.
  cbn in LUBa. rewrite Cl in LUBa. destruct (lub a1 a2) as [|a3] eqn:EQ; inversion LUBa. subst a.
  clear LUBa.
Admitted.

Lemma InvTyp_Lam {n} (Γ : Ctx n) (A : Tm n) (B : Tm (S n)) (M : Tm (S n)) :
  typing Γ A Core.tuniv ->
  typing (Γ ++ A) B  Core.tuniv ->
  typing (Γ ++ A) M B ->
  Γ ⊨ A ∈ Core.tuniv ->
  Γ ++ A ⊨ B ∈ Core.tuniv ->
  Γ ++ A ⊨ M ∈ B ->
  Γ ⊨ (Core.abs A M) ∈ Core.tpi A B.
Proof.
  move=> tA tB tM TA TB TM.
  move=> ρ Fρ u EL.
  specialize (TA _ Fρ). unfold InvTyped in TA.
  have Vρ : valid_env ρ. eauto with valid.

  destruct (~~ is_bot u) eqn:Bu.
  2: { destruct u; try done.
       eapply Typed_bot; eauto.
  } 
  destruct u ; try done.
  cbn in EL.
  destruct EL as [Vl [NBl [a [WTa [ERa ERl]]]]].
  specialize (TA _ ERa).
  have Va: valid a. eapply EvalRel_valid; eauto.
  destruct TA as [av [ax [WTav [LEav [ERav ERax]]]]].
  induction l as [|[ui vi]l]. done.
  clear NBl Bu.
  destruct (is_nil l) eqn:Nl.
  - destruct l; try done.
    cbn in IHl. clear IHl.
    have Vui: valid ui. eauto with valid.
    have Vvi: valid vi. eauto with valid.
    specialize (ERl ui vi Vui).
    destruct ERl as [x [WTx [LEx ERvi]]].
    rewrite app_cons_eq. rewrite compatible_refl; auto. rewrite le_refl; auto.
    cbn. rewrite lub_bot_r. done.
    have FE: fits (Γ ++ A) (x .: ρ).
    { eapply fits_cons; eauto. } 
    specialize (TB _ FE). 
    specialize (TM _ FE _ ERvi). 
    destruct TM as [t [tx [WTvi [LEtx h]]]].
    destruct (is_bot t) eqn:IBu.
    { destruct t; try done. destruct vi; try done.
      unfold valid_fun in Vl. cbn in Vl.
      rewrite compatible_refl in Vl; eauto. cbn in Vl. done. } 
    destruct (is_bot tx) eqn:IBtx.
    { destruct tx; try done. inversion WTvi. subst. done. } 
    have Vt: valid t. eapply EvalRel_valid; eauto.
    have Vx: valid x. eapply wt_valid_tm; eauto.
    have Vtx: valid tx. eapply wt_valid_ty; eauto.
    have Vg : valid (tpi a ((x, tx):: nil)).
    { cbn. rewrite Va. repeat rewrite compatible_refl; eauto.
      rewrite Vx. rewrite Vtx. destruct tx; try done. } 
    have WTpi: wt (tpi a ((x, tx) :: nil)) tuniv.
    { 
      eapply wt_tpi; eauto.
      + (* everything in domain is well-typed *)
        intros uj vj InX. inversion InX as [C|C]; inversion C.
        subst. auto.
      + intros uj vj InX.
        inversion InX as [C|C]; inversion C.
        subst.
        eapply wt_ty_tuniv. eauto.
    } 
    have Vfxt : valid_fun ((x, t) :: nil).
    { unfold valid_fun. cbn. repeat rewrite compatible_refl; eauto.
      rewrite Vx. rewrite Vt.
      destruct t; try done.
    } 
    have Vfxtx : valid_fun ((x, tx) :: nil).
    { unfold valid_fun. cbn. repeat rewrite compatible_refl; eauto.
      rewrite Vx. rewrite Vtx.
      destruct tx; try done.
    } 
    have WTabs: wt (abs ((x,t)::nil)) (tpi a ((x,tx) :: nil)).
    { 
      eapply wt_abs; eauto.
      + intros uj vj InG. inversion InG as [C|C]; inversion C.
        subst uj. subst vj. auto.
      + intros uj vj tj InG APPg. inversion InG as [C|C]; inversion C.
        subst uj. subst vj. 
        rewrite app_cons_eq in APPg. rewrite compatible_refl in APPg; eauto. 
        rewrite le_refl in APPg; eauto.
        cbn in APPg. rewrite lub_bot_r in APPg. inversion APPg. subst tj.
        auto.
      + eapply valid_abs; eauto. 
    } 
    clear Nl.
    eexists. eexists. exists WTabs.
    repeat split; auto.
    + rewrite le_abs. 
      rewrite le_fun_cons.
      rewrite app_cons_eq.
      rewrite LEx. 
      rewrite (le_valid_compatible Vui LEx).
      cbn. 
      rewrite lub_bot_r. rewrite LEtx. done.
    + cbn in ERax.
      destruct ax eqn:Bax; try done. 
      ++ (* x is bot *)
        inversion WTav. subst. apply le_bot_inv in LEav. subst.
        inversion WTx. subst.
        exists bot. exists ltac:(eapply wt_bot; eapply wt_tuniv).
        split. eapply EvalRel_bot.
        intros u v Vu APP.  exists bot. exists ltac: (eapply wt_bot; eapply wt_bot; eapply wt_tuniv).
        rewrite app_cons_eq in APP. 
        rewrite le_bot in APP. cbn in APP.
        have EQ: t = v. { destruct u; cbn in APP; rewrite lub_bot_r in APP; inversion APP; done. } 
        subst t.
        rewrite le_bot. split; eauto. 
      ++ (* ax is tuniv *)
        subst ax.
        exists a. eexists. eauto.
        split; auto.
        intros u v Vu APP. 
        rewrite app_cons_eq in APP.
        cbn in APP.
        rewrite lub_bot_r in APP.
        destruct (compatible x u && le x u) eqn:IN; inversion APP; subst.
        move: IN => /andP. move=> [Cxu LExu]. 
        exists x. repeat split; eauto. 
        exists bot. repeat split; eauto. eapply wt_bot; eauto.
        rewrite le_bot. done. eapply EvalRel_bot.
    + exists a. split. auto.
      intros u v Vu APP.
      rewrite app_cons_eq in APP.
      cbn in APP. rewrite lub_bot_r in APP.
      destruct (compatible x u && le x u) eqn:IN; inversion APP; subst. clear APP.
      move: IN => /andP. move=> [Cxu LExu]. 
      exists x. repeat split; eauto.  
      exists bot. repeat split; eauto. eapply wt_bot; eauto. rewrite le_bot.  done.
      eapply EvalRel_bot; eauto.
  - (* induction case *)
    have Vtl: valid_fun l. eauto with valid.
    specialize (IHl Vtl ltac:(done)). 
    destruct IHl as [v [vt [WTv [LEv [ERabs ERpi]]]]].
    { intros u v Vu APP.
      have Vv: valid v. eapply valid_app; eauto.
      specialize (ERl u).
      rewrite app_cons_eq in ERl.
      rewrite APP in ERl.
      have Vui: valid ui. admit.
      have Vvi: valid vi. admit.
      destruct (compatible ui u && le ui u) eqn:IN.
      { move: IN => /andP. move=> [Cu LEu]. 
        have Chw: coherent_with l (ui,vi). eauto with valid.
        move: (Comp_value_app Cu Chw APP) => Cv.
        destruct (compatible_lub_exists Cv) as [w EQ].
        have Vw: valid w. eapply (@valid_lub vi v); eauto.
        specialize (ERl w Vu EQ).
        destruct ERl as [x [WTx LEx]].
        exists x. split; eauto. split; eauto.
        eapply EvalRel_down; eauto.
        eauto with valid.
        eapply le_lub_right; eauto.
      } 
      specialize (ERl v Vu ltac:(eauto)).
      eapply ERl.
    } 
    cbn. done.
    apply le_abs_inv in LEv.
    destruct LEv as [g [EQ LEf]]. subst v.
Admitted.    



(* =====================================================================
   InvTyp_Pi (LemmaForTS.agda): Pi case at universe level.

       If A has InvTyp at (tuniv i) and the body B has InvTyp at
       (tuniv i) in every typed extended environment, then (Pi A B) has
       InvTyp at (tuniv i).
   ===================================================================== *)

Lemma InvTyp_Pi {n} (Γ : Ctx n) (A : Tm n) (B : Tm (S n)) :
  typing Γ A Core.tuniv -> 
  typing (Γ ++ A) B Core.tuniv -> 
  Γ ⊨ A ∈ Core.tuniv -> 
  (Γ ++ A) ⊨ B ∈ Core.tuniv -> 
  Γ ⊨ (Core.tpi A B) ∈ Core.tuniv.
Proof.
  move=> TA TB IHA IHB ρ Fρ u Eu.
  destruct u; try solve [cbn in Eu; done].
  { (* u = bot *) apply Typed_bot. }
  (* u = tpi u l *)
  cbn in Eu.
  destruct Eu as [Vb [Vf [EAb [u' [EAu'  Hbody]]]]].

  (* Apply IHA to enlarge the type code b to b', well-typed at tuniv *)
  unfold InvTyped in IHA.
  destruct (IHA _ Fρ _ EAb) as [b' [c [WTb'c [LEbb' [EAb'  LEcuniv]]]]].
  cbn in LEcuniv.
  have Vb' : valid b' by eapply EvalRel_valid; exact EAb'.
  have Vti : valid tuniv by [].
  have WTb' : wt b' tuniv. { eapply wt_le; eauto. eapply wt_ty_tuniv; eauto. eapply wt_tuniv. }  

  induction l; unfold Typed.
  - have WTpi : wt (tpi b' nil) tuniv.
    { econstructor; eauto.
      intros ? ? h. inversion h.
      intros ? ? h. inversion h.
      cbn. rewrite Vb'. done.
    }       
    exists (tpi b' nil). exists tuniv. split. eauto.
    split. rewrite le_tpi. rewrite LEbb'. rewrite le_fun_nil. done.
    split. cbn. 
    repeat split; auto.
    exists u'. split; auto. cbn. done.
  - destruct a as [ui vi].
    have Vvi: valid vi. admit.
    have Vl: valid_fun l. eapply valid_fun_tail; eauto.
    destruct (IHl Vl) as [tt T2].
    { intros uj vj Vuj APP.
      have Vvj: valid vj. eapply valid_app; eauto.
      specialize (Hbody uj).
      destruct (valid_app_exists Vf Vuj) as [w [APP2 Vw]].
      rewrite app_cons_eq in APP2.
      rewrite APP in APP2.
      destruct (compatible ui uj && le ui uj) eqn:CC.
      + specialize (Hbody w Vuj).
        destruct Hbody as [x [WTx [LEx Ew]]].
        rewrite app_cons_eq. rewrite CC. rewrite APP. done.
        exists x. exists WTx. split. auto. eapply EvalRel_down; eauto.
        eapply valid_cons; eauto. eapply wt_valid_tm; eauto.
        eapply fits_valid_env; eauto.
        eapply le_lub_right; eauto.
        eapply lub_compatible; eauto.
      + inversion APP2. subst.
        specialize (Hbody w Vuj).
        destruct Hbody as [x [WTx [LEx Ew]]].
        rewrite app_cons_eq. rewrite CC. done.
        exists x. exists WTx. split. auto. auto.
    } 
    destruct T2 as [a [WTtt [LEtt [ERpi ERuniv]]]].
    apply le_tpi_inv in LEtt. destruct LEtt as [w [g [EQ [LEuw LElg]]]].
    subst tt.
    (* now we have the results of the induction call *)
    clear IHl.
    cbn in ERpi.
    move: ERpi => [Vw [Vg [ERw [a' [ERa' h]]]]].
    cbn in ERuniv. destruct a; try done. inversion WTtt.

    have Vg2 : valid_fun ((ui, vi) :: g). admit.
    have WT2 : wt (tpi w ((ui, vi) :: g)) tuniv. admit.

    have Vui : valid ui. admit.
    destruct (valid_app_exists Vl Vui) as [w1 [APP1 Vw1]].
    destruct (valid_app_exists Vf Vui) as [w2 [APP2 Vw2]].
    rewrite app_cons_eq in APP2.  rewrite APP1 in APP2.
    rewrite compatible_refl in APP2; eauto.
    rewrite le_refl in APP2; eauto.
    cbn in APP2.
    destruct (Hbody ui w2 Vui) as [x [WTx [LEx EB]]].
    rewrite app_cons_eq. rewrite compatible_refl; eauto. rewrite le_refl; eauto. rewrite APP1.
    cbn. done.
    exists (tpi w ((ui, vi) :: g)). exists tuniv. split; auto.
    split. admit.     
    split. 2: eauto.
    cbn [EvalRel].
    repeat split; eauto.
    exists a'. split; eauto.
    intros uj w3 Vuj APP.
    rewrite app_cons_eq in APP.
    destruct (compatible ui uj && le ui uj) eqn:h1.
    destruct (app g uj) eqn:APP3; try done.
    specialize (h uj e Vuj APP3).
    destruct h as [x1 [WTx1 [LEx1 ERx1]]].
    have Cx: compatible x x1. admit.
    eapply compatible_lub_exists in Cx. destruct Cx as [w4 LUB].
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

Lemma InvConv_Pi {n} (Γ : Ctx n) (A A' : Tm n) (B B' : Tm (S n)) ρ :
  fits Γ ρ ->
  InvConv Γ A A' Core.tuniv ρ ->
  (forall x a, wt x a -> wt a tuniv -> EvalRel A ρ a ->
    InvConv (Γ ++ A) B B' Core.tuniv (x .: ρ)) ->
  InvConv Γ (Core.tpi A B) (Core.tpi A' B') Core.tuniv ρ.
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
  (M : Tm (S n)) (N : Tm n) ρ :
  fits Γ ρ ->
  InvTyped Γ N A ρ ->
  InvTyped Γ A Core.tuniv ρ ->
  (forall x a, wt x a -> wt a tuniv -> EvalRel A ρ a ->
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

Lemma InvConv_eta {n} (Γ : Ctx n) (A : Tm n) (B : Tm (S n))
  (N N' : Tm n) :
  typing Γ A Core.tuniv ->
  typing (Γ ++ A) B Core.tuniv ->
  typing Γ N (Core.tpi A B) ->
  typing Γ N' (Core.tpi A B) ->
  conv (Γ ++ A) (Core.app (⟨↑⟩ N) (var var_zero)) (Core.app (⟨↑⟩ N') (var var_zero)) (⟨↑⟩ A) ->
  Γ ⊨ A ∈ Core.tuniv ->
  Γ ++ A ⊨ B ∈ Core.tuniv ->
  Γ ⊨ N ∈ (Core.tpi A B) ->
  Γ ⊨ N' ∈ (Core.tpi A B) ->
  Γ ++ A ⊨ (Core.app (⟨↑⟩ N) (var var_zero)) ≡ (Core.app (⟨↑⟩ N') (var var_zero)) ∈ (⟨↑⟩ A) ->
  Γ ⊨ N ≡ N' ∈ (Core.tpi A B).
Admitted.
  (* Translates LemmaForTS.InvConv-funext.

     The forward direction (M → N): from u ≤ ⟦M⟧ρ, use InvM to get a
     typed enlargement at (Pi A B). Case-split on the witness; in the
     non-bot case it must be (abs g'); for each edge (ui, vi) of g',
     build per-edge App evidence at M, apply the IH (App-conversion at
     edge), then decompose to get edge evidence at N. Re-assemble via
     EvalRel_sup.

     Backward (N → M) is symmetric. *)

Lemma InvConv_nrec_Z : forall (n : nat) (Γ : Ctx n) (M0 M1 : Tm n) (T : Tm (S n)),
    typing (Γ ++ Core.tnat) T Core.tuniv ->
    typing Γ M0 T[Core.zero..] ->
    typing Γ M1 (Core.tpi Core.tnat (Core.tpi T (⟨↑⟩ T[rho]))) ->
    (Γ ++ Core.tnat)  ⊨ T ∈ Core.tuniv ->
    Γ  ⊨ M0 ∈ T[Core.zero..] ->
    Γ  ⊨ M1 ∈ (Core.tpi Core.tnat (Core.tpi T (⟨↑⟩ T[rho]))) ->
    Γ  ⊨ (Core.app (nrec T M0 M1) Core.zero) ≡ M0 ∈ T[Core.zero..].
Admitted.

Lemma InvConv_nrec_S : forall (n : nat) (Γ : Ctx n) (T : Tm (S n)) (M0 M1 n0 : Tm n),    
    typing (Γ ++ Core.tnat) T Core.tuniv ->
    typing Γ M0 T[Core.zero..] ->
    typing Γ M1 (Core.tpi Core.tnat (Core.tpi T (⟨↑⟩ T[rho]))) ->
    (Γ ++ Core.tnat) ⊨ T ∈ Core.tuniv ->
    Γ ⊨ M0 ∈ T[Core.zero..] ->
    Γ ⊨ M1 ∈ (Core.tpi Core.tnat (Core.tpi T (⟨↑⟩ T[rho]))) ->
    Γ ⊨ (Core.app (nrec T M0 M1) (Core.succ n0)) ≡ 
      (Core.app (Core.app M1 n0) (Core.app (nrec T M0 M1) n0)) ∈ T[(Core.succ n0)..].
Admitted.


Lemma InvConv_tpi : forall (n : nat) (Γ : Ctx n) (A0 A1 : Tm n) (B0 B1 : Tm (S n)),
    conv Γ A0 A1 Core.tuniv ->
    conv (Γ ++ A0) B0 B1 Core.tuniv -> 
    Γ ⊨ A0 ≡ A1 ∈ Core.tuniv ->
    (Γ ++ A0) ⊨ B0 ≡ B1 ∈ Core.tuniv -> 
    Γ ⊨ (Core.tpi A0 B0) ≡ (Core.tpi A1 B1) ∈ Core.tuniv.
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
    + (* t_nrec — nrec is a fake case in EvalRel: only produces bot. *)
      move=> u Eu. cbn in Eu.
      destruct (Raw.is_bot u) eqn:HU; first by destruct u; try done; apply Typed_bot.
      done.
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
      | ?n ?Γ ?A ?B ?N ?N' hA hB hN hN' hbody
      | ?n ?Γ ?M0 ?M1 ?T hT hM0 hM1
      | ?n ?Γ ?T ?M0 ?M1 ?z hT hM0 hM1
      | ?n ?Γ ?M ?N hMN
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
    + (* c_eta: function extensionality at type A⟨↑⟩, see Admitted note. *)
      move: ρ Fρ. eapply InvConv_eta; eauto.
    + (* c_nrec_Z: app (nrec ...) zero ≡ M0 : T[zero..].  Forward direction
         (app ... → M0): EvalRel of app (nrec ...) ρ u forces u = bot, and
         EvalRel _ ρ bot is always trivially True.  Backward direction:
         requires the converse, which only holds when the actual application
         is bot — needs more structure.  Admit. *)
      move: ρ Fρ.
      eapply InvConv_nrec_Z; eauto.      
    + (* c_nrec_S: similar — nrec is fake. *)
      move: ρ Fρ.
      eapply InvConv_nrec_S; eauto.
    + (* c_tuniv: identity rule — just recurse. *)
      exact (conv_EvalRel _ _ _ _ _ hMN ρ Fρ).
    + (* c_tpi: tpi A0 B0 = tpi A1 B1 : tuniv i *)
      move: ρ Fρ.
      eapply InvConv_tpi; eauto.
Qed.

