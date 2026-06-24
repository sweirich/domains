
From Stdlib Require Import Relations List Program
     ssreflect ssrfun ssrbool.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

From Stdlib Require Import Classes.RelationClasses Classes.Morphisms Lia Arith.


Require Import smpl.Smpl.

Require Import utils.all.
Require Import finelt.utils.

From Equations Require Import Equations.

Require Import findom.

Import findom.Raw.

(* Note about minimality / function representation
 
   For some functions: we might want this property
 
    (ui,vi) in f, (uj,vj) in f,   ui <= uj implies vi <= vj 

   This gives us for any (ui,vi) in f,
    app f ui = Some vi    
    (* exactly, don't need to look at other tuples *)

    
   example: consider F:
     (succ (succ bot),  { (1,1) }  )
     (succ bot, { (0,0) } )


   minimal but violates the property because 
      F (suc (succ bot)) = { (0,0), (1,1) }

   this property + minimal means unique representation for sets of pairs
   
*)


(* -------------------------------------------------------------- *)


(** well typed elements (finMem)
    In this branch tuniv has no universe-level argument (type-in-type). *)
Inductive wt : elt -> elt -> Prop :=
  | wt_bot a :
    wt a tuniv ->
    wt bot a

  | wt_tuniv :
    wt tuniv tuniv

  | wt_tnat :
    wt tnat tuniv

  | wt_zero :
    wt zero tnat

  | wt_succ u :
    wt u tnat ->
    wt (succ u) tnat

  | wt_tpi a g :
    wt a tuniv ->
    (* check all pairs *)
    (forall ui vi, In (ui, vi) g -> wt ui a) ->
    (forall ui vi, In (ui,vi) g -> wt vi tuniv) ->
    (* make sure tm is valid *)
    valid (tpi a g) ->
    wt (tpi a g) tuniv

  | wt_abs a f g :
    (* check definition against type *)
    (forall ui vi, In (ui, vi) f -> wt ui a) ->
    (forall ui vi, In (ui,vi) f -> wt vi (app g ui)) ->
    (* make sure tm is valid *)
    valid (abs f) ->
    (* make sure type is a type *)
    wt (tpi a g) tuniv ->
    wt (abs f) (tpi a g).

(** * Validity *)


Fixpoint wt_valid_tm u a : wt u a -> valid u.
- induction 1; eauto.  
Qed.

Lemma wt_valid_ty u a : wt u a -> valid a.
induction 1; eauto using wt_valid_tm.
Qed.

Hint Resolve wt_valid_tm wt_valid_ty : valid.

(* Only bot has type bot *)
Lemma wt_bot_inv u : wt u bot -> u = bot.
Proof. move=> h. inversion h. done. Qed.

(** Generation / regularity *)

(* FinMem-a-in-U (type-in-type: every typed term's type lives in tuniv). *)
Lemma wt_ty_tuniv u a : wt u a -> wt a tuniv.
Proof.
  induction 1; eauto using wt_tuniv, wt_tnat, wt_tpi.
Qed.

(** ** Inversion lemmas *)


Lemma wt_succ_inv u:
  wt (succ u) tnat -> wt u tnat.
move=>h. inversion h. done. Defined.

Lemma wt_abs_ty g b f : 
  wt (abs g) (tpi b f) -> wt (tpi b f) tuniv.
Proof. 
  move=> h. inversion h. eauto.
Defined.


Lemma wt_abs_inv1 g a f : 
  wt (abs f) (tpi a g) ->     
  (forall ui vi, In (ui, vi) f -> wt ui a).
Proof. 
  move=> h. inversion h. eauto.
Defined.

Lemma wt_abs_inv2 g a f :
  wt (abs f) (tpi a g) ->
  (forall ui vi t, In (ui,vi) f ->
              app g ui = t -> wt vi t).
Proof. 
  move=> h. inversion h. intros. subst. auto.
Defined.


Lemma wt_tpi_keys a g :
  wt (tpi a g) tuniv -> forall ui vi, In (ui, vi) g -> wt ui a.
Proof. move=> h. inversion h. eauto. Defined.

Lemma wt_tpi_dom a g :
  wt (tpi a g) tuniv  -> wt a tuniv.
Proof.
  move=> h. inversion h. eauto.
Defined.




Lemma wt_abs_cons 
  a f g :
  wt (abs f) (tpi a g) -> 
  forall ui vi,
    wt ui a -> wt vi (app g ui) ->
    valid (abs ((ui,vi)::f)) ->
    wt (abs ((ui,vi) :: f)) (tpi a g).
Proof.
  move=> h.
  inversion h. subst.
  intros ui vi WTui WTvi Vcons.
  have Vui: valid ui. eauto with valid.
  eapply wt_abs.
  - intros ui0 vi0 [EQ|INf].
    + inversion EQ. subst. auto.
    + eauto.
  - intros ui0 vi0 [EQ|INf].
    + inversion EQ. subst ui0. subst vi0. clear EQ.
      done.
    + eapply H3; eauto.
  - done.
  - done.
Qed.

Lemma wt_tpi_tail a u v g : 
  wt (tpi a ((u,v)::g)) tuniv -> wt (tpi a g) tuniv.
Proof.
  intro h. inversion h.
  eapply wt_tpi; eauto.
  - intros ui vi Ing.
    eapply H2; eauto. right. eauto.
  - intros ui vi Ing.
    eapply H3; eauto. right. eauto.
  - apply valid_tpi_inv in H4. move: H4 => [Va Vl].
    eapply valid_tpi_intro; eauto.
    eapply valid_fun_tail; eauto.
Qed.

Lemma wt_abs_tail u v w b f :
  wt (abs ((u,v)::w)) (tpi b f) -> ~~is_nil w ->
  wt (abs w) (tpi b f).
Proof.
  move=> WT Nw. inversion WT. subst.
  have Vb: valid b. eauto with valid.
  have Vf: valid_fun f. eauto with valid.
  have Vw: valid_fun ((u,v):: w). eauto with valid.
  move: (valid_fun_tail Vw) => Vt.
  move: (valid_fun_head Vw) => Vh.
  eapply wt_abs; eauto. 
  - intros ui vi Inw. eapply H2; eauto. right; eauto.
  - intros ui vi Inw. eapply H3; eauto. right; eauto.
  - cbn. rewrite Vt. rewrite Nw. done.
Qed.


From Stdlib Require Import Psatz.
Module WTLE.


Record WTLE_Lemmas k := MkLemmas { 
  wt_le  : forall u a (h : wt u a) b, 
           max (rk a) (rk b) <= k ->
           le a b -> wt a tuniv -> wt b tuniv -> wt u b ;
  wt_lub : forall u a (h: wt u a) v, max (rk u) (rk v) <= k -> 
           compatible u v ->
           wt v a -> wt (lub u v) a 

}.

Lemma all_app_is_tuniv k
  (ih : WTLE_Lemmas k) {a g} (h : wt (tpi a g) tuniv) : 
  (rk_fun g) <= k ->
  forall u, valid u -> wt (app g u) tuniv.
Proof.
  move: h.
  induction g as [|[ui vi] g];
  intros h RK u Vu.
  - inversion h; subst.
    rewrite app_nil_eq.
    eapply wt_bot. eapply wt_tuniv.
  - have WTt : wt (tpi a g) tuniv by (eapply wt_tpi_tail; eauto).
    specialize (IHg WTt ltac:(cbn in RK; cbn; lia) u). 
    rewrite app_cons_eq.
    destruct (le ui u) eqn:EQ.
    + inversion h.
      cbn in RK.
      have RK1 : rk (app g u) <= rk_fun g. eapply rk_app.
      have WT1 : wt vi tuniv by (apply: (H3 ui vi); left).
      eapply (@wt_lub _ ih _ _ WT1); eauto. lia.
      eapply compatible_coherent_app; eauto.
      eapply le_compatible; eauto.
      eauto with valid.
    + eapply IHg; eauto.
Qed.


Lemma WTLE : forall k, WTLE_Lemmas k.
Proof.
  elim /strong_ind.
  move=> m ih. 
  split.
(* wt is monotone *)
  - (* If u : a and a <= b, then u : b *)
    move=> u a h b RK. 
    dependent destruction h.
    all: move=> LE WTa WTb.
    7 : { 
      destruct (le_tpi_inv LE) as [a1 [g1 [-> [LEa LEg]]]].
      have Wta: wt a tuniv. inversion WTa; eauto.
      have Wta1: wt a1 tuniv. inversion WTb; eauto.      
      cbn in RK.
      eapply wt_abs; eauto.
      ++ intros ui vi Inf.
         specialize (ih (max (rk a) (rk a1)) ltac:(lia)).
         eapply wt_le; eauto.
      ++ intros ui vi Inf.
         have RA: rk (app g ui) <= rk_fun g. eapply rk_app.
         have RA1: rk (app g1 ui) <= rk_fun g1. eapply rk_app.
         specialize (ih (max (rk_fun g) (rk_fun g1)) ltac:(lia)).
         have Vg : valid_fun g. eauto with valid.
         have Vg1 : valid_fun g1. eauto with valid.
         have Vui : valid ui. eauto with valid.
         move: (le_fun_mono Vg Vg1 LEg Vui) => LEt.
         have WTt: (wt (app g1 ui) tuniv).
         { eapply all_app_is_tuniv; eauto. lia. }
         have WTt2: (wt (app g ui) tuniv).
         { inversion WTa. eapply all_app_is_tuniv; eauto. lia. }
         eapply wt_le; eauto. lia.
    } 
    all: cbn in RK.
    + eapply wt_bot; eauto.
    + apply le_tuniv_inv in LE. subst.
      eapply wt_tuniv.
    + apply le_tuniv_inv in LE. subst.
      eapply wt_tnat.
    + apply le_tnat_inv in LE. subst.
      eapply wt_zero.
    + eapply le_tnat_inv in LE. subst.
      eapply wt_succ; eauto.
    + apply le_tuniv_inv in LE. subst.
      eapply wt_tpi; eauto.
  - (* If u : a and v : a, then lub u v : a. *)
    move=> u a h v RK Cav WTv.
    have WTa: wt a tuniv. eapply wt_ty_tuniv; eauto.
    have WTb:  wt bot a. eapply wt_bot; auto.
    have Vlub: valid (lub u v). 
    { eapply valid_lub; eauto using wt_valid_tm. } 
    dependent destruction h.
    all: destruct v; cbn; auto.
    all: cbn in RK.
    all: try solve [eauto using wt].
    + inversion WTv; subst.
      eapply wt_succ; eauto.
      eapply wt_lub; eauto.
    + inversion WTv; subst.
      cbn in Cav. move: Cav => /andP [Cav Cgl].
      rewrite Cgl.
      eapply wt_tpi; eauto.
      ++ eapply wt_lub; eauto. lia.
      ++ intros ui vi INgl.
         have Va: valid a. eauto with valid.
         have Vv: valid v. eauto with valid.
         have RKlub: rk (lub a v) <= max (rk a) (rk v). eapply rk_lub.
         destruct (in_app_or _ _ _ INgl) as [Ing|Inl].
         * eapply wt_le; eauto.  lia.
           eapply le_lub_left; eauto.
           eapply wt_lub; eauto. lia.
         * eapply wt_le; eauto.  lia.
           eapply le_lub_right; eauto.
           eapply wt_lub; eauto. lia.         
      ++ intros ui vi INgl.
         destruct (in_app_or _ _ _ INgl) as [Ing|Inl].
         eauto. eauto.
      ++ cbn in Vlub. rewrite Cgl in Vlub. done.
    + cbn in Cav. rewrite Cav.
      inversion WTv. subst.
      eapply wt_abs.
      ++ move=> u v APP.
       have Vf: valid_fun f. eauto with valid.
       have Vl: valid_fun l. eauto with valid.
       apply in_app_or in APP. destruct APP as [INf|Inl]; eauto.
    ++ (* wt rng for (f ++ l) *)
       move=> u v InApp.
       have Vf: valid_fun f. eauto with valid.
       have Vl: valid_fun l. eauto with valid.
       apply in_app_or in InApp. destruct InApp as [INf|Inl]; eauto.
    ++ cbn.
       apply /andP. split.
       eapply valid_append; eauto with valid.
       destruct f; try done.
    ++ done.
Qed.
         
End WTLE.         


Definition wt_le : forall u a (h : wt u a), 
    forall b, le a b -> wt a tuniv -> wt b tuniv -> wt u b.
Proof.
  intros.
  eapply WTLE.wt_le; eauto. eapply WTLE.WTLE.
Qed.

Definition wt_lub : forall u a (h: wt u a) v, 
           compatible u v ->
           wt v a -> wt (lub u v) a. 
Proof.   intros.
  eapply WTLE.wt_lub; eauto. eapply WTLE.WTLE.
Qed.

Lemma all_app_is_tuniv {a g} (h : wt (tpi a g) tuniv) : 
  forall u, valid u -> wt (app g u) tuniv.
Proof. 
  intros.
  eapply WTLE.all_app_is_tuniv; eauto. eapply WTLE.WTLE.
Qed.

Lemma wt_tpi_inv2 a g :
  wt (tpi a g) tuniv  ->
  forall u v, valid u -> app g u = v -> wt v tuniv.
Proof.
  move=> h u v Vu <-. eapply all_app_is_tuniv; eauto.
Defined.


(* Corollary 2 If w : Πaf and u : a, then w(u) : f (u). *)

Lemma wt_app w a f :
  wt (abs w) (tpi a f) ->
  forall u, wt u a -> wt (app w u) (app f u).
Proof.
  induction w as [|[ui vi] w'].
  - (* w = nil is impossible: valid (abs nil) is false *)
    move=> WT u WTu.
    move: (wt_valid_tm WT). by cbn.
  - move=> WT u WTu.
    have Vu : valid u by eauto with valid.
    have Vtpi : valid (tpi a f) by eauto with valid.
    have Vf : valid_fun f by (move: Vtpi => /andP [_ ?]; done).
    have Vabs : valid (abs ((ui,vi) :: w')) by eauto with valid.
    have Vw : valid_fun ((ui,vi) :: w') by (move: Vabs => /andP [Vff _]; done).
    have Vt : valid (app f u) by eapply (app_tpi_valid Vtpi Vu).
    have Vui : valid ui by eapply key_valid; eauto using valid_fun_head.
    have Vvi : valid vi by eapply val_valid; eauto using valid_fun_head.
    (* Extract per-entry typing info from WT *)
    inversion WT as [| | | | | |aX wX fX j HuiAll VabsX WTtpiX]; subst.
    (* app f u is itself a type *)
    have WTfu : wt (app f u) tuniv.
    { eapply (all_app_is_tuniv); eauto. }
    (* r' := app w' u is well-typed at app f u *)
    have WTr' : wt (app w' u) (app f u).
    { destruct (~~ is_nil w') eqn:Nw.
      - have WTw' : wt (abs w') (tpi a f) by eapply wt_abs_tail; eauto.
        eapply IHw'; eauto.
      - destruct w'; try done. rewrite app_nil_eq.
        by eapply wt_bot. }
    rewrite app_cons_eq.
    destruct (le ui u) eqn:LEui.
    + (* ui <= u: result is lub vi (app w' u) *)
      have WTviwi : wt vi (app f ui)
        by (eapply (HuiAll ui vi); left). 
      have LEwit : le (app f ui) (app f u)
        by (eapply le_fun_mono_arg; eauto with valid).
      have WTvit : wt vi (app f u).
      { eapply wt_le; [exact WTviwi | exact LEwit | ..].
        - eapply wt_ty_tuniv; exact WTviwi.
        - exact WTfu. }
      eapply wt_lub; eauto.
      eapply compatible_coherent_app; eauto.
      eapply le_compatible; eauto.
      eauto with valid.
    + (* ui not below u: result is app w' u *)
      exact WTr'.
Qed.

(* Same as [wt_app] but only requires the argument to be valid (not
   necessarily typed at the domain): a typed function maps any valid
   argument to a value well-typed at the corresponding codomain image.
   The argument's typing is only used in [wt_app] to thread the
   recursion, so [valid u] suffices throughout. *)
Lemma wt_app_valid w a f :
  wt (abs w) (tpi a f) ->
  forall u, valid u -> wt (app w u) (app f u).
Proof.
  induction w as [|[ui vi] w'].
  - move=> WT u Vu.
    move: (wt_valid_tm WT). by cbn.
  - move=> WT u Vu.
    have Vtpi : valid (tpi a f) by eauto with valid.
    have Vf : valid_fun f by (move: Vtpi => /andP [_ ?]; done).
    have Vabs : valid (abs ((ui,vi) :: w')) by eauto with valid.
    have Vw : valid_fun ((ui,vi) :: w') by (move: Vabs => /andP [Vff _]; done).
    have Vt : valid (app f u) by eapply (app_tpi_valid Vtpi Vu).
    have Vui : valid ui by eapply key_valid; eauto using valid_fun_head.
    have Vvi : valid vi by eapply val_valid; eauto using valid_fun_head.
    inversion WT as [| | | | | |aX wX fX j HuiAll VabsX WTtpiX]; subst.
    have WTfu : wt (app f u) tuniv.
    { eapply (all_app_is_tuniv); eauto. }
    have WTr' : wt (app w' u) (app f u).
    { destruct (~~ is_nil w') eqn:Nw.
      - have WTw' : wt (abs w') (tpi a f) by eapply wt_abs_tail; eauto.
        eapply IHw'; eauto.
      - destruct w'; try done. rewrite app_nil_eq.
        by eapply wt_bot. }
    rewrite app_cons_eq.
    destruct (le ui u) eqn:LEui.
    + have WTviwi : wt vi (app f ui)
        by (eapply (HuiAll ui vi); left).
      have LEwit : le (app f ui) (app f u)
        by (eapply le_fun_mono_arg; eauto with valid).
      have WTvit : wt vi (app f u).
      { eapply wt_le; [exact WTviwi | exact LEwit | ..].
        - eapply wt_ty_tuniv; exact WTviwi.
        - exact WTfu. }
      eapply wt_lub; eauto.
      eapply compatible_coherent_app; eauto.
      eapply le_compatible; eauto.
      eauto with valid.
    + exact WTr'.
Qed.


