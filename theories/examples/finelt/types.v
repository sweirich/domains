
From Stdlib Require Import Relations List Program
     ssreflect ssrfun ssrbool.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

From Stdlib Require Import ProofIrrelevance.

From Stdlib Require Import Classes.RelationClasses Classes.Morphisms Lia Arith.

Require Import utils.all.

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
Inductive wt : elt -> elt -> Type :=
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
    (forall u v, valid u -> app g u = Some v -> ~ is_bot v -> wt u a) -> 
    (forall u v, valid u -> app g u = Some v -> ~ is_bot v -> wt v tuniv) ->
    (* make sure tm is valid *)
    valid (tpi a g) ->
    wt (tpi a g) tuniv

  | wt_abs a f g :
    (* check definition against type *)
    (forall u v, valid u -> app f u = Some v -> ~ is_bot v -> wt u a) -> 
    (forall u v t, valid u -> app f u = Some v -> ~ is_bot v -> app g u = Some t -> wt v t) -> 
    (* make sure tm is valid *)
    valid (abs f) ->
    (* make sure type is a type *)
    wt (tpi a g) tuniv ->
    wt (abs f) (tpi a g).


From Stdlib Require Import Lia Inverse_Image Wellfounded.Inclusion Wf_nat.

Inductive wt_ord := 
  | wt_ord_zero : wt_ord
  | wt_ord_succ : wt_ord -> wt_ord 
  | wt_ord_tpi : wt_ord -> 
      (forall (u v : elt), wt_ord) ->
      (forall (u v t : elt), wt_ord) ->
      wt_ord
  | wt_ord_abs :
    (forall (u v : elt), wt_ord) -> 
    (forall (u v t : elt), wt_ord) -> 
    wt_ord ->
    wt_ord.

Fixpoint lt_wt_ord (w1 w2 : wt_ord ) : Prop := 
  match w1, w2 with 
  | wt_ord_zero , wt_ord_zero => False
  | wt_ord_zero , _ => True 
  | wt_ord_succ _ , wt_ord_zero => False
  | wt_ord_succ n1, wt_ord_succ n2 =>  lt_wt_ord n1 n2 
  | wt_ord_succ _ , _ => True 
  | wt_ord_tpi _ _ _ , wt_ord_zero => False
  | wt_ord_tpi _ _ _ , wt_ord_succ _ => False
  | wt_ord_tpi h1 h2 h3, wt_ord_tpi h1' h2' h3' => 
      lt_wt_ord h1 h1' /\   
      (forall u v, 
        lt_wt_ord (h2 u v) (h2' u v)) /\
      (forall u v t, 
        lt_wt_ord (h3 u v t) (h3' u v t))
  | wt_ord_tpi _ _ _ , _ => True
  | wt_ord_abs h1 h2 h3, wt_ord_abs h1' h2' h3' => 
      (forall u v, 
        lt_wt_ord (h1 u v) (h1' u v)) /\
      (forall u v t, 
        lt_wt_ord (h2 u v t) (h2' u v t)) /\
     lt_wt_ord h3 h3'
  | wt_ord_abs h1 h2 h3, _ => False
  end.
        

(* Acc on each constructor, built bottom-up via the strict hierarchy
   zero < succ < tpi < abs. *)

Lemma acc_zero : Acc lt_wt_ord wt_ord_zero.
Proof.
  constructor. intros y Hy. destruct y; cbn in Hy; try done.
Qed.

(* Acc (succ n) from Acc n via Acc-induction. *)
Lemma acc_succ_from_acc : forall n, Acc lt_wt_ord n -> Acc lt_wt_ord (wt_ord_succ n).
Proof.
  intros n Hn.
  induction Hn as [n _ IHn].
  constructor. intros y Hy. destruct y; cbn in Hy.
  - apply acc_zero.
  - apply IHn. exact Hy.
  - contradiction.
  - contradiction.
Qed.

(* Acc (tpi h1 h2 h3) given Acc on h1, h2 u v, h3 u v t AND Acc on
   wt_ord_zero and on (wt_ord_succ y) for every y. *)
(*
Lemma acc_tpi_from_accs : forall h1 h2 h3,
  Acc lt_wt_ord h1 ->
  (forall u v, Acc lt_wt_ord (h2 u v)) ->
  (forall u v t, Acc lt_wt_ord (h3 u v t)) ->
  Acc lt_wt_ord (wt_ord_tpi h1 h2 h3).
Proof.
  intros h1 h2 h3 H1 H2 H3.
  constructor. intros y Hy. destruct y; cbn in Hy.
  - (* y = zero *) apply acc_zero.
  - (* y = succ y' *) 
    eapply acc_succ_from_acc.
  - (* y = tpi h1' h2' h3' (structural) *)
    destruct Hy as [Hh1 [Hh2 Hh3]].
    apply tpi_acc.
    + eapply Acc_inv. exact H1. exact Hh1.
    + intros u v. eapply Acc_inv. apply H2. apply Hh2.
    + intros u v t. eapply Acc_inv. apply H3. apply Hh3.
  - contradiction.
Qed.

(* Acc (abs h1 h2 h3) given Acc on h1 u v, h2 u v t, h3 AND Acc on
   wt_ord_zero, (wt_ord_succ y) for every y, and (wt_ord_tpi g1 g2 g3) for
   every g1, g2, g3. *)
Lemma acc_abs_from_accs : forall h1 h2 h3,
  (forall u v, Acc lt_wt_ord (h1 u v)) ->
  (forall u v t, Acc lt_wt_ord (h2 u v t)) ->
  Acc lt_wt_ord h3 ->
  (forall y, Acc lt_wt_ord (wt_ord_succ y)) ->
  (forall g1 g2 g3, Acc lt_wt_ord (wt_ord_tpi g1 g2 g3)) ->
  Acc lt_wt_ord (wt_ord_abs h1 h2 h3).
Proof.
  intros h1 h2 h3 H1 H2 H3 Hsucc Htpi.
  revert h1 h2 h3 H1 H2 H3.
  fix abs_acc 6.
  intros h1 h2 h3 H1 H2 H3.
  constructor. intros y Hy. destruct y; cbn in Hy.
  - apply acc_zero.
  - apply Hsucc.
  - apply Htpi.
  - (* y = abs h1' h2' h3' (structural) *)
    destruct Hy as [Hh1 [Hh2 Hh3]].
    apply abs_acc.
    + intros u v. eapply Acc_inv. apply H1. apply Hh1.
    + intros u v t. eapply Acc_inv. apply H2. apply Hh2.
    + eapply Acc_inv. exact H3. exact Hh3.
Qed. *)


Lemma well_founded_lt_wt_ord : well_founded lt_wt_ord.
Proof.
Admitted.
(*
  red.
   intros wto. induction wto.
  - (* zero *) apply acc_zero.
  - (* succ wto, IH : Acc wto *)
    apply acc_succ_from_acc. exact IHwto.
  - (* tpi h1 h2 h3, IHs : Acc h1, forall u v Acc (h2 u v), forall u v t Acc (h3 u v t) *)
Admitted.
*)


(* Uniqueness of [wt] (and its mutual companions) derivations.
   Constructors that hold positive content recurse on the sub-derivations;
   propositional witnesses (the [valid _] booleans and the [app g ui = Some t]
   equality) are unified via the [proof_irrelevance] axiom. *)
Fixpoint wt_unique u a (h1 h2 : wt u a) {struct h1} : h1 = h2.
  - dependent destruction h1; dependent destruction h2;
      try reflexivity.
    + (* wt_bot *) f_equal. apply wt_unique.
    + (* wt_succ *) f_equal. apply wt_unique.
    + (* wt_tpi *) f_equal.
         apply wt_unique.
         ext. apply wt_unique.
         ext. apply wt_unique.
         apply proof_irrelevance.
    + (* wt_abs *) f_equal.
         ext. apply wt_unique.
         ext. apply wt_unique.
         apply proof_irrelevance.
         apply wt_unique.
Qed.


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
  (forall u v, valid u -> app f u = Some v -> ~ is_bot v -> wt u a).
Proof. 
  move=> h. inversion h. eauto.
Defined.

Lemma wt_abs_inv2 g a f : 
  wt (abs f) (tpi a g) ->    
  (forall u v t, valid u -> app f u = Some v -> ~ is_bot v -> app g u = Some t -> wt v t). 
Proof. 
  move=> h. inversion h. eauto.
Defined.


Lemma wt_tpi_dom a g :
  wt (tpi a g) tuniv  -> wt a tuniv.
Proof.
  move=> h. inversion h. eauto.
Defined.


Lemma wt_tpi_inv1 a g :
  wt (tpi a g) tuniv -> 
  (forall u v, valid u -> app g u = Some v -> ~ is_bot v -> wt u a).
Proof.
  move=> h. inversion h. eauto.
Defined.

Lemma wt_tpi_inv2 a g :
  wt (tpi a g) tuniv -> 
  (forall u v, valid u -> app g u = Some v -> ~ is_bot v -> wt v tuniv).
Proof.
  move=> h. inversion h. eauto.
Defined.


(* wt is monotone *)

(*
Lemma 2 
If u : a and a <= b, then u : b.
*)
Fixpoint wt_le u a 
  (h : wt u a) {struct h} : forall b, le a b -> wt a tuniv -> wt b tuniv -> wt u b.
Proof.
    dependent destruction h.
    all: move=> b LE WTa WTb.
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
  + (* abs case: know wt (abs f) (tpi a g),
       WTP wt (abs f) (tpi a1 g1) where a <= a1 and g <= g1  *)
    destruct (le_tpi_inv LE) as [a1 [g1 [-> [LEa LEg]]]].
    eapply wt_abs; eauto.
    ++ move=> u v Vu APP Nb.
       eapply wt_le; eauto.
       inversion WTa. done.
       inversion WTb. done.
    ++ move=> u v t1 Vu APP NB APP1.
       have Vg : valid_fun g. eauto with valid.
       have Vg1 : valid_fun g1. eauto with valid.
       destruct (valid_app_exists Vg Vu) as [t2 [APP2 Vt2]].
       move: (w0 _ _ _ Vu APP NB APP2) => WTvt2.
       move: (le_fun_mono Vg Vg1 LEg Vu APP2 APP1) => LEt.
       destruct (is_bot t1) eqn:NBt1.
       -- destruct t1; try done. 
          apply le_bot_inv in LEt. subst t2. done.
       -- eapply wt_le; eauto.
          eapply wt_ty_tuniv; eauto.
          inversion WTb. eapply (H3 u t1); eauto. 
Qed.


(*
Lemma wt_abs_fun_lub f1 a g :
  wt_abs_fun f1 a g -> forall f2, wt_abs_fun f2 a g -> 
                            compatible_fun f1 f2 ->
                            wt_abs_fun (f1 ++ f2) a g.
Proof.
  induction f1.
  all: move=> WTf1 f2 WTf2 Cf.
  all: inversion WTf1; subst.
  all: cbn; eauto.
  move: Cf => /andP [Cui Cf].
  eapply wt_abs_cons; eauto.
  rewrite app_comm_cons.
  eapply valid_append; eauto.
  eapply wt_abs_fun_valid_fun; eauto.
  apply /andP. split; auto.
Qed. *)


(* - If u : a, v : a, and u and v are compatible, then lub u v : a *)
Lemma wt_lub u a (h: wt u a) 
  : forall v w, wt v a -> lub u v = Some w -> wt w a.
Proof.
  induction h.
  all: move=> v w1 Wtv LUB.
  all: inversion LUB; subst; try done.
  all: destruct v; try done.
  all: try solve [cbn in LUB; inversion LUB;
                  subst; econstructor; eauto].
  + (* u = succ u, v = succ v *)
    destruct (lub u v) eqn:EQ; try done.
    match goal with [H0 : option_map _ (Some _) = _ |- _] =>
    cbn in H0; inversion H0 end. 
    subst.
    inversion Wtv; subst.
    eapply wt_succ; eauto.
  + (* u = tpi a g, v=tpi v l *)
    destruct (compatible_fun g l) eqn:C1; try done.
    destruct (lub a v) eqn:L1; try done.
    match goal with [H0 : option_map _ (Some _) = _ |- _] =>
    cbn in H0; inversion H0; clear H0 end. 
    (* e = lub a v *)
    clear LUB.
    inversion Wtv; subst. clear Wtv.
    eapply wt_tpi.
    ++ eapply IHh in L1; eauto. 
    ++ move=> ui vi Vui APP NB.
       have Vg: valid_fun g. eauto with valid.
       have Vl: valid_fun l. eauto with valid.
       move: (compatible_app_inv Vg Vl Vui C1 APP) => 
             [v1 [v2 [APP1 [APP2 h3]]]].
       destruct (is_bot v1) eqn:N1. 
       destruct (is_bot v2) eqn:N2.
       { destruct v1; destruct v2; try done. cbn in h3. 
         inversion h3. subst. done. }
       { have Nb2: ~ is_bot v2. 
         rewrite N2. done.
         specialize (H5 ui v2 Vui APP2 Nb2).
         eapply wt_le; eauto. 
         eapply le_lub_right; eauto.
         eapply lub_compatible; eauto.
         eauto with valid.
         eauto with valid. } 
       { have Nb1 : ~ is_bot v1. rewrite N1. done. 
         specialize (w0 ui v1 Vui APP1 Nb1).
         eapply wt_le; eauto.
         eapply le_lub_left; eauto.
         eapply lub_compatible; eauto.
         eauto with valid.
         eauto with valid. } 
    ++ move=> ui vi Vui APP NB.
       have Vg: valid_fun g. eauto with valid.
       have Vl: valid_fun l. eauto with valid.
       move: (compatible_app_inv Vg Vl Vui C1 APP) => 
             [v1 [v2 [APP1 [APP2 h3]]]].
       destruct (is_bot v1) eqn:N1. 
       { destruct v1; try done. inversion h3. subst.  eauto. } 
       destruct (is_bot v2) eqn:N2.
       { destruct v2; try done. rewrite lub_bot_r in h3. inversion h3. subst. eauto. }
       have Nb1 : ~ is_bot v1. rewrite N1. done. 
       have Nb2: ~ is_bot v2. rewrite N2. done.
       have WT1: wt v1 tuniv.  { exact (w0 ui v1 Vui APP1 Nb1). } 
       have WT2: wt v2 tuniv.  { exact (H6 ui v2 Vui APP2 Nb2). } 
       eapply (H0 ui v1 Vui APP1 Nb1 v2 vi WT2 h3) .
    ++ eapply valid_tpi_intro.
       eapply (@valid_lub a v); eauto with valid.
       eapply valid_append; eauto with valid.
  + (* u = abs f, v=abs l *)
    rename H into IHdom.
    rename H0 into IHrng.
    cbn in LUB.
    destruct (compatible_fun f l) eqn:C1; try done.
    inversion LUB; subst w1; clear LUB.
    inversion Wtv. subst. clear Wtv.
    eapply wt_abs.
    ++ move=> u v Vu APP NB.
       have Vf: valid_fun f. eauto with valid.
       have Vl: valid_fun l. eauto with valid.
       move: (compatible_app_inv Vf Vl Vu C1 APP) => 
             [v1 [v2 [APP1 [APP2 h3]]]].
       destruct (is_bot v1) eqn:N1. 
       destruct (is_bot v2) eqn:N2.
       { destruct v1; destruct v2; try done. cbn in h3. 
         inversion h3. subst. done. }
       { have Nb2: ~ is_bot v2. rewrite N2. done.
         eapply H3; eauto. }
       { have Nb1 : ~ is_bot v1. rewrite N1. done. 
         eapply (w u v1 Vu APP1 Nb1); eauto.
       } 
    ++ (* wt rng for (f ++ l) *)
       move=> u v t Vu APP NB APPg.
       have Vf: valid_fun f. eauto with valid.
       have Vl: valid_fun l. eauto with valid.
       move: (compatible_app_inv Vf Vl Vu C1 APP) => 
             [v1 [v2 [APP1 [APP2 h3]]]].
       have WTt: wt t tuniv.
       { destruct (is_bot t) eqn: NT.
         destruct t; try done. eapply wt_bot. eapply wt_tuniv.
         have Nb1:~ is_bot t. rewrite NT. done.
         eapply wt_tpi_inv2; eauto. } 
       have WT1: wt v1 t.
       { destruct (is_bot v1) eqn:N1. 
         - destruct v1; try done. 
           eapply wt_bot; eauto.
         - have Nb1 : ~ is_bot v1. rewrite N1. done. 
           exact (w0 u v1 t Vu APP1 Nb1 APPg).
       } 
       have WT2: wt v2 t.
       { destruct (is_bot v2) eqn:N2.
         - destruct v2; try done. eapply wt_bot; eauto. 
         - have Nb2: ~ is_bot v2. rewrite N2. done.
           exact (H4 u v2 t Vu APP2 Nb2 APPg).
       }
       destruct (is_bot v1) eqn:N1.
       - destruct v1; try done. cbn in h3. inversion h3. subst. done.
       - have Nb1: ~ (is_bot v1). rewrite N1. done.
         eapply (IHrng u v1 t Vu APP1 Nb1 APPg v2 v WT2 h3).
    ++ cbn.
       apply /andP. split.
       eapply valid_append; eauto with valid.
       destruct f; try done.
    ++ done.
Qed.


(* Corollary 2 If w : Πaf and u : a, then w(u) : f (u). *)

Lemma wt_abs_pred u v w b f :
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
Admitted.


Lemma wt_app w a f :
  wt (abs w) (tpi a f) ->
  forall u r t, wt u a -> app w u = Some r -> app f u = Some t -> wt r t.
Proof.
  induction w as [|[ui vi] w'].
  - (* w = nil: app nil u = Some bot, so r = bot *)
    move=> WT u r t WTu A1 A2.
    rewrite app_nil_eq in A1. inversion A1. subst r.
    have Vtpi : valid (tpi a f) by eauto with valid.
    have Vu : valid u by eauto with valid.
    have Vt : valid t by eapply app_tpi_valid; eauto.
    inversion WT. subst. inversion H4. 
  - move=> WT u r t WTu A1 A2.
    have Vu : valid u by eauto with valid.
    have Vtpi : valid (tpi a f) by eauto with valid.
    have Vabs : valid (abs ((ui,vi) :: w')) by eauto with valid.
    have Vw : valid_fun ((ui,vi) :: w'). move: Vabs => /andP [Vf _]. done.
    have Vt : valid t. { eapply (app_tpi_valid Vtpi Vu A2). }
    have Vui : valid ui by eapply key_valid; eauto using valid_fun_head.
    have Vvi : valid vi by eapply val_valid; eauto using valid_fun_head.
    (* Extract per-entry typing info from WT *)
    inversion WT as [| | | | | |aX wX fX j HuiAll VabsX WTtpiX]; subst.
    (* Get app w' u = Some r' *)
    have [r' [Ar' Vr']] : { r' & ((app w' u = Some r') * valid r')%type }.
    { destruct (~~ is_nil w') eqn:Nw.
      { eapply valid_app_exists; eauto using valid_fun_tail. }
      destruct w'; try done. exists bot; cbn; auto. }
    rewrite app_spec in A1. cbn in A1. rewrite <- app_spec in A1.
    rewrite Ar' in A1.
    (* r' is well-typed at t: either by IH (w' non-nil with wt_abs_pred) or r' = bot *)
    have WTr' : wt r' t.
    { destruct (~~ is_nil w') eqn:Nw.
      { have WTw' : wt (abs w') (tpi a f) by eapply wt_abs_pred; eauto.
        eapply IHw'; eauto. }
      destruct w'; try done. cbn in Ar'. inversion Ar'. subst r'.
      eapply wt_bot. admit.
    }
    destruct (compatible ui u && le ui u) eqn:EQui.
    + (* ui compatible with u and ui <= u: r = lub vi r' *)
      move: EQui => /andP [Cui LEui].
      (* Get wi = app f ui and show wt vi wi *)
      have [wi [Awi Vwi]] : { wi & ((app f ui = Some wi) * (valid wi))%type }
        by eapply app_tpi_exists; eauto.
      (* 
      have WTvi_wi : wt vi wi. inversion HuiAll. subst. rewrite Awi in H3. inversion H3. subst t0. clear H3. done. *)
 
      (* wi <= t by monotonicity of app f (or trivially if f is nil) *)
      have LEwit : le wi t.
      { cbn in Vtpi. move: Vtpi => /andP [_ Vf].
        { fold (valid_fun f) in Vf.
          have [_ LE] : compatible wi t /\ le wi t.
          { eapply le_fun_mono_arg with (h := f) (u1 := ui) (u2 := u); eauto. }
          exact LE. }
      }
(*
      have WTvi_t : wt vi t. eapply wt_le; eauto. admit. admit. *)
      eapply wt_lub with (u := vi) (v := r'); eauto.
      admit.
    + (* no contribution from (ui,vi): r = r' *)
      inversion A1. subst r. done.
Admitted.

