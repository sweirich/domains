From Stdlib Require Import Relations List Program
     ssreflect ssrfun ssrbool.
Unset Printing Implicit Defensive.

Require Import smpl.Smpl.

From Stdlib Require Import Classes.RelationClasses Classes.Morphisms Lia Arith.


Require Import utils.all.
Require Import categories.all.
Require Import preord.
Require Import finelt.utils.

From Equations Require Import Equations.

Require Import finelt.findom.

(* Module of valid finite functions *)
Module Valid.

Definition elt : Set := 
  { u : Raw.elt | Raw.valid u }.
(* finfun records [valid_fun f] only.
   Use [nefinfun] (non-empty finfun) for the [abs] case. *)
Definition finfun : Set :=
  { f : list (Raw.elt * Raw.elt) | Raw.valid_fun f }.

Definition nefinfun : Set :=
  { f : list (Raw.elt * Raw.elt) | Raw.valid_fun f /\ ~~ Raw.is_nil f }.

Lemma elt_ext (u v : elt) : sval u = sval v -> u = v.
Proof.
  destruct u, v ; cbn.
  intros ?.
  now ext.
Qed.

(* --------------- constructors --------------- *)

Program Definition bot : elt := exist _ Raw.bot _.
Program Definition tnat : elt := (exist _ Raw.tnat _).
Program Definition tuniv : elt := (exist _ Raw.tuniv _).
Program Definition zero : elt := (exist _ Raw.zero _).
Program Definition succ (u : elt) : elt := (exist _ (Raw.succ (sval u)) _).
Next Obligation.
  apply svalP.
Qed.

Program Definition tabs (f : finfun) : elt :=
  if_eq (Raw.is_nil (sval f)) (fun _ => bot) (fun e => exist _ (Raw.abs (sval f)) _).
Next Obligation.
  destruct f as [rf h] ; cbn in *.
  rewrite h e //.
Qed.

Program Definition tpi_finfun (a : elt) (f : finfun) : elt :=
  (exist _ (Raw.tpi (sval a) (sval f)) _).
Next Obligation.
  cbn. apply /andP. split. eapply svalP.
  destruct f as [rf h1]. cbn. exact h1.
Qed.

Program Definition tpi_empty (a : elt) : elt := (tpi_finfun a (exist _ nil _)).

(* create either a abs (u,v) or bot *)
Program Definition singleton (u v : elt) : elt :=
  if_eq (Raw.le (sval v) Raw.bot)
  (fun _ =>  bot)
  (fun e => (exist _ (Raw.singleton (sval u) (sval v)) _)).
Next Obligation.
  destruct u as [u Vu], v as [v Vv] ; cbn in *.
  assert (Raw.is_bot v = false) as h.
  {
   by destruct v ; simp le in e ; cbn in *. 
  }
  rewrite /Raw.singleton h /= /Raw._valid_fun /= !Bool.andb_true_r.
  apply /andP ; split.
  2: by rewrite Vu Vv.
  apply /andP ; split.
  2: by rewrite e.
  apply /implyP => _.
  by apply Raw.compatible_refl.
Qed.

(* -------------- compatible ----------------- *)

Definition compatible (u : elt) (v : elt) : bool := 
  Raw.compatible (sval u) (sval v).

(* --------------------- lub ----------------- *)

Program Definition lub (u : elt) (v : elt) : elt :=
  if_eq (compatible u v)
  (fun e => exist _ (Raw.lub (sval u) (sval v)) _)
  (fun _ => bot).
Next Obligation.
  destruct u, v ; cbn in *.
  now eapply Raw.valid_lub.
Qed.

(* -------------------- le ------------------- *)
Definition le : elt -> elt -> bool := 
  fun u v => Raw.le (sval u) (sval v).

Definition le_fun (u v : finfun) : bool :=
  Raw.le_fun (sval u) (sval v).

Lemma le_refl : forall u, le u u.
Proof.
move=> [u Vu]. unfold le.
now rewrite Raw.le_refl.
Qed.

Lemma le_trans : forall u v w, le u v -> le v w -> le u w.
Proof.
move=> [u Vu] [v Vv] [w Vw].
rewrite /le /=.
by apply Raw.le_trans.
Qed.

Lemma le_bot : forall u, le bot u.
Proof.
move=> [ru Vu].
rewrite /le /=.
now simp le.
Qed.

Lemma le_tnat : le tnat tnat = true.
Proof.
  by cbv ; simp le.
Qed.

(** -------------- equal ------------- *)

Definition eqb : elt -> elt -> bool := 
  fun u v => le u v && le v u.
Definition eqb_fun (u v : finfun) : Prop := 
  le_fun u v && le_fun v u.

Lemma eqb_bot_inv u : eqb u bot -> u = bot.
Proof.
  move /andP => [] /Raw.le_bot_inv ? _.
  by ext.
Qed.

Lemma eqb_zero_inv u : eqb zero u -> u = zero.
Proof.
  move => /andP [].
  rewrite /le /= => [? _].
  ext ; cbn.
  by destruct u as [[] ?] ; cbn in * ; simp le in *.
Qed.

Lemma eqb_succ_inv u v : eqb (succ u) v -> 
                         exists u', v = succ u' /\ eqb u u'.
Proof.
  move => /andP [].
  rewrite /le /= => [? ?].
  destruct v as [[] ?] ; cbn in * ; simp le in * ; try done.
  eexists (exist _ _ _) ; split.
  1: ext ; cbn ; reflexivity.
  apply /andP.
  rewrite /le //=.
  Unshelve.
  easy.
Qed.

(** ----------------- application -------------- *)

Program Definition app (f : finfun) (u : elt) : elt :=
  exist _ (Raw.app (sval f) (sval u)) _.
Next Obligation.
  destruct f as [f Vf], u as [u Vu] => /=.
  by apply Raw.valid_app.
Qed.

Program Definition is_abs (v : elt) : option finfun :=
  match (sval v) with
    | Raw.abs rf => Some (exist _ rf _)
    | _ => None
  end.
Next Obligation.
  destruct v as [rv Vv] ; cbn in * ; subst.
  move: Vv => /= /andP [] //.
Qed.

Program Definition app_elt (f : elt) (u : elt) : elt :=
  match is_abs f with
    | Some f' => app f' u
    | _ => bot
   end.

Definition is_bot (v : elt) : bool := 
  match sval v with 
  | Raw.bot => true
  | _ => false
  end.

Definition graph (f : finfun) : list (elt * elt).
  destruct f as [f Vf].
  move: (Raw.valid_fun_subterms _ Vf) => h.
  clear Vf.
  move: h.
  induction f as [|[u v]f].
  move=> h. exact nil.
  cbn.
  move=> /andP.
  move=> [/andP h1 h2]. 
  eapply cons. destruct h1 as [Vu Vv].
  eapply ((exist _ u Vu),(exist _ v Vv)).
  eapply IHf; eauto.
Defined.

Definition compatible_fun (f g : finfun) : bool := 
  Raw.compatible_fun (sval f) (sval g).

Definition coherent_with (f:finfun) : elt * elt -> bool := 
  fun '(u, v) => 
  Raw.coherent_with (sval f) (sval u, sval v).

Lemma In_graph_def (f : finfun) ui vi : 
  In (sval ui, sval vi) (sval f) <->
  In (ui, vi) (graph f).
Proof.
  split.
  + destruct f as [rf Vf]. move: Vf.
    induction rf as [|[uj vj]f].
    all: move=> Vf.
    all: cbn [sval].
  - move=> h. inversion h.
  - cbn [sval] in IHf.
    move=> [EQ|h].
Admitted.

Lemma coherent_with_def f u v :
  (forallb 
    (fun '(uj, vj) => compatible u uj ==> compatible v vj) (graph f)) <->
  coherent_with f (u,v).
Proof.
  split.
  - move=> /forallb_forall CF. 
    apply /forallb_forall.
    move=> [rui rvi] Inrf.
    have [ui E1]: { UI : elt & sval UI = rui }. 
    { destruct f as [rf Vf]. cbn in Inrf.
      have Vui: Raw.valid rui.
      move: (Raw.valid_fun_subterms _ Vf) => /forallb_forall VSt.
      specialize (VSt _ Inrf). cbn in VSt. 
      move: VSt=> /andP. eauto.
      exists (exist _ rui Vui). eauto. } 
    have [vi E2]: { VI : elt & sval VI = rvi }. 
    { destruct f as [rf Vf]. cbn in Inrf.
      have Vvi: Raw.valid rvi.
      move: (Raw.valid_fun_subterms _ Vf) => /forallb_forall VSt.
      specialize (VSt _ Inrf). cbn in VSt. 
      move: VSt=> /andP. eauto.
      exists (exist _ rvi Vvi). eauto. } 
    rewrite <- E1 in Inrf. rewrite <- E2 in Inrf.
    rewrite In_graph_def in Inrf.
    specialize (CF _ Inrf). cbn in CF. 
    destruct ui. destruct vi. unfold compatible in CF.
      cbn in CF. cbn in E1. cbn in E2. subst. done. 
  - move=> /forallb_forall CF. 
    apply /forallb_forall.
    move=> [ui vi] Ingf.
    rewrite <- In_graph_def in Ingf.
    destruct ui. destruct vi. cbn in Ingf.
    specialize (CF _ Ingf).
    unfold compatible. cbn. eapply CF.
Qed.

Lemma compatible_fun_def (f g : finfun) : 
  forallb (coherent_with g) (graph f) <-> 
  compatible_fun f g.
Proof.
  split.
  - move=> /forallb_forall h.
    unfold compatible_fun, Raw.compatible_fun.
    apply /forallb_forall.
    move=> [ui vi] Inf.
Admitted.

Lemma le_fun_mono_arg f u1 u2 :
  le u1 u2 -> le (app f u1) (app f u2).
Proof.
  move=> LE.
  destruct f as [f Vf].
  destruct u1 as [u1 Vu1].
  destruct u2 as [u2 Vu2].
  unfold le in LE. cbn [sval] in LE. 
Admitted.

End Valid.

#[export] Instance eq_elt_equivalence : Equivalence Valid.eqb.
unfold Valid.eqb.
constructor.
- intros [u Vu].
  cbn.
Admitted.

#[export] Instance eqfun_elt_equivalence : Equivalence Valid.eqb_fun.
Admitted.
