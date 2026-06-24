(* Definition of EvalRel in terms of Valid.elt (i.e. coherent elements). *)

From Stdlib Require Import Relations List Program
     ssreflect ssrfun ssrbool.
From Stdlib Require Import Classes.RelationClasses 
  Classes.Morphisms Lia Arith.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Require findom.
Require types.
Require Import syntax.syntax.
Require Import syntax.typing.

Import SyntaxNotations.
Import SubstNotations.

Open Scope syntax_scope.

Module Raw.
  Include findom.Raw.
  Include types.
End Raw.

Module Valid. 
  Include findom.Valid.

  Definition wt (u a : Valid.elt) := 
    Raw.wt (projT1 u) (projT1 a).

  Definition is_bot (v : Valid.elt) : bool := 
    match projT1 v with 
    | Raw.bot => true
    | _ => false
    end.

  Definition is_abs (v : Valid.elt) : option Valid.finfun := 
    match v with 
    | existT _ (Raw.abs e) Vf => Some (existT _ e Vf)
    | _ => None
    end.

  Definition raw_is_tpi : forall (v : Valid.elt),
    option { a : Raw.elt & 
           { f : list (Raw.elt * Raw.elt) 
                 & Raw.valid (Raw.tpi a f) }} := 
    fun v =>
    match v with 
      | existT _ (Raw.tpi a fs) Va => 
          Some (existT _ a (existT _ fs Va))
      | _ => None
    end.

  Definition is_tpi (v : Valid.elt) :
    option (Valid.elt * option Valid.finfun).
    destruct (raw_is_tpi v) as [[a [f Vv]]|].
    - cbn in Vv. 
      eapply Some. split. exists (Raw.tpi a f). eauto.
      destruct f as [|p f].
      eapply None.
      eapply Some.
      exists (cons p f).
      move: Vv => /andP.
      move=> [_ /orP Vf].
      destruct Vf. auto. done.
    - eapply None.
  Defined.

  Definition abs (f : finfun) : elt.
    exists (Raw.abs (projT1 f)).
    destruct f as [f Vf]. 
    eassumption.
  Defined.

  Definition finfun_app (f : finfun) (u : elt) : elt.
    destruct f as [f Vf].
    destruct u as [u Vu].
    destruct (Raw.app f u) eqn:h. 
    { apply Raw.valid_app in h; eauto.
      exists e. exact h. } 
    { assert False.
      destruct (Raw.valid_app_exists Vf Vu) as [w [Aw Vw]].
      rewrite Aw in h. done. done. } 
  Defined.

  Definition graph (f : finfun) : list (elt * elt).
    destruct f as [f Vf].
    move: (Raw.valid_fun_subterms Vf) => h.
    clear Vf.
    move: h.
    induction f as [|[u v]f].
    move=> h. exact nil.
    cbn.
    move=> /andP.
    move=> [/andP h1 h2]. 
    eapply cons. destruct h1 as [Vu Vv].
    eapply ((existT _ u Vu),(existT _ v Vv)).
    eapply IHf; eauto.
  Defined.


  Definition compatible_fun (f g : finfun) : bool := 
    Raw.compatible_fun (projT1 f) (projT1 g).

  Definition coherent_with (f:finfun) : elt * elt -> bool := 
    fun '(u, v) => 
    Raw.coherent_with (projT1 f) (projT1 u, projT1 v).

  Lemma In_graph_def (f : finfun) ui vi : 
    In (projT1 ui, projT1 vi) (projT1 f) <->
    In (ui, vi) (graph f).
  Proof.
    split.
    + destruct f as [rf Vf]. move: Vf.
      induction rf as [|[uj vj]f].
      all: move=> Vf.
      all: cbn [projT1].
    - move=> h. inversion h.
    - cbn [projT1] in IHf.
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
      have [ui E1]: { UI : elt & projT1 UI = rui }. 
      { destruct f as [rf Vf]. cbn in Inrf.
        have Vui: Raw.valid rui.
        move: (Raw.valid_fun_subterms Vf) => /forallb_forall VSt.
        specialize (VSt _ Inrf). cbn in VSt. 
        move: VSt=> /andP. eauto.
        exists (existT _ rui Vui). eauto. } 
      have [vi E2]: { VI : elt & projT1 VI = rvi }. 
      { destruct f as [rf Vf]. cbn in Inrf.
        have Vvi: Raw.valid rvi.
        move: (Raw.valid_fun_subterms Vf) => /forallb_forall VSt.
        specialize (VSt _ Inrf). cbn in VSt. 
        move: VSt=> /andP. eauto.
        exists (existT _ rvi Vvi). eauto. } 
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
    unfold le in LE. cbn [projT1] in LE. 
  Admitted.

  Lemma compatible_lub (u v : elt) (h : compatible u v) :
    { w : elt & Raw.lub (projT1 u) (projT1 v) = Some (projT1 w) }.
  destruct u as [ru Vu]. destruct v as [rv Vv].
  cbn in h.
  apply Raw.compatible_lub_exists in h.
  cbn. destruct h as [rw P].
  have Vrw: Raw.valid rw. eapply (@Raw.valid_lub ru rv); eauto.
  exists (existT _ rw Vrw).  eapply P.
  Qed.

End Valid.


(* Part 1: Finite environments *)

Definition Env n := fin n -> Valid.elt.

(* Part 2: EvalRel *)

Notation " a ↦ b " := (Valid.singleton a b) (at level 70).
  
Fixpoint EvalRel {n} (t : Tm n) : Env n -> Valid.elt -> Prop := 
  match t return Env n -> Valid.elt -> Prop with 
  | var i => fun ρ b => Valid.le b (ρ i)
  | tuniv i => fun ρ b =>
             (* i.e. b == bot \/ b == tuniv i *)
             Valid.le b (Valid.tuniv i)
  | tnat => fun ρ b => 
             (* b == bot \/ b == tnat *)
             Valid.le b Valid.tnat
  | zero => fun ρ b => 
             Valid.le b Valid.zero
  | succ M => fun ρ b => 
               if Valid.is_bot b then True else
                 exists a, Valid.le b (Valid.succ a) /\ EvalRel M ρ a
  | tpi A B => fun ρ b => 
        if Valid.is_bot b then True
        else match Valid.is_tpi b with 
              | Some (a, ff) =>
                  exists (i : nat), 
                  Valid.wt a (Valid.tuniv i) /\ EvalRel A ρ a /\
                    match ff with 
                    | Some g =>         
                        forall u v, In (u,v) (Valid.graph g) -> 
                               exists x, Valid.le x u /\ Valid.wt x a /\
                                      EvalRel B (x .: ρ) v
                    | None => True 
                    end
              | None => False
             end
  | app M N => fun ρ b => 
         if Valid.is_bot b then True else 
            exists a, EvalRel M ρ (a ↦ b) /\ EvalRel N ρ a 
  | abs A M => fun ρ b => 
         match b with 
         | existT _ Raw.bot _ => True
         | existT _ (Raw.abs rg) Vg =>
             exists i a, Valid.wt a (Valid.tuniv i) /\ EvalRel A ρ a
                    /\ forall u v, In (u,v) (Valid.graph (existT _ rg Vg)) -> 
                             exists x, Valid.le x u 
                                  /\ Valid.wt x a
                                  /\ EvalRel M (x .: ρ) v
         | _ => False 
         end
  | nrec T M0 M1 => fun ρ b =>
         if Valid.is_bot b then True else False                  
  end.


(* monotonicity *)
Definition LeEnv {n} (ρ1 ρ2 : Env n) := 
  forall x, Valid.le (ρ1 x) (ρ2 x).

Lemma EvalRel_mono_env {n} (M : Tm n) (ρ ρ' : Env n) u :
  EvalRel M ρ u -> LeEnv ρ ρ' -> EvalRel M ρ' u.
Proof.
  dependent induction M.
  all: cbn [EvalRel].
  all: eauto.
  all: move=> h1 h2. 
  - (* M = x *)
    specialize (h2 f).
    eapply Valid.le_trans; eauto.
  - (* M = Abs M1 M2,  *)
    destruct u as [u Vu]. 
    destruct u eqn:Eq; try done.
    move: h1 => [i [a [WT [ER f]]]].
    exists i ,a. repeat split; eauto.
    move=> u1 v1 h3. 
    specialize (f u1 v1 h3).
    destruct f as [x [Lex [WT2 EM2]]].
    exists x. repeat split; eauto.
    eapply IHM2; eauto.
    unfold LeEnv. move=> [y|]. cbn. eauto.
    cbn. eapply Valid.le_refl.
  - (* M = app M1 M2 *)
    destruct (Valid.is_bot u); try done.
    destruct h1 as [a [E1 E2]].
    exists a. split; eauto.
  - (* M = succ M *)
    destruct (Valid.is_bot u); try done.
    destruct h1 as [a [EQ1 E]].
    exists a. split; eauto.
  - (* M = tpi M1 M2 *)
    destruct (Valid.is_bot u); try done.
    destruct (Valid.is_tpi u) as [[a [f|]]|]; try done.
    + destruct h1 as [i [WT1 [E1 h3]]].
      exists i. repeat split; eauto.
      intros u1 v1 APP.
      specialize (h3 u1 v1 APP).
      destruct h3 as [x [Lx [WT E2]]].
      exists x. repeat split; eauto.
      eapply IHM2; eauto.
      unfold LeEnv. move=> [y|]. cbn. eauto.
      cbn. eapply Valid.le_refl.
    + destruct h1 as [i [WT E]].
      exists i. split; eauto.   
Qed.    



(* Lam-edgewise *)
Lemma lam_edgewise {n} {A : Tm n} {M ρ g} : 
  EvalRel (abs A M) ρ (Valid.abs g) -> 
  exists a, EvalRel A ρ a 
       /\ forall u v, In (u,v) (Valid.graph g) -> 
         exists x, Valid.wt x a /\ EvalRel M (x .: ρ) v.
Proof.
  move=> E1.
  destruct g as [g Vg].
  cbn [EvalRel projT1 Valid.abs] in E1.
  destruct E1 as [i [a [WT [EA body]]]].
  exists a. split; eauto.
  intros u v ein.
  destruct (Raw.valid_app_exists Vg (projT2 u)) as [rw [EQ Vw]].
  specialize (body u v ein).
  remember (existT (fun x => Raw.valid x) rw Vw) as w.
  destruct body as [x [Lex [WT2 ER2]]].
  exists x. split; eauto.
Qed.

Lemma EvalRel_bot {n} (M : Tm n) (ρ : Env n) : 
  EvalRel M ρ Valid.bot.
Proof.
  destruct M eqn:EQ; cbn; try done.
  (* var *) rewrite Valid.le_bot; eauto.
Qed.


Lemma EvalRel_compatible {n} (M : Tm n) :
  forall (ρ : Env n) (a b : Valid.elt),
  EvalRel M ρ a -> EvalRel M ρ b -> Valid.compatible a b.
Proof.
  induction M.
  all: cbn [EvalRel].
  all: move=> ρ a b.
  - (* var *) 
    move=> /andP h1 /andP h2. 
    move: h1 => [C1 L1]. move: h2 => [C2 L2].
    destruct (ρ f) as [rf Vf]. cbn in *.
    eapply Raw.le_valid_compatible_pair; eauto. 
  - (* abs M1 M2 *)
    destruct a as [a Vl]. destruct b as [b Vl0].
    move=> h1 h2.
    destruct a; try done;
    destruct b; try done.
    

    remember (existT (fun f : list (findom.Raw.elt * findom.Raw.elt) => findom.Raw.valid_fun f) l Vl) as f. 
    fold Valid.finfun in f.
    remember (existT (fun f : list (findom.Raw.elt * findom.Raw.elt) => findom.Raw.valid_fun f) l0 Vl0) as g.
    fold Valid.finfun in g.

    cbn [projT1 Raw.compatible].    
    suffices H: (Valid.compatible_fun f g). 
    { rewrite Heqf Heqg in H. eapply H. } 
    clear l Vl l0 Vl0 Heqf Heqg.
    rewrite <- Valid.compatible_fun_def.
    apply /forallb_forall.
    move=> [ui vi] Ingf.
    fold (is_true (Valid.coherent_with g (ui,vi))).
    rewrite <- Valid.coherent_with_def.
    apply /forallb_forall.
    move=> [uj vj] Ingg.
    
    destruct h1 as [i1 [a1 [WT1 [E1 F1]]]].
    destruct h2 as [i2 [a2 [WT2 [E2 F2]]]].
    specialize (F1 _ _ Ingf).
    destruct F1 as [ui' [Lui' [WTi' Ei']]].
    specialize (F2 _ _ Ingg).
    destruct F2 as [uj' [Luj' [WTj' Ej']]].
    
    move: (IHM1 _ _ _ E1 E2) => Ca.

    have wt_compatible:
      forall ui ai uj aj, Valid.wt ui ai -> Valid.wt uj aj -> 
                     Valid.compatible ai aj -> 
                     Valid.compatible ui uj.
    admit.
    have C': (Valid.compatible ui' uj'). 
    eapply wt_compatible; eauto.

    

    apply /implyP. move=> h.
Admitted.

