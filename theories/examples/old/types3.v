
From Stdlib Require Import Relations List Program
     ssreflect ssrfun ssrbool.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.


From Stdlib Require Import Classes.RelationClasses Classes.Morphisms Lia Arith.

From Equations Require Import Equations.

Require Import findom.

Import findom.Raw.

From Equations Require Import Equations.
From Stdlib Require Import Wellfounded.Wellfounded.

Definition max_rk '(u, v) := max (rk u) (rk v).

Instance WellFounded_max_rk : WellFounded (fun (x y : elt*elt) => (max_rk x < max_rk y)%nat).
Admitted.

Fixpoint wt (u : elt) (a: elt) (n : nat)  := 
  match n with
  | 0 => match u , a with 
        | bot , bot => True 
        | bot, tuniv => True
        | tuniv , tuniv => True
        | tnat , tuniv => True 
        | _ , _ => False
        end
  | S m => match u , a with 
        | bot , bot => True
        | bot , tuniv => True
        | bot , a => wt a tuniv m
        | tuniv , tuniv => True 
        | tnat , tuniv => True 
        | zero , tnat => True
        | succ v , tnat => wt v tnat m
        | tpi a g , tuniv =>
            forall u v, wt u a m -> app g u = Some v -> wt v tuniv m
        | abs f , tpi a g =>
            forall u v t, wt u a m -> app f u = Some v -> app g u = Some t -> wt v t m
        | _ , _ => False 
          end
  end.

Lemma wt_max_enough : forall k u a, 
    max (rk u) (rk a) <= k -> 
    wt u a k = wt u a (max (rk u) (rk a)).
Proof.  
  elim /strong_ind.
  move => m ih u a RK.
  destruct m.
  - destruct u; destruct a; cbn in *.
    all: try lia.
    done.
  - destruct u; destruct a.
    all: cbn in *.
    all: try done.
    all: destruct m; try done.
    cbn.
Admitted.

Definition wt_core (wt : elt -> elt -> Prop) 
  (f : list (elt * elt)%type) a (G : elt -> elt) : Prop :=
  Forall (fun '(x,y) => 
     (Exists (fun '(x',y') => le x' x /\ le y y' /\ wt x' a) f)
     /\ wt y (G x)) f.

Equations? wt (u : elt) (a : elt) (n : nat) : Prop 
  by wf  Nat.lt :=
  wt bot a := if rk a < n then wt a tuniv (rk a) else False ;
  wt tuniv tuniv := True ;
  wt tnat tuniv := True ;
  wt zero tnat := True ;
(*  wt (succ n) tnat := wt n tnat ;
  wt (tpi a g) tuniv := 
    forall u, rk u < rk (tpi a g) -> wt u a -> forall v, app g u = Some v -> wt v tuniv ; *)
  wt _ _ := False.

(* -------------------------------------------------------------- *)

(*
Fixpoint wt_tpi' (wt: elt -> elt -> Prop) b g i : Prop :=
    match g with 
    | ((u,v) :: g') => wt u b /\ wt v (tuniv i) /\ wt_tpi' wt b g' i
    | nil => True
    end.
Fixpoint wt_abs' (wt:elt -> elt -> Prop) f a g : Prop := 
    match f with 
    | (u,v) :: f' => wt u a 
                     /\ exists w, app g u = Some w /\ wt v w
                     /\ wt_abs' wt f' a g
    | nil => True
    end.

Fixpoint wt (u:elt) (a : elt) { struct u } : Prop := 
  match u with 
  | bot => valid a
  | tuniv i => match a with 
               | tuniv j => (i < j)%nat
               | _ => False
              end
  | tpi b g => 
      match a with 
      | tuniv i => 
          wt_tpi' wt b g i /\ wt b (tuniv i)
          /\ valid (tpi b g) 
      | _ => False 
      end    
  | abs f => 
      match a with 
      | tpi b g =>  
          wt_abs' wt f b g /\
          valid (abs f) /\ valid (tpi b g) 
      | _ => False
      end
  | _ => False
end.

Notation wt_tpi := (wt_tpi' wt).
Notation wt_abs := (wt_abs' wt).
*)

Fixpoint ForallT (A : Type) (P : A -> Type) (l : list A) : Type :=
  match l with
  | nil => True
  | x :: l => P x * ForallT P l
  end.



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
    wt_pi_fun g a ->
    wt a tuniv ->
    wt (tpi a g) tuniv

  | wt_abs a f g :
    wt_abs_fun f a g ->
    (* make sure tm is valid *)
    valid (abs f) ->
    (* make sure type is a type *)
    wt (tpi a g) tuniv ->
    wt (abs f) (tpi a g)
with wt_pi_fun : list (elt * elt) -> elt -> Type :=
  | wt_pi_nil a : 
    wt a tuniv ->
    wt_pi_fun nil a
  | wt_pi_cons a ui vi w g :
    wt ui a ->
    wt vi tuniv ->
    wt_pi_fun g a ->
    valid_fun ((ui,vi) :: g) ->
    wt_pi_fun ((ui,vi) :: g) a
with wt_abs_fun : list (elt * elt) -> elt -> list (elt * elt) ->  Type :=
  | wt_abs_nil a g : wt_abs_fun nil a g
  | wt_abs_cons ui vi f a g t :
    wt ui a ->
    app g ui = Some t ->
    wt vi t ->
    wt_abs_fun f a g ->
    valid_fun ((ui,vi) :: f) ->
    wt_abs_fun ((ui,vi) :: f) a g
  .

From Stdlib Require Import ProofIrrelevance.

(* Uniqueness of [wt] (and its mutual companions) derivations.
   Constructors that hold positive content recurse on the sub-derivations;
   propositional witnesses (the [valid _] booleans and the [app g ui = Some t]
   equality) are unified via the [proof_irrelevance] axiom. *)
Fixpoint wt_unique u a (h1 h2 : wt u a) {struct h1} : h1 = h2
with wt_pi_fun_unique g a (h1 h2 : wt_pi_fun g a) {struct h1} : h1 = h2
with wt_abs_fun_unique f a g (h1 h2 : wt_abs_fun f a g) {struct h1} : h1 = h2.
Proof.
  - dependent destruction h1; dependent destruction h2;
      try reflexivity.
    + (* wt_bot *) f_equal. apply wt_unique.
    + (* wt_succ *) f_equal. apply wt_unique.
    + (* wt_tpi *) f_equal.
         apply wt_pi_fun_unique.
         apply wt_unique.
    + (* wt_abs *) f_equal;
        [ apply wt_abs_fun_unique
        | apply proof_irrelevance
        | apply wt_unique ].
  - dependent destruction h1; dependent destruction h2.
    (* wt_pi_nil *)
    f_equal. apply wt_unique.
    (* wt_pi_cons *)
    f_equal; [apply wt_unique | apply wt_unique | apply wt_pi_fun_unique | apply proof_irrelevance ].
  - dependent destruction h1; dependent destruction h2.
    (* wt_abs_nil *)
    reflexivity.
    (* wt_abs_cons: equate the existential t via injectivity of Some on app *)
    match goal with
    | E1 : app ?g ?u = Some ?t1, E2 : app ?g ?u = Some ?t2 |- _ =>
        assert (Et : t1 = t2) by congruence; subst t1
    end.
    f_equal;
      [ apply wt_unique
      | apply proof_irrelevance
      | apply wt_unique
      | apply wt_abs_fun_unique
      | apply proof_irrelevance ].
Qed.

(* app f ui = lub { vj | uj <= ui  and (uj,vj) in f } *)

(* For some functions: we might want this property
 
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

(* If we restrict to these elements, then we can think about this 
   stronger typing rule for functions *)
(*
Lemma wt_abs_ext a f g :
    (forall u, exists v, wt v a /\ app f u = app f v) ->
    (forall u w v, app g u = Some w -> app f u = Some v -> wt v w) ->
    (* make sure both tm and type are valid *)
    (valid (abs f)) ->
    (valid (tpi a g)) <-> 
    wt (abs f) (tpi a g)
  .
Abort.
*)

Lemma valid_tpi1 a g : valid (tpi a g) -> valid a.
move=> /andP [h1 h2]. exact h1.
Qed.
Lemma valid_tpi2 a g : valid (tpi a g) -> valid_fun g.
move=> /andP [h1 h2]. exact h2.
Qed.
Lemma valid_abs f : valid (abs f) -> valid_fun f.
move=> /andP [h1 _]. exact h1.
Qed.
Hint Resolve valid_tpi1 valid_tpi2 valid_abs : valid.

Fixpoint wt_valid_tm u a : wt u a -> valid u
with wt_pi_fun_valid f a : wt_pi_fun f a -> valid (tpi a f).
- induction 1; eauto.  
- induction 1. 
  + cbn. apply /andP. split; eauto.
  + apply /andP. split; eauto. fold valid.
    eapply valid_tpi1; eauto.
Qed.

Lemma wt_valid_ty u a : wt u a -> valid a.
induction 1; eauto using wt_valid_tm.
Qed.

Lemma wt_abs_fun_valid_fun f a g : wt_abs_fun f a g -> valid_fun f.
Proof.
  induction 1; eauto.
Qed.

Hint Resolve wt_valid_tm wt_valid_ty wt_pi_fun_valid
  wt_abs_fun_valid_fun : valid.

(* Only bot has type bot *)
Lemma wt_bot_inv u : wt u bot -> u = bot.
Proof. move=> h. inversion h. done. Qed.

(* FinMem-a-in-U (type-in-type: every typed term's type lives in tuniv). *)
Lemma wt_ty_tuniv u a : wt u a -> wt a tuniv.
Proof.
  induction 1; eauto using wt_tuniv, wt_tnat, wt_tpi.
Qed.

Lemma wt_pi_fun_wt g a : wt_pi_fun g a -> wt a tuniv.
Proof. 
  induction 1; eauto.
Qed.

Lemma In_rk_fun1 u v f:
  In (u, v) f -> rk u <= rk_fun f.
Proof.
  induction f as [|[ui vi]f]; eauto. cbn. done.
  move=> [h1|h1].
  inversion h1; subst. cbn. lia.
  apply IHf in h1. cbn. lia.
Qed.

Lemma In_rk_fun2 u v f:
  In (u, v) f -> rk v <= rk_fun f.
Proof.
  induction f as [|[ui vi]f]; eauto. cbn. done.
  move=> [h1|h1].
  inversion h1; subst. cbn. lia.
  apply IHf in h1. cbn. lia.
Qed.

Lemma rk_abs f : 
  valid (abs f) -> 1 <= rk_fun f.
Proof.
  move=> /andP [Vf Nf]. fold valid (valid_fun f) in Vf.
  destruct f as [|[u v]f]. done.
  apply valid_fun_head in Vf.
  apply val_nbot in Vf.
  cbn.
  destruct v; try done.
  all: cbn.
  all: lia.
Qed.

(*
Module WTL.

Record WTLemmas k := MkLemmas { 
    wt_le  : forall u a b, max (rk u) (max (rk a) (rk b)) <= k -> wt u a -> 
       le a b -> forall i, wt a (tuniv i) -> wt b (tuniv i) -> wt u b ;
    wt_lub : forall u a, max (rk u) (rk a) <= k -> wt u a -> 
       forall v w, wt v a -> lub u v = Some w -> wt w a ;
    wt_instantiate : 
       forall b f i ui, wt (tpi b f) (tuniv i) ->                
             wt ui b -> 
             max (rk (tpi b f)) (rk ui) <= k ->
             forall w, app f ui = Some w -> wt w (tuniv k) ;
    wt_app : forall f b g u, max (rk_fun f) (max (rk (tpi b g)) (rk u)) <= k ->
            wt (abs f) (tpi b g) -> wt u b -> 
            forall t r, app g u = Some r -> app f u = Some t -> wt r t 
}.

(*
finMemFun-upward : (g : FinFun) (a b : FinEl) (f h : FinFun) ->
  LeCode a b -> Coherent a -> Coherent b ->
  CoherentFunTail f -> CoherentFunTail h -> LeFunCode f h ->
  FinMemFun g a f -> FinMem b UCode -> FinMemAllU h b -> FinMemFun g b h
*)

Definition wt_fun g a f := 
   (forall ui vi, 
        List.In (ui,vi) g -> wt ui a) /\
    (forall ui vi w, 
        List.In (ui,vi) g -> app f ui = Some w -> wt vi w).

Lemma wt_le_fun : forall g a b f h i, 
    le a b -> valid a -> valid b -> valid_fun f -> valid_fun h -> 
    le_fun f h -> 
    wt_fun g a f ->
    wt (tpi b h) (tuniv i) -> 
    wt_fun g b h.
Proof.
  induction g as [|[u v]g].
  - intros. split; intros; done.
  - move=> a b f h i LEa Va Vb Vf Vh LEf [WTg1 WTg2] WTP.
    split.
    + admit.
    + move=> ui vi w [h1|h2] APP.
      -- inversion h1.  subst. clear h1.
         destruct (valid_app_exists Vf Vui) as [w [APPf Vw]].
         move: (le_fun_mono Vf Vh LEf APP)
         specialize (WTg2 _ _ _ ltac:(left; eauto)
      -- 

Lemma WTLs : forall k, WTLemmas k.
Proof.
  elim /strong_ind.
  move=> m ih.
  constructor.
  - (* wt_le *)
    move=> u a b RK WTu LE i0 WTa WTb.
    dependent destruction WTu.
    + eapply wt_bot; eauto. 
    + apply le_tuniv_inv in LE. subst. 
      eapply wt_tuniv; eauto.
    + apply le_tuniv_inv in LE. subst.
      eapply wt_tnat; eauto.
    + apply le_tnat_inv in LE. subst.
      eapply wt_zero; eauto.
    + eapply le_tnat_inv in LE. subst.
      eapply wt_succ; eauto.
    + apply le_tuniv_inv in LE. subst.    
      eapply wt_tpi; eauto.
    + (* abs case: know wt (abs f) (tpi a g), 
         WTP wt (abs f) (tpi a1 g1) where a <= a1 and g <= g1  *)
      destruct (le_tpi_inv LE) as [a1 [g1 [-> [LEa LEg]]]].
      cbn in RK. fold rk rk_fun in RK. 
      

      have WTpi: wt (tpi a g) (tuniv (max i0 i)).
      { eapply wt_cumul; eauto. lia. }
      have WTpi1: wt (tpi a1 g1) (tuniv (max i0 i)).
      { eapply wt_cumul; eauto. lia. }
      
      have Vf: valid_fun f. eauto with valid.
      have Vtpi1: valid (tpi a1 g1). eauto with valid.
      have Vg1 : valid_fun g1. eapply valid_tpi2; eauto.  
      have Vtpi : valid (tpi a g). eauto with valid.
      have Vg : valid_fun g. eapply valid_tpi2; eauto.
      
      eapply wt_abs; eauto.
      ++ (* dom elts are wt ui a1 *)
        move=> ui vi Inf.
        have RKui : rk ui <= rk_fun f. eapply In_rk_fun1; eauto.
        have RKvi : rk vi <= rk_fun f. eapply In_rk_fun2; eauto.
        have Vui: valid ui. eauto with valid.
        move: (valid_app_exists Vg Vui) => [wi [Ai Vwi]].
        eapply wt_le; eauto. lia.
        inversion WTa. eauto.
        inversion WTb. eauto.
    ++ (* rng elts are wt *)
      move=> ui vi w1 Inf APP1.
      have RKui : rk ui <= rk_fun f. eapply In_rk_fun1; eauto.
      have RKvi : rk vi <= rk_fun f. eapply In_rk_fun2; eauto.
      have Vui: valid ui. eauto with valid.
      move: (valid_app_exists Vg Vui) => [w [APP Vw]].
      move: (rk_app APP) => RKw.
      move: (rk_app APP1) => RKw1.
      move: (rk_abs H1) => RKf.
      have WTvi: wt vi w. 
      { eapply H0; eauto. } 
      have LFM: le w w1. 
      { eapply (le_fun_mono Vg Vg1 LEg Vui APP APP1). } 
      (* Given wt vi w and w <= w1 want to show wt vi w1 *)

      (* BUT to apply IH (i.e. H2) we need to know that 
         both w and w1 have a common universe level. *)
      (* we know that w is good by assumption *)
      have [j WTw] : exists j, wt w (tuniv j).
      { eapply wt_ty_tuniv; eauto.  } 

      (* but we need to somehow know that w1 is well typed. *)
      have WTw1: wt w1 (tuniv i0).
      { specialize (ih (max (rk_fun f) (max (max (rk a) (rk_fun g)) 
                                          (max (rk a1) (rk_fun g1)))) ltac:(lia)).
        move: (@wt_instantiate _ ih _ _ _ _ WTb) => LTI. 
        cbn in LTI. fold rk_fun in LTI.
        specialize (LTI ltac:(lia)).
        
        
admit.  (* app g1 ui = w1i and  
                         where wt (tpi a g1) (tuniv i0) *) }  

      destruct (~~ is_nil g) eqn:Ng_g.
      -- destruct (~~ is_nil g1) eqn:Ng_g1.
         ++ 
            Unshelve.
            have Vw1i: valid w1i by eapply (valid_app Vg1 Vui A1i).
            move: (wt_ty_tuniv WTvi) => [j WTwi].
            move: (H2 _ _ _ Inf Ai) => Hwt.
            have WTwi': (wt wi (tuniv (max (max i0 i) j))).
            { eapply wt_cumul. eauto. lia. } clear WTwi.
            eapply H2; eauto.
            eapply wt_cumul. eauto. lia.
         ++ destruct g1; try done.
            move: (valid_fun_not_le_fun_nil Ng_g Vg LEf). done.
      -- destruct g; try done.
         destruct (~~ is_nil g1) eqn:Ng_g1.
         ++ have Vw1i: valid w1i by eapply (valid_app Vg1 Vui A1i).
            move: (H2 _ _ bot Inf (app_nil_eq _)) => Hwt.
            eapply Hwt. eapply wt_bot; eauto. 
            instantiate (2:= max i0 i). instantiate (1:= (S (max i0 i))).
            eapply wt_tuniv. lia.
            eapply le_bot. 
            eauto.
         ++ destruct g1; try done.
            rewrite app_nil_eq in A1i. inversion A1i. subst.
            move: (H1 _ _ bot Inf (app_nil_eq _)) => Hwt.
            exact Hwt.
Admitted.
*)

(*
Lemma wt_WT u a : wt u a -> WT u a.
induction 1.
all: split; [ move => i0 WTa b LE WTb 
            | move=> v w Wtv LUB;
              inversion LUB; subst; try done;
              destruct v; try done;
              try solve [cbn in LUB; inversion LUB; 
                  subst; econstructor; eauto]
            | try (move=> w b f EQ1 EQ2; inversion EQ1; subst)
  ].
(* bot *)
- eapply wt_bot; eauto.
(* tuniv *)
- apply le_tuniv_inv in LE. subst. 
  eapply wt_tuniv; eauto.
- cbn in LUB.
  destruct (i=?n) eqn:EQ. rewrite Nat.eqb_eq in EQ. subst.
  inversion LUB. done. inversion LUB.
(* tnat *)
- apply le_tuniv_inv in LE. subst.
  eapply wt_tnat; eauto.
(* zero *)
- apply le_tnat_inv in LE. subst.
  eapply wt_zero; eauto.
(* succ *)
- eapply le_tnat_inv in LE. subst.
  eapply wt_succ; eauto.
- cbn in LUB. destruct (lub u v) eqn:EQ; try done. inversion LUB.
  inversion Wtv. subst.
  eapply WT_lub in EQ; eauto. eapply wt_succ; eauto. 
(* tpi *)
- apply le_tuniv_inv in LE. subst.    
    eapply wt_tpi; eauto.
(* tpi - lub *)
- destruct (compatible_fun g l) eqn:C1; try done.
  destruct (lub a v) eqn:L1; try done.
  inversion H6. clear H6.
  (* e = lub a v *)
  inversion Wtv; subst. clear Wtv.
  have Va : valid a. eauto with valid.
  have Vv : valid v. eauto with valid.
  have Ve : valid e. eauto with valid.
  eapply wt_tpi; eauto.
  + move=> ui vi InApp.
    destruct (in_app_or _ _ _ InApp) as [Ing|Inl].
      ++ (* tuple is in the original list *) 
         specialize (H0 _ _ Ing). 
         eapply WT_le; eauto.
         eapply le_lub_left; eauto.
         eapply lub_compatible; eauto.
         eapply WT_lub; eauto.
      ++ (* tuple is in l -- can't use IH for WT_le *)
        move: (H9 _ _ Inl) => WTui.
        eapply WT_le; eauto.
        eapply le_lub_right; eauto.
        eapply lub_compatible; eauto.
        eapply WT_lub; eauto.
    + move=> ui vi InApp.
      destruct (in_app_or _ _ _ InApp) as [Ing|Inl]; eauto.
    + apply /andP. fold valid (valid_fun (g ++ l)).
      split. eauto.
      move: H3 => /andP [_ Vg]. fold valid (valid_fun g) in Vg.
      move: H11 => /andP [_ Vl]. fold valid (valid_fun l) in Vl.
      eapply valid_append; eauto.
*)

(*
Lemma 2 
If u : a and a <= b, then u : b.
*)
Fixpoint wt_le u a :
  wt u a -> forall b, le a b -> wt a tuniv -> wt b tuniv -> wt u b
with wt_pi_le f a :
  wt_pi_fun f a ->
  forall b, le a b -> wt a tuniv -> wt b tuniv -> wt_pi_fun f b
with wt_abs_le f a1 g1 :
  wt_abs_fun f a1 g1 -> forall a2, le a1 a2 -> forall g2, le_fun g1 g2
     -> wt (tpi a1 g1) tuniv -> wt (tpi a2 g2) tuniv -> wt_abs_fun f a2 g2.
Proof.
  - move=> h.
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

  - move=> h.
    dependent destruction h.
    all: move=> b LE WTa WTb.
    + eapply wt_pi_nil; eauto.
    + eapply wt_pi_cons.
      (* dom elts are wt ui b *)
      have Vui: valid ui by eauto with valid.
      eapply wt_le; eauto.
      auto.
      eapply wt_pi_le; eauto.
      auto.
  - (* abs_fun *)
    move=> h.
    dependent destruction h.
    all: move=> a2 LEa g2 LEg WTa WTb.
    + eapply wt_abs_nil.
    + inversion WTa.
      inversion WTb. subst.
      have Vui: valid ui. eauto with valid.
      have Vg: valid_fun g. eauto with valid.
      have Vg2: valid_fun g2. eauto with valid.
      destruct (valid_app_exists Vg2 Vui) as
        [w2 [APP2 Vw2]].

      have WTt : wt t tuniv.
      { admit. }
      (* need to know that wt_pi_fun g a
         and app g ui = Some t
         and wt ui a
         implies  wt t tuniv *)
      have Wtui1 : wt ui a2.
      { admit. }

      have WTw2 : wt w2 tuniv.
      { admit. }
      (* need to know that
         wt_pi_fun g2 a2 and app g2 ui = Some w2
         and wt ui a2
         implies  wt w2 tuniv *)

      have LFM: le t w2.
      { eapply (le_fun_mono Vg Vg2 LEg Vui e APP2). }
      have WTvi: wt vi w2.
      { eapply wt_le; eauto. }
      eapply wt_abs_cons; eauto.
Admitted.

(*
Lemma wt_pi_fun_lub f a i :
  wt_pi_fun f a i -> forall g, wt_pi_fun g a i -> wt_pi_fun (f ++ g) a i.
Proof.
  induction f.
  all: move=> WTf g WTg.
  all: inversion WTf; subst.
  all: cbn; eauto.
  eapply wt_pi_cons; eauto.
Qed.
*)

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
Qed.

(* - If u : a, v : a, and u and v are compatible, then lub u v : a *)
Fixpoint wt_lub u a (h: wt u a) {struct h}
  : forall v w, wt v a -> lub u v = Some w -> wt w a
with wt_pi_fun_lub f1 a1 (h: wt_pi_fun f1 a1) {struct h} :
  wt a1 tuniv ->
  forall f2 a2, wt a2 tuniv -> wt_pi_fun f2 a2 -> forall b, lub a1 a2 = Some b ->
  compatible_fun f1 f2 ->
  wt_pi_fun (f1 ++ f2) b
with wt_pi_fun_lub_right f a1 (h: wt_pi_fun f a1) {struct h} :
  wt a1 tuniv ->
  forall a2, wt a2 tuniv -> forall b, lub a2 a1 = Some b ->
  wt_pi_fun f b.
Proof.
  - dependent destruction h.
  all: move=> v w1 Wtv LUB.
  all: inversion LUB; subst; try done.
  all: destruct v; try done.
  all: try solve [cbn in LUB; inversion LUB;
                  subst; econstructor; eauto].
  + destruct (lub u v) eqn:EQ; try done.
    cbn in H0. inversion H0. subst.
    inversion Wtv; subst.
    eapply wt_succ; eauto.
  + (* u = tpi a g, v=tpi v l *)
    destruct (compatible_fun g l) eqn:C1; try done.
    destruct (lub a v) eqn:L1; try done.
    inversion H0. clear H0. subst.
    (* e = lub a v *)
    clear LUB.
    inversion Wtv; subst. clear Wtv.
    eapply wt_tpi.
    eapply wt_pi_fun_lub in H1; eauto using wt_pi_fun_wt.
    eapply wt_lub in L1; eauto. 
  + cbn in LUB.
    destruct (compatible_fun f l) eqn:C1; try done.
    inversion LUB; subst w1; clear LUB.
    inversion Wtv as [| | | | | |a2 l2 g2 j Hui2 Hvi2 Vabs2 Vtpi2]; subst;
      clear Wtv.
    have Vf: valid_fun f. eauto with valid.
    have Vl: valid_fun l. eauto with valid.
    have Vfl : valid_fun (f ++ l) by eapply valid_append; eauto.
    have Nfl : ~~ is_nil (f ++ l) by destruct f; destruct l; cbn in *.
    eapply wt_abs; eauto.
    eapply wt_abs_fun_lub; eauto.
    apply /andP. split; auto.
 - (* wt_pi_fun_lub *)
   move=> WTa1 f2 a2 WTa2 WTf2 b LUB. 
   dependent destruction h.
   all: cbn.
   have LE: le a2 b. { eapply le_lub_right; 
                       eauto using lub_compatible with valid. } 
   ++ move=> _. 
      eapply (wt_pi_fun_lub_right _ _ WTf2 WTa2 _ WTa1 _ LUB).
   ++ move=> /andP [Cui Cf]. 
      eapply wt_pi_cons; eauto.
      eapply wt_le; eauto.
      eapply le_lub_left; eauto using lub_compatible with valid.
      rewrite app_comm_cons.
      eapply valid_append; eauto.
      eauto with valid.
      apply /andP. split; auto.
      
 - (* wt_pi_fun_lub_right *)
   move=> WTa1 a2 WTa2 b LUB.
   dependent destruction h.
   ++ eapply wt_pi_nil.
      eapply (@wt_lub a2 tuniv WTa2 a); eauto.
   ++ eapply wt_pi_cons. 
      eapply wt_le; eauto.
      eapply le_lub_right; eauto using lub_compatible with valid.
      auto.
      eauto.
      auto.
Admitted. (* need termination argument *)

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
  eapply wt_abs; eauto. inversion H2; eauto.
  apply /andP. split; eauto.
Qed.


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
    inversion WT. subst. inversion H4. subst.
    eapply wt_bot.
    admit.
    (* eapply wt_bot; eauto. *)
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


(*
Lemma 3 If Πaf : Uk and f = (u1 → t1,...,un → tn), then ui : a and f (ui) : Uk. 

This version is not the same as it doesn't say anything 
intensional about f.

*)

(*
Lemma lemma3_1 a f k : 
  wt (tpi a f) (tuniv k) -> 
  forall ui vi, In (ui,vi) f -> wt ui a.
Proof.
  intros.
  inversion H. eauto.
Qed.
*)

(*
Lemma wt_instantiate a f k : 
  wt (tpi a f) (tuniv k) -> 
  forall ui w, wt ui a -> app f ui = Some w -> wt w (tuniv k).
Proof.
  induction f as [|[u v]f].
  all: move=> WT; inversion WT; subst; clear WT.
  all: move=> ui vi w. 
  - rewrite app_nil_eq. move=> EQ. inversion EQ. subst.
    eapply wt_bot; eauto.
    admit.
  - rewrite app_spec. cbn. rewrite <- app_spec.
    destruct (compatible u ui && le u ui) eqn:EQ.
    + move=> LUB. destruct (app f ui) eqn:APP; try done.
      cbn [valid] in H5. fold (valid_fun ((u,v)::f)) in H5.
      move: H5 => /andP [Va Vuf]; try done.
      have WTv : wt v (tuniv k). 
      { eapply H3; eauto. left. reflexivity. } 
      have WT: wt (tpi a f) (tuniv k).
      { destruct (~~ is_nil f) eqn:Nf.
        - eapply wt_tpi; eauto.
        move=> uj vj Infj. eapply H2; eauto. right; eauto.
        move=> uj vj Infj. eapply H3; eauto. right; eauto.
        apply /andP. fold valid. fold (valid_fun f).
        split; auto. eauto with valid.
      - destruct f; try done.
        eapply wt_tpi; eauto; try done.
        apply /andP. auto. 
    } 
    specialize (IHf WT).
    eapply wt_lub in LUB; eauto.
    + move=> APP.
      eapply IHf; eauto.
      eapply wt_tpi; eauto.
      move=> uj vj Infj. eapply H2; eauto. right; eauto.
      move=> uj vj Infj. eapply H3; eauto. right; eauto.
      move: H5 => /andP [Va Vf]. fold valid in Va, Vf.
      apply /andP. fold valid. split; auto.      
      fold (valid_fun f).
      eapply valid_fun_tail; eauto.
Admitted.

Lemma lemma3_2 a f k : 
  wt (tpi a f) (tuniv k) -> 
  forall ui vi w, In (ui,vi) f -> app f ui = Some w -> wt w (tuniv k).
Proof.
  intros.
  inversion H. subst.
  eapply wt_instantiate; eauto.
Qed.
*)

(*
Lemma 4:

If w : Πaf and w = (u1 → t1,...,un → tn), then ui : a
and w(ui) : f (ui).
*)

(*
Lemma lemma4_1 w a f :
  wt (abs w) (tpi a f) ->
  forall ui vi, In (ui, vi) w -> wt ui a.
Proof.
  move=> WT ui vi In.
  inversion WT as [| | | | | |aX wX fX j HuiAll HviAll Vabs WTtpi]; subst.
  have Vw : valid_fun w. eauto with valid.
  have Vui : valid ui.
  { move: (valid_fun_subterms_prop Vw In) => [Vu _]. done. }
  have Vtpi : valid (tpi a f). eauto with valid.
  destruct (app_tpi_exists Vtpi Vui) as [t [At Vt]].
  eapply HuiAll; eauto.
Qed.

Lemma lemma4_2 w a f :
  wt (abs w) (tpi a f) ->
  forall ui vi r t, In (ui, vi) w ->
           app w ui = Some r -> app f ui = Some t -> wt r t.
Proof.
  move=> WT ui vi r t In Aw Af.
  eapply wt_app; eauto.
  eapply lemma4_1; eauto.
Qed.
*)


                                       
(*
 if u : a then lv(u) <= lv(a) and if u : Uk then lv(u) < k 
*)

Lemma wt_level u a :
  wt u a -> level u <= level a.
Proof.
  move=> h. 
  induction h.
Abort.


(*
Lemma 5 If w : Π b f and b <= a, then for any u : a there exists v : b such that v <= u and w(u) = w(v).

Proof We write w = (u1 → l1,...,un → ln) with ui : b and 
   li : f (ui). We then
have w(u) = w(v) 
   with v = ∨{ui | ui <= u} and v : b by Lemma 2.

*)

(*
(* Stronger form: for any x with le v x and le x u, app w u = app w x. *)
Lemma app_down_strong w b f :
  wt (abs w) (tpi b f) -> forall u a,
      le b a ->
      wt u a ->
      { v & (wt v b) * ( ( le v u) * 
        (forall x, valid x -> le v x -> le x u -> app w u = app w x)) }.
Proof.
  induction w as [|[ui vi] w'].
  - move=> WT. inversion WT. done.
  - move=> WT u a LE WTu.
    have Vu : valid u by eauto with valid.
    have Vtpi : valid (tpi b f) by eauto with valid.
    have Vabs : valid (abs ((ui,vi) :: w')) by eauto with valid.
    have Vb : valid b.
    { cbn in Vtpi. move: Vtpi => /andP [? _]. done. }
    move: Vabs => /andP [Vw _]. fold (valid_fun ((ui,vi) :: w')) in Vw.
    have Vui : valid ui by eapply key_valid; eauto using valid_fun_head.
    have Vvi : valid vi by eapply val_valid; eauto using valid_fun_head.
    have [wi [Awi Vwi]] : exists wi, app f ui = Some wi /\ valid wi
      by eapply app_tpi_exists; eauto.
    inversion WT as [| | | | | |aX wX fX j Hui2 Hvi2 VabsX VtpiX]; subst.
    have WTui_b : wt ui b. admit.
    destruct (~~ is_nil w') eqn:Nw.
    + (* w' non-nil: use IH *)
      have WTw' : wt (abs w') (tpi b f) by eapply wt_abs_pred; eauto.
      destruct (IHw' WTw' u a LE WTu) as [v' [WTv' [LEv' IH2]]].
      have Vv' : valid v' by eapply wt_valid_tm; eauto.
      destruct (le ui u) eqn:LEui.
      * (* le ui u = true *)
        have Cui : compatible ui u by eapply le_valid_compatible; eauto using le_refl.
        have Cuiv' : compatible ui v'.
        { apply compatible_sym. eapply comp_down; eauto.
          apply compatible_sym; eauto. }
        destruct (compatible_lub_exists Cuiv') as [v_new EQv].
        have Vv_new : valid v_new. { eapply (valid_lub Vui Vv' EQv). }
        have LE_uivn : le ui v_new. { eapply (le_lub_left Cuiv' EQv Vui Vv'). }
        have LE_vvn : le v' v_new. { eapply (le_lub_right Cuiv' EQv Vui Vv'). }
        have LE_vnu : le v_new u. { eapply (@le_sup_lub ui v' v_new u LEui LEv' EQv). }
        have WT_vnew : wt v_new b. { eapply wt_lub; [exact WTui_b | exact WTv' | exact EQv]. }
        exists v_new. split; [|split]; eauto.
        move=> x Vx LE_vnx LE_xu.
        have LE_uix : le ui x by eapply le_trans with (v := v_new); eauto.
        have LE_v'x : le v' x by eapply le_trans with (v := v_new); eauto.
        have Cuix : compatible ui x by eapply le_valid_compatible; eauto.
        have App_eq : app w' u = app w' x by apply IH2; eauto.
        rewrite app_spec. cbn. rewrite <- app_spec.
        rewrite Cui LEui Cuix LE_uix /=.
        rewrite App_eq. reflexivity.
      * (* le ui u = false *)
        exists v'. split; [|split]; eauto.
        move=> x Vx LE_v'x LE_xu.
        have LE_uix : le ui x = false.
        { destruct (le ui x) eqn:E; try reflexivity.
          have Luiu : le ui u by eapply le_trans with (v := x); eauto.
          rewrite LEui in Luiu. done. }
        have App_eq : app w' u = app w' x by apply IH2; eauto.
        rewrite app_spec. cbn. rewrite <- app_spec.
        rewrite LEui LE_uix !Bool.andb_false_r /=.
        exact App_eq.
    + (* w' nil *)
      destruct w'; try done.
      destruct (le ui u) eqn:LEui.
      * (* le ui u = true *)
        have Cui : compatible ui u by eapply le_valid_compatible; eauto.
        exists ui. split; [|split]; eauto.
        move=> x Vx LE_uix LE_xu.
        have Cuix : compatible ui x by eapply le_valid_compatible; eauto.
        rewrite app_spec. cbn.
        rewrite Cui LEui Cuix LE_uix /=.
        rewrite !lub_bot_r. reflexivity.
      * (* le ui u = false *)
        exists bot. split; [|split].
        -- eapply wt_bot; eauto. admit.
        -- eapply le_bot.
        -- move=> x Vx LE_botx LE_xu.
           have LE_uix : le ui x = false.
           { destruct (le ui x) eqn:E; try reflexivity.
             have Luiu : le ui u by eapply le_trans with (v := x); eauto.
             rewrite LEui in Luiu. done. }
           rewrite app_spec. cbn.
           rewrite LEui LE_uix !Bool.andb_false_r /=.
           reflexivity.
Admitted.

Lemma app_down w b f :
  wt (abs w) (tpi b f) -> forall u a,
      le b a ->
      wt u a -> exists v, wt v b /\ le v u /\ app w u = app w v.
Proof.
  move=> WT u a LE WTu.
  destruct (app_down_strong WT LE WTu) as [v [WTv [LEv HStr]]].
  have Vv : valid v by eapply wt_valid_tm; eauto.
  exists v. split; [|split]; eauto.
  eapply HStr; eauto. eapply le_refl; eauto.
Qed.
*)

(* NOT TRUE *)
Lemma wt_compatible:
  forall ui ai, wt ui ai -> forall uj aj, wt uj aj -> 
                               compatible ai aj -> 
                               compatible ui uj.
Proof.
  move=> ui ai h.
  induction h.
  all: move=> ui ai WTi CC.
  all: try solve [destruct ui; done].
  all: destruct ai; try done.
  all: try match goal with [ H : wt _ bot |- _ ] => inversion WTi; subst; done end.
  all: inversion CC; subst; clear CC.
Abort.

(* ------------------------------------------------------------- *)
(*
Inductive is_type : elt -> Prop :=
  | is_bot : is_type bot
  | is_tuniv i : is_type (tuniv i)
  | is_tnat : is_type tnat
  | is_tpi a f :
    valid (tpi a f) ->
    is_type a ->
    (forall u v, In (u,v) f -> wt u a) ->
    (forall u v, In (u,v) f -> is_type v) ->
    is_type (tpi a f).

Lemma is_type_valid a : is_type a -> valid a.
Proof.
  induction 1; cbn; auto.
Qed.

Hint Resolve is_type_valid : valid.


(* 
If a : Uj , then a type. 
If a type, b type, and a,b are compatible, then a ∨ b type. 
If Π a (u1 → t1,...,un → tn) type and u1 → t1,...,un → tn is a
minimal description, then ui : a and ti type.
*)

Lemma wt_is_type a i :
  wt a (tuniv i) -> is_type a.
Proof.
  move=> h.
  remember (tuniv i) as t eqn:Ht.
  move: i Ht.
  induction h; move=> k Heq; try discriminate.
  - constructor.
  - constructor.
  - constructor.
  - inversion Heq; subst j.
    apply is_tpi.
    + eauto.
    + eauto.
    + eauto.
    + eauto.
Qed.

Lemma is_type_lub a b :
  is_type a -> is_type b -> forall c, lub a b = Some c -> is_type c.
Proof.
  move=> Ta. move: b.
  induction Ta as [ | i | | a0 f0 Va Ta0 IHa0 Hwt_f0 Hist_f0 IH_f0].
  - move=> b Tb c L. cbn in L. inversion L; subst. exact Tb.
  - move=> b Tb c L.
    inversion Tb; subst; cbn in L; try discriminate.
    + inversion L; subst. constructor.
    + destruct (i =? i0) eqn:E; try discriminate.
      inversion L; subst. constructor.
  - move=> b Tb c L.
    inversion Tb; subst; cbn in L; try discriminate.
    + inversion L; subst. constructor.
    + inversion L; subst. constructor.
  - move=> b Tb c L.
    inversion Tb as [| | | a1 f1 Va1_tpi Ta1 Hwt_f1 Hist_f1];
      subst; cbn in L; try discriminate.
    + inversion L; subst. eapply is_tpi; eauto.
    + destruct (compatible_fun f0 f1) eqn:CF; try discriminate.
      destruct (lub a0 a1) eqn:La; try discriminate.
      cbn in L. inversion L; subst c; clear L.
      have Va0 : valid a0 by eauto using is_type_valid.
      have Va1 : valid a1 by eauto using is_type_valid.
      have Ca : compatible a0 a1 by eapply lub_compatible; eauto.
      have Ve : valid e by exact: (valid_lub Va0 Va1 La).
      have LEae : le a0 e by exact: (le_lub_left Ca La Va0 Va1).
      have LEbe : le a1 e by exact: (le_lub_right Ca La Va0 Va1).
      have Te : is_type e by eapply IHa0; eauto.
      have Vres : valid (tpi e (f0 ++ f1)).
      { cbn. apply /andP. split; auto.
        cbn in Va, Va1_tpi.
        move: Va => /andP [Va Vf0].
        move: Va1_tpi => /andP [_ Vf1].
        eapply valid_append; eauto.
      }         
      eapply is_tpi; eauto.
      * move=> u v Inv. apply in_app_or in Inv. destruct Inv as [Inv|Inv].
        -- eapply wt_le; eauto. admit. admit.
        -- eapply wt_le; eauto. admit. admit.
      * move=> u v Inv. apply in_app_or in Inv. destruct Inv as [Inv|Inv].
        -- eapply Hist_f0; eauto.
        -- eapply Hist_f1; eauto.
Admitted.

Lemma is_type_dom a f :
  is_type (tpi a f) -> is_type a.
Proof.
  move=> H. inversion H. done.
Qed.

Lemma is_type_cod a f :
  is_type (tpi a f) -> forall ui w, wt ui a -> app f ui = Some w -> is_type w.
Proof.
  induction f as [|[u v] f' IHf'].
  - move=> _ ui w _ A.
    rewrite app_nil_eq in A. inversion A; subst. constructor.
  - move=> Ttpi ui w Wtui A.
    inversion Ttpi as [| | |a2 f2 Vtpi Ta Hwt Hist]; subst.
    have Tf' : is_type (tpi a f').
    { have [Va Vu] := valid_tpi_inv Vtpi.
      have Vtf' : valid (tpi a f').
      { apply valid_tpi_intro; [exact Va|].
        eauto with valid. }
      apply is_tpi; auto;
        move=> u' v' In'; [eapply Hwt|eapply Hist]; right; eauto. }
    rewrite app_cons_eq in A.
    destruct (compatible u ui && le u ui) eqn:E.
    + destruct (app f' ui) as [t|] eqn:Afp; try discriminate.
      have Tv : is_type v by eapply Hist; left; reflexivity.
      have Tt : is_type t by eapply IHf'; eauto.
      eapply is_type_lub; [exact Tv|exact Tt|exact A].
    + eapply IHf'; eauto.
Qed.
*)
