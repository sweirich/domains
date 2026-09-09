
From Stdlib Require Import Relations List Program
     ssreflect ssrfun ssrbool.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.


From Stdlib Require Import Classes.RelationClasses Classes.Morphisms Lia Arith.

From Equations Require Import Equations.

Require Import findom.

Import findom.Raw.

Definition is_tuniv a := 
  match a with 
  | tuniv i => true 
  | _ => false
  end.

Definition is_tnat a := 
  match a with 
  | tnat => true 
  | _ => false
  end.


Definition glb_fun (f: list (elt * elt)) (g : list (elt*elt)) := 
  forallb (fun '(uf,vf) =>             
    forallb (fun '(ug, vg) => 
          match lub uf ug with 
          | Some u => 
              match app f u , app g u with 
              | Some vf , Some vg => 
                  [ (u, glb vf vg) ]
              
                  
          | None 
      g))f
           



(** * Well-typed elements (wt) (finMem) *) 

(* This version terminates by structural recursion 
   on u.

   It is also "extensional" type checking: functions type 
   check with a particular type when, for each (u,v) in f 
   u type checks at the domain type implies v typechecks at 
   the codomain type.

   However, it doesn't also check that there is some i 
   such that wt a (tuniv i). That must be done separately 
   (when desired).

   It does not return a boolean because I'm too lazy to 
   calculate and reason about universe levels. But it is 
   decidable.

   *)

Definition ForallP {a} (p : a -> Prop) (l : list a) : Prop := 
  List.fold_right (fun x y => p x /\ y) True l.
Lemma ForallP_forall {a} p (l : list a) :
  ForallP p l <-> forall x, In x l -> p x.
Admitted.


Fixpoint wt (u : elt) (a : elt) {struct u} : Prop := 
  let wt_tpi g a i : Prop :=
    ForallP (fun '(u,v) => 
               forall a', valid a' -> le a a' -> 
                     wt u a -> wt v (tuniv i)) g
  in 
  let wt_abs f a g : Prop :=
    ForallP (fun '(u,v) => 
      forall a', 
          valid a' -> le a a' ->
          (wt u a' -> match app g u with 
                     | Some w => wt v w
                     | None => False 
                     end)) f
  in  
  match u with 
  | bot => valid a
  | tuniv i => 
      match a with 
      | tuniv j => (i < j)%nat
      | _ => False
      end
  | tnat => is_tuniv a
  | zero => is_tnat a
  | succ v => is_tnat a /\ wt v tnat
  | tpi b g => 
      (match a with 
      | tuniv i => wt b (tuniv i) /\ wt_tpi g b i 
      | _ => False
      end) /\ valid (tpi a g)
  | abs f => 
      (match a with 
      | tpi b g => 
          wt_abs f b g /\ valid (tpi b g)
      | _ => False
      end) /\ valid (abs f) 
end.

Definition wt_abs f a g : Prop :=
    ForallP (fun '(u,v) => 
      forall a', 
          valid a' -> le a a' ->
          (wt u a' -> match app g u with 
                     | Some w => wt v w
                     | None => False 
                     end)) f.
Definition wt_tpi g a i : Prop :=
     ForallP (fun '(u,v) => 
                forall a', valid a' -> le a a' -> 
                      wt u a' -> wt v (tuniv i)) g.
      
Lemma wt_valid_tm u a : wt u a -> valid u.
move: a. induction u; eauto.
all: move=>a; cbn.
all: eauto.  
move=> [h1 h2]. 
destruct a; try done.
move: h1 => [h1 h3]. apply IHu in h1. rewrite h1.
cbn in h2. cbn. done.
Qed.

Lemma wt_valid_ty u a : wt u a -> valid a.
move: a. induction u; eauto.
all: move=> a; cbn.
all: try solve[destruct a; auto].
Qed.
          
Hint Resolve wt_valid_tm wt_valid_ty : valid.

(* wt is monotonic in the type *)

Fixpoint wt_abs_le 
    (wt_le : forall u a b, wt u a -> le a b -> valid b -> wt u b)
    f {struct f} : forall a1 a2 g1 g2,
    valid_fun f ->
    valid (tpi a1 g1) -> 
    wt_abs f a1 g1 -> le (tpi a1 g1) (tpi a2 g2) 
                   -> valid (tpi a2 g2) -> wt_abs f a2 g2.
Proof.
  induction f as [|[ui vi]f].
  all: move=> a1 a2 g1 g2 Vf Vtpi1 WT LEtpi Vtpi2.
    - cbn. done.
    - cbn.
      cbn in WT. move: WT => [h1 WTf].
      split. 2: { eapply (IHf _ _ _ _  (valid_fun_tail Vf) Vtpi1 WTf); eauto. } 
      clear WTf.
      eapply valid_fun_head in Vf.
      rewrite le_tpi in LEtpi. move: LEtpi => /andP [LEa LEg].
      cbn in Vtpi1. move: Vtpi1 => /andP [Va1 Vg1].
      cbn in Vtpi2. move: Vtpi2 => /andP [Va2 Vg2].
      move=> a' Va' LEa' WTu.     
      have LE: le a1 a'. { eapply (@le_trans a1 a2 a'); eauto. } 
      specialize (h1 a' Va' LE WTu).
      have Vui: valid ui. eauto with valid.
      destruct (valid_app_exists Vg2 Vui) as [w [EQ2 Vw]].
      rewrite EQ2.
      destruct (app g1 ui) eqn:EQ1; try done.
      move: (le_fun_mono Vg1 Vg2 LEg Vui EQ1 EQ2) => LEw.
      eapply wt_le; eauto.
Defined.


Fixpoint wt_le u { struct u} : forall a b,
  wt u a -> le a b -> valid b -> wt u b.
Proof.
  move=> a b WT LE Vb.
  dependent destruction u.
  all: cbn. 
  - auto.
  - destruct a; try done.
    eapply le_tuniv_inv in LE.
    subst. done.
  - destruct a; try done.
    destruct b; try done.
    cbn in LE.
    destruct (n0 =? n1) eqn:E; try done.
    rewrite Nat.eqb_eq in E. subst. done.
  - destruct a; try done.
    apply le_tnat_inv in LE. subst. done.
  - move: WT => [ISa WTu].
    destruct a; try done.
    apply le_tnat_inv in LE. subst. auto.
  - (* tpi case *)
    move: WT => [ISa WTu].
    destruct a; try done.
    apply le_tuniv_inv in LE. subst. auto.
  - (* abs case *)
    cbn in WT.
    move: WT => [ISa Vl].
    fold (valid_fun l) in Vl.
    destruct a eqn:EQa; try done.
    fold (valid_fun l0) in ISa.
    fold (wt_abs l e l0) in ISa.
    move: ISa => [WTl0 Va].
    destruct (le_tpi_inv LE) as [w [g1 [-> [LEu LEf]]]].
    fold (wt_abs l w g1).
    fold (valid_fun l).
    fold (valid_fun g1).
    move: Vl => /andP [Vf Nf].
    repeat split; eauto.
    eapply wt_abs_le; eauto.
    apply /andP; split; eauto.
Qed.
    
Lemma le_fun_nil_inv g :
  le_fun g nil -> valid_fun g -> g = nil.
Proof.
Admitted.

(* g1 may have (u,v) and g2 may not 
   so we need to find some g0 <= g2 where
   adding (u,v) gets us back to g1.
   where (u,v) g0 == g1 *)
Lemma le_fun_cons_inv g1 u v g2 :
  le_fun g1 ((u, v) :: g2) -> 
  valid_fun g1 -> 
  exists g0, le_fun g0 g2 /\ le_fun ((u,v) :: g0) g1 /\ le_fun g1 ((u,v)::g0).
Admitted.

Fixpoint wt_le_tpi 
  (wt_le : forall v u a, 
      wt u a -> le v u -> valid v -> wt v a)
  g2 a i {struct g2} : 
  forall g1, 
      wt_tpi g2 a i -> le_fun g1 g2 
      -> valid_fun g1 -> wt_tpi g1 a i.
induction g2 as [|[u v]g2].
all: move=> g1 WT1 LE V1.
- move: (le_fun_nil_inv LE V1) => ->. done.
- cbn in WT1. move: WT1 => [WTv WTg2]. 
  fold (wt_tpi g2 a i) in WTg2.

(* wt is anti-monotonic in the argument *)

Fixpoint wt_le v u a {struct v} : 
  wt u a -> le v u -> valid v -> wt v a.
Proof.
  have wt_le_tpi  :
    wt_tpi g2 a i -> le_fun g1 g2 
                  -> valid_fun g1 -> wt_tpi g2 a i.
    valid b ->
    valid_fun f ->
    le b b1 ->
    le_fun f g ->
    ForallP 
      (fun '(u,v) => wt u b1 -> wt v (tuniv i)) g ->
    ForallP 
      (fun '(u,v) => wt u b -> wt v (tuniv i)) f.
  { 
    all: move=> Vb Vf LEb LEf ALL.
    move: Vf LEf.
    induction f as [|[ui vi]f].
    all: move=> Vf LEf.
    - cbn. done.
    - cbn.       
      cbn in LEf. move: LEf => /andP [h1 LEf].
      destruct (~~ is_nil f) eqn:Nf.
      move: (valid_fun_tail Vf Nf) => Vf'.
      specialize (IHf  Vf' LEf). 
      clear Vf' LEf.
      split.
      + clear IHf.
        apply valid_fun_head in Vf. 
        destruct (app g ui) eqn:EA; try done.
        rewrite ForallP_forall in ALL.
        move=>WTui.
        eapply wt_le; eauto using val_valid.
        admit.
      
  move v a TW LE 
  have: valid a. eauto with valid.
  move: v a WT.
  induction u.
  all: move=> v a WT Va LE Vv.
  all: cbn in *.
  - apply le_bot_inv in LE. subst. cbn. done.
  - destruct (is_tuniv a) eqn:IS; try done.
    destruct v; cbn; try done.
  - destruct a eqn:EQa; try done.
    destruct v; try done.
    cbn in *. unfold is_true in LE. rewrite Nat.eqb_eq in LE. subst.
    done.
  - destruct v; try done.
  - destruct v; try done.
    rewrite le_succ in LE.
    move: WT => [IS WTu].
    destruct a; try done.
    cbn. split; eauto.
  - destruct v; try done.
    rewrite le_tpi in LE.
    move: LE => /andP [h1 h2].
    move: WT => [WTu /andP [_ Vl]].
    destruct a; try done.
    move: WTu => [WTu WTl].
    cbn in Vv.
    move: Vv => /andP [Vv Vl0]. 
    cbn. split. split.
    + eapply IHu; eauto.
    + move: h2 WTl.

(* wt is monotonic in the type *)

Lemma wt_le : forall u a b,
  wt u a -> le a b -> valid b -> wt u b.
Proof.
  induction u.
  all: move=> a b WT LE Vb.
  all: cbn in *. 
  - auto.
  - destruct a; try done.
    eapply le_tuniv_inv in LE.
    subst. done.
  - destruct a; try done.
    destruct b; try done.
    cbn in LE.
    destruct (n0 =? n1) eqn:E; try done.
    rewrite Nat.eqb_eq in E. subst. done.
  - destruct a; try done.
    apply le_tnat_inv in LE. subst. done.
  - move: WT => [ISa WTu].
    destruct a; try done.
    apply le_tnat_inv in LE. subst. auto.
  - move: WT => [ISa WTu].
    destruct a; try done.
    apply le_tuniv_inv in LE. subst. auto.
  - move: WT => [ISa WTu].
    destruct a; try done.
    move: ISa => [WTl0 Va].
    destruct (le_tpi_inv LE) as [w [g1 [-> [LEu LEf]]]].
    move: Vb => /andP [Vw Vg1];
    fold valid in Vw, Vg1.
    fold (valid_fun g1) in Vg1.
    move: Va => /andP [Va Vl0].
    rewrite /andP. split; auto.
    rewrite /andP. split.
    all: eauto.
    eapply wt_abs; eauto.
    + move=> ui vi w1i Inf A1i.
      have Vui: valid ui.
      { 

    apply le_tpi_inv in LE. 
    move: LE => 

(** well typed elements:  (finMem) *)
Inductive wt : elt -> elt -> Prop := 
  | wt_bot a :
    valid a ->
    wt bot a 

  | wt_tuniv i j :
    (i < j)%nat -> 
    wt (tuniv i) (tuniv j)

  | wt_tnat j :
    wt tnat (tuniv j)

  | wt_zero : 
    wt zero tnat

  | wt_succ u : 
    wt u tnat -> 
    wt (succ u) tnat

  | wt_tpi a g j :
    (forall ui vi, 
        List.In (ui,vi) g -> wt ui a) -> 
    (forall ui vi, 
        List.In (ui,vi) g -> wt vi (tuniv j)) ->

    wt a (tuniv j) -> 
    (valid (tpi a g)) ->
    wt (tpi a g) (tuniv j)

  | wt_abs a f g :  
    (* TODO: we don't need the g[ui]=w premise in this first 
       one. *)
    (forall ui vi w, 
        List.In (ui,vi) f -> app g ui = Some w -> wt ui a) ->
    (forall ui vi w, 
        List.In (ui,vi) f -> app g ui = Some w -> wt vi w) ->
    (* make sure both tm and type are valid *)
    (valid (abs f)) ->
    (valid (tpi a g)) -> 
    wt (abs f) (tpi a g)
  .

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
Lemma wt_abs_ext a f g :
    (forall u, exists v, wt v a /\ app f u = app f v) ->
    (forall u w v, app g u = Some w -> app f u = Some v -> wt v w) ->
    (* make sure both tm and type are valid *)
    (valid (abs f)) ->
    (valid (tpi a g)) <-> 
    wt (abs f) (tpi a g)
  .
Abort.

Lemma wt_valid_tm u a : wt u a -> valid u.
induction 1; eauto.  
Qed.

Lemma wt_valid_ty u a : wt u a -> valid a.
induction 1; eauto.
Qed.

Hint Resolve wt_valid_tm wt_valid_ty : valid.

(*
Lemma 2 
- If u : a and a <= b, then u : b.

- If u : a, v : a, and u and v are compatible, then u ∨ v : a
*)


Lemma wt_le u a : 
  wt u a -> forall b, le a b -> valid b -> wt u b.
Proof.
  move=> h.
  induction h; move=> b LE Vb.
  - eapply wt_bot; eauto. 
  - apply le_tuniv_inv in LE. subst. 
    eapply wt_tuniv; eauto.
  - apply le_tuniv_inv in LE. subst.
    eapply wt_tnat; eauto.
  - apply le_tnat_inv in LE. subst.
    eapply wt_zero; eauto.
  - eapply le_tnat_inv in LE. subst.
    eapply wt_succ; eauto.
  - apply le_tuniv_inv in LE. subst.    
    eapply wt_tpi; eauto.
  - destruct (le_tpi_inv LE) as [w [g1 [-> [LEu LEf]]]].
    move: Vb => /andP [Vw Vg1];
    fold valid in Vw, Vg1.
    fold (valid_fun g1) in Vg1.
    eapply wt_abs; eauto.
    + move=> ui vi w1i Inf A1i.
      have Vui: valid ui.
      { 
        cbn in H3.
        move: H3 => /andP [_ /forallb_forall h3].
        specialize (h3 _ Inf). move: h3 => /andP [Vui Vvi].
        done.        
      } 

      move: H4 => /andP [_ /orP [h4|h4]];
      fold valid valid_fun in h4.
      -- move: (valid_app_exists h4 Vui) => [wi [Ai Vwi]].
         move: Vg1 => /orP [Vg1|Ng1].
         move: (le_fun_mono h4 Vg1 LEf Vui Ai A1i) => LFM.
         eapply H0; eauto.
         (* g1 is nil *)
         destruct g1; try done.
         rewrite app_nil_eq in A1i. inversion A1i; subst.
         exfalso. eapply valid_fun_not_le_fun_nil; eauto.
      -- (* g is nil *)
         destruct g; try done.
         specialize (H0 ui vi bot Inf (app_nil_eq _)).
         eapply H0; eauto.

    + move=> ui vi w1i Inf A1i.
      have Vui: valid ui. 
      { move: H3 => /andP [_ /forallb_forall h3]; fold valid in h3.
        specialize (h3 _ Inf). move: h3 => /andP [Vui Vvi].
        done.
      }
      move: H4 => /andP [Va /orP [Vg|Vg]]; fold valid in Va, Vg.
      move: (valid_app_exists Vg Vui) => [wi [Ai Vwi]].
      move: Vg1 => /orP [Vg1|Vg1].
      move: (le_fun_mono Vg Vg1 LEf Vui Ai A1i) => LFM.
      eapply H2; eauto.
      eapply (valid_app Vg1 Vui); eauto.
      (* g1 is nil, g is not nil *)
      destruct g1; try done.
      exfalso. eapply valid_fun_not_le_fun_nil; eauto.
      (* g is nil, try cases for g1 *)
      destruct g; try done.
      move: Vg1 => /orP [Vg1|Vg1].
      (* g1 is non nil, and g is nil *)
      specialize (H2 _ _ bot Inf (app_nil_eq _)).
      eapply H2; eauto. eapply le_bot.
      eapply (valid_app (u:= ui)); eauto.
      (* both nil *)
      destruct g1; try done.
      rewrite app_nil_eq in A1i. inversion A1i.
      eapply H1; eauto.
    + apply /andP. fold valid (valid_fun g1).
      split; auto.
Qed. 

Lemma wt_lub u a : 
  wt u a -> (forall v w, wt v a -> lub u v = Some w -> 
                   wt w a).
Proof.
  move=> h. induction h.
  all: move=> v w Wtv LUB.
  all: inversion LUB; subst; try done.
  all: destruct v; try done.
  all: try solve [cbn in LUB; inversion LUB; 
                  subst; econstructor; eauto].
  - destruct (i =? n) eqn:EQ; try done.
    inversion H1. 
    eapply wt_tuniv. done.
  - destruct (lub u v) eqn:EQ; try done.
    cbn in H0. inversion H0. subst.
    inversion Wtv; subst.
    eapply wt_succ; eauto.
  - (* u = tpi a g, v=tpi v l *)
    destruct (compatible_fun g l) eqn:C1; try done.
    destruct (lub a v) eqn:L1; try done.
    inversion H5. clear H5.
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
         eapply wt_le; eauto.
         eapply le_lub_left; eauto.
         eapply lub_compatible; eauto.
      ++ (* tuple is in v *)
        specialize (H9 _ _ Inl). 
        eapply wt_le; eauto.
        eapply le_lub_right; eauto.
        eapply lub_compatible; eauto.
    + move=> ui vi InApp.
      destruct (in_app_or _ _ _ InApp) as [Ing|Inl]; eauto.
    + apply /andP. fold valid (valid_fun (g ++ l)).
      split. eauto.
      move: H3 => /andP [_ /orP [Vg|Vg]].
      fold valid (valid_fun g) in Vg.
      all: move: H11 => /andP [_ /orP [Vl|Vl]];
           fold valid (valid_fun l) in Vl.
      all: apply /orP.
      ++ left. eapply valid_append; eauto.
      ++ destruct l; try done.
         rewrite app_nil_r. left; auto.
      ++ destruct g; try done.
         cbn. left; auto.
      ++ destruct l; destruct g; try done.
         cbn. right; done.
  - (* u = abs f, v = abs l *)
    cbn in LUB.
    destruct (compatible_fun f l) eqn:C1; try done.
    inversion LUB; subst w; clear LUB.
    inversion Wtv as [| | | | | |a2 l2 g2 Hui2 Hvi2 Vabs2 Vtpi2]; subst;
      clear Wtv.
    have Vf : valid_fun f by cbn in H1.
    have Vl : valid_fun l by cbn in Vabs2.
    have Vfl : valid_fun (f ++ l) by eapply valid_append; eauto.
    eapply wt_abs; eauto.
    + move=> ui vi wi Inapp A.
      destruct (in_app_or _ _ _ Inapp) as [Inf|Inl]; eauto.
    + move=> ui vi wi Inapp A.
      destruct (in_app_or _ _ _ Inapp) as [Inf|Inl]; eauto.
Qed.

(* Corollary 2 If w : Πaf and u : a, then w(u) : f (u). *)

Lemma wt_abs_pred u v w b f :
  wt (abs ((u,v)::w)) (tpi b f) -> ~~is_nil w ->
  wt (abs w) (tpi b f).
Proof.
  move=> WT Nw. inversion WT. subst.
  move: H5 => /andP [Vb Vf]. fold valid in Vb , Vf.
  fold (valid_fun f) in Vf.
  move: (valid_fun_tail H4 Nw) => Vt.
  move: (valid_fun_head H4) => Vh.
    eapply wt_abs; eauto.
    + move=> uj vj wj Inj.
      eapply (H2 uj vj wj ltac:(right;eauto)).
    + move=> uj vj wj Inj.
      eapply (H3 uj vj wj ltac:(right;eauto)).
    + eapply wt_valid_ty; eauto.
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
    eapply wt_bot; eauto.
  - move=> WT u r t WTu A1 A2.
    have Vu : valid u by eauto with valid.
    have Vtpi : valid (tpi a f) by eauto with valid.
    have Vabs : valid (abs ((ui,vi) :: w')) by eauto with valid.
    have Vw : valid_fun ((ui,vi) :: w') by done.
    have Vt : valid t. { eapply (app_tpi_valid Vtpi Vu A2). }
    have Vui : valid ui by eapply key_valid; eauto using valid_fun_head.
    have Vvi : valid vi by eapply val_valid; eauto using valid_fun_head.
    (* Extract per-entry typing info from WT *)
    inversion WT as [| | | | | |aX wX fX HuiAll HviAll VabsX VtpiX EwX EafX]; subst.
    (* HviAll: forall ui' vi' w0, In (ui',vi') ((ui,vi)::w') -> app f ui' = Some w0 -> wt vi' w0 *)
    (* Get app w' u = Some r' *)
    have [r' [Ar' Vr']] : exists r', app w' u = Some r' /\ valid r'.
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
      eapply wt_bot; eauto. }
    destruct (compatible ui u && le ui u) eqn:EQui.
    + (* ui compatible with u and ui <= u: r = lub vi r' *)
      move: EQui => /andP [Cui LEui].
      (* Get wi = app f ui and show wt vi wi *)
      have [wi [Awi Vwi]] : exists wi, app f ui = Some wi /\ valid wi
        by eapply app_tpi_exists; eauto.
      have WTvi_wi : wt vi wi by eapply HviAll; [left; reflexivity | eauto].
      (* wi <= t by monotonicity of app f (or trivially if f is nil) *)
      have LEwit : le wi t.
      { cbn in Vtpi. move: Vtpi => /andP [_ /orP [Vf|Nf]].
        { fold (valid_fun f) in Vf.
          have [_ LE] : compatible wi t /\ le wi t.
          { eapply le_fun_mono_arg with (h := f) (u1 := ui) (u2 := u); eauto. }
          exact LE. }
        destruct f; try done. cbn in Awi, A2.
        inversion Awi. inversion A2. subst. eapply le_bot. }
      have WTvi_t : wt vi t by eapply wt_le; eauto.
      eapply wt_lub with (u := vi) (v := r'); eauto.
    + (* no contribution from (ui,vi): r = r' *)
      inversion A1. subst r. done.
Qed.


(*
Lemma 3 If Πaf : Uk and f = (u1 → t1,...,un → tn), then ui : a and f (ui) : Uk. 

This version is not the same as it doesn't say anything 
intensional about f.

*)

Lemma lemma3_1 a f k : 
  wt (tpi a f) (tuniv k) -> 
  forall ui vi, In (ui,vi) f -> wt ui a.
Proof.
  intros.
  inversion H. eauto.
Qed.


Lemma wt_instantiate a f k : 
  wt (tpi a f) (tuniv k) -> 
  forall ui w, wt ui a -> app f ui = Some w -> wt w (tuniv k).
Proof.
  induction f as [|[u v]f].
  all: move=> WT; inversion WT; subst; clear WT.
  all: move=> ui vi w. 
  - rewrite app_nil_eq. move=> EQ. inversion EQ. subst.
    eapply wt_bot; eauto.
  - rewrite app_spec. cbn. rewrite <- app_spec.
    destruct (compatible u ui && le u ui) eqn:EQ.
    + move=> LUB. destruct (app f ui) eqn:APP; try done.
      cbn [valid] in H5. fold (valid_fun ((u,v)::f)) in H5.
      move: H5 => /andP [Va /orP [Vuf|h]]; try done.
      have WTv : wt v (tuniv k). 
      { eapply H3; eauto. left. reflexivity. } 
      have WT: wt (tpi a f) (tuniv k).
      { destruct (~~ is_nil f) eqn:Nf.
        - eapply wt_tpi; eauto.
        move=> uj vj Infj. eapply H2; eauto. right; eauto.
        move=> uj vj Infj. eapply H3; eauto. right; eauto.
        apply /andP. fold valid. fold (valid_fun f).
        split; auto. apply /orP. left. eauto with valid.
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
      move: Vf => /orP [h1|h1]; try done.
      fold (valid_fun f).
      destruct (is_nil f) eqn:Nf. 
      apply /orP. right. auto. 
      apply /orP. left. apply valid_fun_tail in h1; auto. 
      rewrite Nf. done.
Qed.

Lemma lemma3_2 a f k : 
  wt (tpi a f) (tuniv k) -> 
  forall ui vi w, In (ui,vi) f -> app f ui = Some w -> wt w (tuniv k).
Proof.
  intros.
  inversion H. subst.
  eapply wt_instantiate; eauto.
Qed.


(*
Lemma 4:

If w : Πaf and w = (u1 → t1,...,un → tn), then ui : a
and w(ui) : f (ui).
*)

Lemma lemma4_1 w a f :
  wt (abs w) (tpi a f) ->
  forall ui vi, In (ui, vi) w -> wt ui a.
Proof.
  move=> WT ui vi In.
  inversion WT as [| | | | | |aX wX fX HuiAll HviAll Vabs Vtpi]; subst.
  have Vw : valid_fun w by exact Vabs.
  have Vui : valid ui.
  { move: (valid_fun_subterms_prop Vw In) => [Vu _]. done. }
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



                                       
(*
 if u : a then lv(u) <= lv(a) and if u : Uk then lv(u) < k 
*)

Lemma wt_level u a :
  wt u a -> level u <= level a.
Proof.
  move=> h. 
  induction h.
  7: { 
    move: H H0 H1 H2.
    induction f as [|[ui vi]f].
    + cbn in *. move=> _ _ _ _. lia.
    + move=> Wta La Wtb Lb.
    cbn. fold level_fun. 
    have IH: level (abs f) <= level (tpi a g).
    { destruct (~~ is_nil f) eqn:Nf.
      + eapply valid_fun_tail in H3; eauto.
        { eapply IHf; eauto.
          - intros. eapply Wta. right. eauto. eauto.
          - intros. eapply La. right. eauto. eauto.
          - intros. eapply Wtb. right. eauto. eauto.
          - intros. eapply Lb. right. eauto. eauto.
        }     
      + destruct f; try done. cbn. lia.
    }        
    cbn in IH. fold level_fun in IH.
    move: H4 => /andP[ Va /orP [Vg|Ng]].
    fold valid in *. 
    - move: (valid_fun_head H3) => Vh.
      move: (key_valid Vh) => Vui.
      move: (val_valid Vh) => Vvi.
      move: (valid_app_exists Vg Vui) => [w [EQ Vw]].
      specialize (@Wta ui vi w ltac:(left;auto) EQ).
      specialize (@La ui vi w ltac:(left;auto) EQ).
      specialize (@Wtb ui vi w ltac:(left;auto) EQ).
      specialize (@Lb ui vi w ltac:(left;auto) EQ).
      eapply level_app in EQ.
      lia.
    -       
Admitted.


(*
Lemma 5 If w : Π b f and b <= a, then for any u : a there exists v : b such that v <= u and w(u) = w(v).

Proof We write w = (u1 → l1,...,un → ln) with ui : b and 
   li : f (ui). We then
have w(u) = w(v) 
   with v = ∨{ui | ui <= u} and v : b by Lemma 2.

*)


(* Stronger form: for any x with le v x and le x u, app w u = app w x. *)
Lemma app_down_strong w b f :
  wt (abs w) (tpi b f) -> forall u a,
      le b a ->
      wt u a ->
      exists v, wt v b /\ le v u /\
        (forall x, valid x -> le v x -> le x u -> app w u = app w x).
Proof.
  induction w as [|[ui vi] w'].
  - move=> WT. inversion WT. done.
  - move=> WT u a LE WTu.
    have Vu : valid u by eauto with valid.
    have Vtpi : valid (tpi b f) by eauto with valid.
    have Vabs : valid (abs ((ui,vi) :: w')) by eauto with valid.
    have Vb : valid b.
    { cbn in Vtpi. move: Vtpi => /andP [? _]. done. }
    have Vw : valid_fun ((ui,vi) :: w') by done.
    have Vui : valid ui by eapply key_valid; eauto using valid_fun_head.
    have Vvi : valid vi by eapply val_valid; eauto using valid_fun_head.
    have [wi [Awi Vwi]] : exists wi, app f ui = Some wi /\ valid wi
      by eapply app_tpi_exists; eauto.
    inversion WT as [| | | | | |aX wX fX Hui2 Hvi2 VabsX VtpiX]; subst.
    have WTui_b : wt ui b by eapply Hui2; [left; reflexivity | exact Awi].
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
        -- eapply wt_bot; eauto.
        -- eapply le_bot.
        -- move=> x Vx LE_botx LE_xu.
           have LE_uix : le ui x = false.
           { destruct (le ui x) eqn:E; try reflexivity.
             have Luiu : le ui u by eapply le_trans with (v := x); eauto.
             rewrite LEui in Luiu. done. }
           rewrite app_spec. cbn.
           rewrite LEui LE_uix !Bool.andb_false_r /=.
           reflexivity.
Qed.

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
  - rewrite Nat.eqb_eq in H1. subst. inversion WTi; subst; try done.
Abort.

(* ------------------------------------------------------------- *)

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
        move: Va => /andP [_ VD0].
        move: Va1_tpi => /andP [_ VD1].
        move: VD0 => /orP [Vf0|Nf0].
        - move: VD1 => /orP [Vf1|Nf1].
          + apply /orP. left. eapply valid_append; eauto.
          + destruct f1; try done. rewrite app_nil_r.
            apply /orP. left. exact Vf0.
        - move: VD1 => /orP [Vf1|Nf1].
          + destruct f0; try done. cbn. apply /orP. left. exact Vf1.
          + destruct f0; destruct f1; done. }
      eapply is_tpi; eauto.
      * move=> u v Inv. apply in_app_or in Inv. destruct Inv as [Inv|Inv].
        -- eapply wt_le; eauto.
        -- eapply wt_le; eauto.
      * move=> u v Inv. apply in_app_or in Inv. destruct Inv as [Inv|Inv].
        -- eapply Hist_f0; eauto.
        -- eapply Hist_f1; eauto.
Qed.

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
        destruct f' as [|[u2 v2] f''];
          [right; done|left; destruct Vu as [Vf|Nf]; [|done]; eapply valid_fun_tail; eauto]. }
      apply is_tpi; auto;
        move=> u' v' In'; [eapply Hwt|eapply Hist]; right; eauto. }
    rewrite app_spec in A. cbn in A. rewrite <- app_spec in A.
    destruct (compatible u ui && le u ui) eqn:E.
    + destruct (app f' ui) as [t|] eqn:Afp; try discriminate.
      have Tv : is_type v by eapply Hist; left; reflexivity.
      have Tt : is_type t by eapply IHf'; eauto.
      eapply is_type_lub; [exact Tv|exact Tt|exact A].
    + eapply IHf'; eauto.
Qed.
