From Stdlib Require Import Relations List Program
     ssreflect ssrfun ssrbool.
From Stdlib Require Import Classes.RelationClasses 
  Classes.Morphisms Lia Arith.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Require Import findom.
Require Import types.
Require Import syntax.syntax.
Require Import syntax.typing.

Import SyntaxNotations.
Import SubstNotations.

Open Scope syntax_scope.

Import Raw.

(* ------------------------------------------------- *)

(* analogue of RawSemantics.agda.  

   Unlike the version in Figure 1 of the paper, this semantics 
   does not use finitary projection for some reason.

*)

(* Part 1: Finite environments *)

Definition Env n := fin n -> elt.

  
(* Part 2: EvalRel *)

Notation " a ↦ b " := (singleton a b) (at level 70).

Definition _EvalRel_fun (EvalRel: forall {n}, Tm n -> Env n -> elt -> Prop) 
    {n} (M : Tm (S n)) :=
    fun ρ a g => 
      forall u v, valid u -> app g u = Some v -> 
        exists x (h:wt x a), le x u /\ EvalRel M (x .: ρ) v.

Fixpoint EvalRel {n} (t : Tm n) : Env n -> elt -> Prop := 
  match t return Env n -> elt -> Prop with 
  | Core.var i => 
      fun ρ b => valid b /\ le b (ρ i)
  | Core.tuniv => fun ρ b =>
             le b tuniv
  | Core.tnat => fun ρ b => 
             le b tnat
  | Core.zero => fun ρ b => 
             le b zero
  | Core.succ M => fun ρ b => 
      if is_bot b then True else
         valid b /\ exists a, le b (succ a) /\ EvalRel M ρ a
  | Core.tpi A B => fun ρ b =>
        match b with 
        | bot => True
        | tpi a g =>
            valid a /\ valid_fun g
            /\ EvalRel A ρ a
            /\ exists a', EvalRel A ρ a' 
            /\ _EvalRel_fun (@EvalRel) B ρ a' g 
        | _ => False
        end
  | Core.app M N => fun ρ b => 
         if is_bot b then True else 
            exists a, EvalRel M ρ (a ↦ b) /\ EvalRel N ρ a 
  | Core.abs A M => fun ρ b => 
         match b with 
         | bot => True
         
         | abs g =>
                valid_fun g /\ ~~ is_nil g
              /\ exists a (h: wt a tuniv), EvalRel A ρ a
              /\ _EvalRel_fun (@EvalRel) M ρ a g
              
         | _ => False 
         end
  | nrec T M0 M1 => fun ρ b =>
         if is_bot b then True else False                  
  end.

(* Now this version doesn't even work! *)
Arguments EvalRel : clear implicits.

Notation EvalRel_fun := (@_EvalRel_fun (@EvalRel)).

Arguments EvalRel {_}.



(** * validity *)


Definition valid_env {n} (ρ : Env n) :=
  forall x, valid (ρ x).

Lemma valid_nil : valid_env null.
  unfold valid_env. auto_case. Qed.
Lemma valid_cons n x (ρ : Env n) 
  : valid x -> valid_env ρ -> valid_env (x .: ρ).
Proof.  move=> Vx Vr. unfold valid_env. auto_case. Qed.

Hint Resolve valid_cons: valid.

  
Lemma EvalRel_valid {n} (M : Tm n) (ρ : Env n) (u : elt) : 
  EvalRel M ρ u -> valid u.
Proof.
  move: ρ u.
  induction M.
  all: move=> ρ u.
  all: cbn [EvalRel].
  - auto.
  - (* abs *)
    destruct u; try done.
    move=> [Vl [Nl [a [WT [E1 _]]]]].
    cbn. apply /andP. split; eauto.
  - destruct (is_bot u) eqn:h. 
    destruct u; try done.
    move=> [a [E1 E2]].
    apply IHM1 in E1.
    unfold singleton in E1.
    rewrite h in E1.
    cbn in E1.
    move: E1 => /andP. 
    move=> [h1 _]. move: h1 => /andP. move=> [h1 h2].
    move: h2 => /andP. move=> [h2 _]. move: h2 => /andP. auto.
  - destruct u; try done.
  - destruct (is_bot u) eqn:h.
    destruct u; try done.
    eauto.
  - (* nrec (fake case) *)
    destruct (is_bot u) eqn:h; try done.
    destruct u; try done.
  - destruct u; try done.
  - (* tpi *)
    destruct u; try done.
    move=> [Vu [Vf [WTu [E1 _]]]].
    eapply valid_tpi_intro; eauto.
  - destruct u; try done.
Qed.

(** * monotonicity *)

Definition le_env {n} (ρ1 ρ2 : Env n) := 
  forall x, le (ρ1 x) (ρ2 x).
Lemma le_env_nil : le_env null null.
  unfold le_env. auto_case. Qed.
Lemma le_env_cons n u v (ρ1 ρ2 : Env n):
  le u v -> le_env ρ1 ρ2 -> le_env (u .: ρ1) (v .: ρ2).
Proof. move=> L1 L2. unfold le_env. auto_case. Qed.


Lemma EvalRel_mono_env {n} (M : Tm n) (ρ ρ' : Env n) u :
  EvalRel M ρ u -> valid_env ρ -> valid_env ρ' -> le_env ρ ρ' -> EvalRel M ρ' u.
Proof.
  dependent induction M.
  all: cbn [EvalRel].
  all: move=> h1 V1 V2 h2. 
  - (* M = x *)
    specialize (h2 f). specialize (V1 f). specialize (V2 f).
    move: h1 => [Vu h1]. 
    split; auto. eapply (le_trans Vu V1 V2); eauto.
  - (* M = Abs M1 M2,  *)
    destruct u ; try done.
    move: h1 => [Vl [Nl [a [WT [ER f]]]]].
    repeat split; eauto.
    exists a. repeat split; eauto.
    move=> u1 v1 Vu1 h3. 
    specialize (f u1 v1 Vu1 h3).
    destruct f as [x [Lex [WT2 EM2]]].
    have Vx: valid x. eauto with valid.
    exists x. repeat split; eauto.
    eapply IHM2; eauto with valid. 
    eapply le_env_cons; eauto using le_refl.
  - (* M = app M1 M2 *)
    destruct (is_bot u); try done.
    destruct h1 as [a [E1 E2]].
    exists a. split; eauto.
  - (* M = zero *)
    destruct (is_bot u); try done.    
  - (* M = succ M *)
    destruct (is_bot u); try done.
    destruct h1 as [Vu [a [LE E]]].
    eapply IHM in E; eauto.
  - (* M = nrec *)
    destruct (is_bot u); try done.
  - (* M = tnat *)
    destruct (is_bot u); try done.
  - (* M = tpi M1 M2 *)
    destruct u; try done.
    destruct h1 as [Vu [Vl [WT1 [a' [E1 h3]]]]].
    repeat split; eauto.
    exists a'.
    repeat split; eauto.
    intros u1 v1 Vu1 APP.
    specialize (h3 u1 v1 Vu1 APP).
    destruct h3 as [x [Lx [WT E2]]].
    exists x. repeat split; eauto.
    eapply IHM2; eauto with valid.
    eapply le_env_cons; eauto using le_refl.
    eapply le_refl; eauto with valid.
  - (* M = tuniv n *)
    destruct u; try done.
Qed.    


Lemma EvalRel_bot {n} (M : Tm n) (ρ : Env n) : 
  EvalRel M ρ bot.
Proof.
  destruct M eqn:EQ; cbn; try done.
  (* var *) split; eauto. eapply le_bot; eauto.
Qed.

Lemma EvalRel_down n (M : Tm n) (ρ : Env n) u u' :
  valid_env ρ -> valid u' ->
  EvalRel M ρ u -> le u' u -> EvalRel M ρ u'.
Proof.
  move:ρ u u'.
  dependent induction M.
  all: move=> ρ u u' Vρ Vu' ER1 LE.
  all: have Vu1: valid u by eapply EvalRel_valid; eauto.
  all: cbn in ER1.
  all: cbn.

  - (* var *)
    move: ER1 => [_ LE1].
    split; eauto. eapply le_trans; eauto.

  - (* abs A M *)
    destruct u; try done.
    + (* u = bot, so u' = bot *)
      apply le_bot_inv in LE. subst u'. done.
    + (* u = abs l *)
      move: ER1 => [Vl [Nl [a [WTa [Ea h]]]]].
      destruct u' as [ | | | | | | l0 ]; try done.
      (* only u' = abs l0 case remains *)
      cbn in Vu'.
      have Vl0 : valid_fun l0 by move/andP : Vu' => [? _].
      have Nl0 : ~~ is_nil l0 by move/andP : Vu' => [_ ?].
      repeat split; eauto with valid.
      exists a. repeat split; eauto.
      unfold EvalRel_fun in h |- *.
      move=> u v0 Vu APP0.
      destruct (valid_app_exists Vl Vu) as [v [APP Vv]].
      rewrite le_abs in LE.
      move: (le_fun_mono Vl0 Vl LE Vu APP0 APP) => LEv. 
      destruct (h u v Vu APP) as [x [WTx [LEx ER2]]].
      exists x. exists WTx. split; auto.
      eapply (IHM2 _ v v0); eauto.
      eapply valid_cons; eauto.
      eapply wt_valid_tm; eauto.
      eapply (@valid_app l0 u); eauto.
  - (* app M1 M2 *)
    destruct (is_bot u') eqn:Hu'.
    + (* u' = bot, trivial *)
      destruct u'; done.
    + (* u' not bot: u not bot either since le u' u and valid u' *)
      destruct (is_bot u) eqn:Hu.
      ++ (* u = bot, so u' = bot, contradiction *)
         destruct u; try done. apply le_bot_inv in LE. subst u'.
         cbn in Hu'. done.
      ++ destruct ER1 as [a [E1 E2]].
         exists a. split; eauto.
         (* le (a ↦ u') (a ↦ u): by IHM1 we descend M1 from (a↦u) to (a↦u'). *)
         have Va: valid a by eapply EvalRel_valid; eauto.
         have Vau1: valid (a ↦ u) by eapply EvalRel_valid; eauto.
         have Vau': valid (a ↦ u').
         { unfold singleton. rewrite Hu'.
           cbn.
           apply /andP; split; last by [].
           apply /andP; split. apply /andP; split.
           - cbn. apply /andP; split; last by [].
             apply /andP; split; last by [].
             apply /implyP => _. by apply compatible_refl.
           - cbn. apply /andP; split; last by [].
             apply /negP => Lub. apply le_bot_inv in Lub. subst u'. done.
           - cbn. by rewrite Va Vu'. }
         have LEau: le (a ↦ u') (a ↦ u).
         { unfold singleton. rewrite Hu' Hu. rewrite le_abs.
           rewrite le_fun_cons. cbn.
           have Ca: compatible a a by apply compatible_refl.
           have La: le a a by apply le_refl.
           rewrite Ca La. cbn.
           rewrite lub_bot_r. cbn. by rewrite LE. }
         eapply IHM1; eauto.

  - (* zero *)
    have Vz: valid zero by done.
    eapply (le_trans (v := u)); eauto.

  - (* succ M *)
    destruct (is_bot u') eqn:Hu'.
    + destruct u'; done.
    + destruct (is_bot u) eqn:Hu.
      ++ destruct u; try done. apply le_bot_inv in LE. subst u'.
         cbn in Hu'. done.
      ++ destruct ER1 as [Vu0 [a [LEa Ea]]].
         have Va: valid a by eapply EvalRel_valid; eauto.
         have Vsa: valid (succ a) by cbn; rewrite Va.
         split; first by [].
         exists a. split; last by [].
         eapply (le_trans (v := u)); eauto.

  - (* nrec *)
    destruct (is_bot u') eqn:Hu'.
    + destruct u'; done.
    + destruct (is_bot u) eqn:Hu.
      ++ destruct u; try done. apply le_bot_inv in LE. subst u'.
         cbn in Hu'. done.
      ++ done.

  - (* tnat *)
    have Vt: valid tnat by done.
    eapply (le_trans (v := u)); eauto.

  - (* tpi A B *)

    destruct u as [ | | | | | a f |]; try done.
    + (* u = bot, u' = bot *)
      apply le_bot_inv in LE. subst u'. done.
    + (* u = tpi a f *)
      destruct u' as [ | | | | | a' f' |]; try done.
      (* only u' = tpi a' f' case *)
      move: ER1 => [Va [Vf [evA [a0 [evA0 body1]]]]].
      cbn in Vu'.
      move: Vu' => /andP. move=> [Va' Vf'].
      fold (valid_fun f') in Vf'.
      rewrite le_tpi in LE. move: LE => /andP. move=> [LEa LEf].

      split. apply Va'.
      split. apply Vf'.

      split. eapply (IHM1 _ a a'); eauto.
      exists a0.
      split. eauto.
      move=> u v Vu APP.
      destruct (valid_app_exists Vf Vu) as [w [APPw Vw]].
      move: (le_fun_mono Vf' Vf LEf Vu APP APPw) => LEv. 
      destruct (body1 u w Vu APPw) as [x [WTx [LEx ERx]]].
      exists x. 
      split. auto.
      split. auto.
      eapply IHM2; eauto.
      eapply valid_cons. eapply wt_valid_tm. eauto. eauto.
      eapply (@valid_app f' u); eauto.
  - (* tuniv *)
    have Vt: valid tuniv by done.
    eapply (le_trans (v := u)); eauto.
Qed.


Lemma EvalRel_fun_compatible {n} (M : Tm (S n)) ρ a l b l0 
  (Vρ : valid_env ρ)
  (IHM : forall (ρ : Env (S n)) (a b : elt),
      valid_env ρ -> EvalRel M ρ a -> EvalRel M ρ b -> compatible a b
 /\ forall c, lub a b = Some c -> EvalRel M ρ c
)
  (Va : valid a)
  (Vl : valid_fun l)
  (h1 : EvalRel_fun M ρ a l)
  (Vb : valid b)
  (Vl0 : valid_fun l0)
  (h2 : EvalRel_fun M ρ b l0) :
  forall c, lub a b = Some c -> 
  compatible_fun l l0 /\ EvalRel_fun M ρ c (l ++ l0).
Proof.
  move=> c LUB.
  have COMP: compatible_fun l l0.
  - unfold compatible_fun.
  apply /forallb_forall.
  move=> [u1 v1] Inl.
  apply /forallb_forall.
  move=> [u2 v2] Inl0.
  apply /implyP.
  move=> Cu.

  unfold EvalRel_fun in h1, h2.
  move: (valid_elt Vl Inl) => [Vu1 _].
  move: (valid_elt Vl0 Inl0) => [Vu2 _].
  destruct (valid_app_compatible Vl Vu1) as 
    [w [APPl [Vw Cui]]].


  have Cv1w: compatible v1 w.
  { eapply (Cui _ _ Inl). rewrite compatible_refl; eauto.
    rewrite le_refl; eauto. } clear Cui.  

  destruct (h1 _ _ Vu1 APPl) as [x1 [WTx1 [LEx1 ERx1]]].  
  destruct (valid_app_compatible Vl0 Vu2) as 
    [w0 [APPl0 [Vw0 Cui0]]].
  have Cv2w0: compatible v2 w0.
  { eapply (Cui0 _ _ Inl0). rewrite compatible_refl; eauto.
    rewrite le_refl; eauto. } clear Cui0.


  destruct (h2 _ _ Vu2 APPl0) as [x0 [WTx0 [LEx0 ERx0]]].
  have Cab: compatible a b. 
  { eapply lub_compatible; eauto. } 
  have Vx1 : valid x1. eapply wt_valid_tm; eauto.
  have Vx0 : valid x0. eapply wt_valid_tm; eauto.

  have Cx: compatible x1 x0.
  { move: (comp_down LEx1 Cu) => C1.
      move: (compatible_sym C1) => C2.
      move: (comp_down LEx0 C2) => C3.
      eapply compatible_sym. auto. } 

  have [x LUBx] : { x & lub x1 x0 = Some x}.
  { eapply compatible_lub_exists; eauto. } 
  have LEE1: le_env (x1 .: ρ) (x .: ρ).
  { unfold le_env. auto_case. eapply le_refl. eapply Vρ.
    eapply le_lub_left; eauto. 
  } 
  have LEE0: le_env (x0 .: ρ) (x .: ρ).
  { unfold le_env. auto_case. eapply le_refl. eapply Vρ.
    eapply le_lub_right; eauto. 
  } 

  have Vx : valid x. eapply (@valid_lub x1 x0); eauto.
  have Vx1ρ : valid_env (x1 .: ρ). eapply valid_cons; eauto.
  have Vx0ρ : valid_env (x0 .: ρ). eapply valid_cons; eauto.
  have Vxρ : valid_env (x .: ρ). eapply valid_cons; eauto.

  move: (EvalRel_mono_env ERx1 Vx1ρ Vxρ LEE1) => hR1.
  move: (EvalRel_mono_env ERx0 Vx0ρ Vxρ LEE0) => hR0.
  have Cww0: compatible w w0.
  { eapply IHM; eauto. } 

  move: (le_app Vl Vu1 APPl Inl (le_refl Vu1)) => LEv1.
  move: (le_app Vl0 Vu2 APPl0 Inl0 (le_refl Vu2)) => LEv2.

  move: (comp_down LEv1 Cww0) => C1.
  move: (comp_down LEv2 (compatible_sym C1)) => C2.
  eapply compatible_sym; eauto.
  (* EvalRel_fun_app *)
  - split. auto. 
    unfold EvalRel_fun.
    move=> u v Vu APP.
    destruct (compatible_app_inv Vl Vl0 Vu COMP APP) as
      [v1 [v0 [APPl [APPl0 LUBv]]]].

    destruct (h1 u v1 Vu APPl) as [x1 [WTx [LEx Ex]]].
    destruct (h2 u v0 Vu APPl0) as [x0 [WTx0 [LEx0 Ex0]]].

    have Cxx0 : compatible x1 x0. 
    { eapply le_valid_compatible_pair; eauto. } 

    have Vx1 : valid x1. eapply wt_valid_tm; eauto.
    have Vx0 : valid x0. eapply wt_valid_tm; eauto.

    have [x LUBx] : { x & lub x1 x0 = Some x}.
    { eapply compatible_lub_exists; eauto. } 

    have LEE1: le_env (x1 .: ρ) (x .: ρ).
    { unfold le_env. auto_case. eapply le_refl. eapply Vρ.
      eapply le_lub_left; eauto. 
    } 
    have LEE0: le_env (x0 .: ρ) (x .: ρ).
    { unfold le_env. auto_case. eapply le_refl. eapply Vρ.
      eapply le_lub_right; eauto. 
    } 

    have Vx : valid x. eapply (@valid_lub x1 x0); eauto.
    have Vx1ρ : valid_env (x1 .: ρ). eapply valid_cons; eauto.
    have Vx0ρ : valid_env (x0 .: ρ). eapply valid_cons; eauto.
    have Vxρ : valid_env (x .: ρ). eapply valid_cons; eauto.
    
    move: (EvalRel_mono_env Ex Vx1ρ Vxρ LEE1) => hR1.
    move: (EvalRel_mono_env Ex0 Vx0ρ Vxρ LEE0) => hR0.

    move: (IHM _ _ _ Vxρ hR1 hR0) => [CC ih].
    specialize (ih _ LUBv).

    have WTc: wt c tuniv.
    { eapply wt_lub. eapply (wt_ty_tuniv WTx). eapply (wt_ty_tuniv WTx0). auto. } 
    have WTx1c: wt x1 c.
    { eapply wt_le. eapply WTx. eapply le_lub_left; eauto.
      eapply lub_compatible. eauto. eapply wt_ty_tuniv; eauto. auto.
    } 
    have WTx0c: wt x0 c.
    { eapply wt_le. eapply WTx0. eapply le_lub_right; eauto.
      eapply lub_compatible. eauto. eapply wt_ty_tuniv; eauto. auto.
    } 
    have WTxc: wt x c.
    { eapply wt_lub. eapply WTx1c. eapply WTx0c. auto. } 
    exists x.
    exists WTxc.
    split.
    eapply le_sup_lub in LUBx; eauto.
    auto.
Qed.


Lemma lub_up : 
  forall a b c a0 b0 c0, 
    le a a0 -> le b b0 -> lub a b = Some c -> lub a0 b0 = Some c0 -> le c c0.
Proof.
Admitted.

Lemma EvalRel_compatible_lub {n} (M : Tm n) :
  forall (ρ : Env n) (a b : elt), valid_env ρ ->
  EvalRel M ρ a -> EvalRel M ρ b -> 
  compatible a b /\ 
    forall c, lub a b = Some c -> EvalRel M ρ c.
Proof.
  dependent induction M.
  all: cbn [EvalRel].
  all: move=> ρ a b Vρ.
  - (* var *) 
    split.
    + move: H => [C1 L1].
      move: H0 => [C2 L2].
      specialize (Vρ f).
      eapply (Raw.le_valid_compatible_pair Vρ); eauto. 
    + move: H => [C1 L1].
      move: H0 => [C2 L2].
      move=> c LUB.
      split. eapply (@valid_lub a b); eauto.
      eapply (@le_sup_lub a b); eauto.
  - (* abs M1 M2 *)
    destruct a; try done; destruct b; try done.
    + move=> _ _. split; try done.
      move=> c LUB. cbn in LUB. inversion LUB. done.
    + move=> _ h1. split; try done.
      move=> c LUB. cbn in LUB. inversion LUB. subst. eapply h1.
    + move=> h1 _. split; try done.
      move=> c LUB. cbn in LUB. inversion LUB. subst. eapply h1.
    + move=> [Vl [Nl [a [WT1 [E1  h1]]]]].
      move=> [Vl0 [Nl0 [b [WT2 [E2  h2]]]]].
      have Va: valid a. eapply EvalRel_valid; eauto.
      have Vb: valid b. eapply EvalRel_valid; eauto.
      move: (IHM1 _ _ _ Vρ E1 E2) => [Cab h3].
      destruct (compatible_lub_exists Cab) as [c LUB].
      have Vc: valid c. eapply (@valid_lub a b); eauto.
      have WTc: wt c tuniv. eapply (@wt_lub a _ WT1 b _ WT2); eauto.
      destruct (EvalRel_fun_compatible Vρ IHM2 Va Vl h1 Vb Vl0 h2 LUB) 
        as [Cll0 EAPP].
      split. 
      eapply Cll0.
      move=> l' LUBl. cbn in LUBl. rewrite Cll0 in LUBl. inversion LUBl.
      repeat split.
      eapply valid_append; eauto.
      destruct l; try done.
      specialize (h3 c LUB).
      exists c. exists WTc. split.
      eapply (IHM1 ρ a b); eauto.
      eauto.
  - (* app M1 M2 *)
    rename M1 into M.
    rename M2 into N.
    destruct (is_bot a) eqn:IBa; try done;
    destruct (is_bot b) eqn:IBb; try done.
    destruct a; try done.
    destruct b; try done.
    { move=> _ _ .   split; try done. 
    move=> c h. inversion h; subst. cbn. done. } 
    { move=> _. move=> [va[Ea1 Ea2]]. 
    destruct a; try done.
    split. destruct b; done.
    move=> c h. inversion h; subst. 
    rewrite IBb. eauto.
    } 
    { move=> [va[Ea1 Ea2]] _.
    destruct b; try done.
    split. destruct a; done.
    move=> c h. rewrite lub_bot_r in h.
    inversion h; subst. 
    rewrite IBa. eauto. } 
    move=> [v1 [evM1 evN1]].
    move=> [v2 [evM2 evN2]].
    have cv1: valid v1. eapply EvalRel_valid; eauto.
    have cv2: valid v2. eapply EvalRel_valid; eauto.
    
    move: (IHM1 _ _ _ Vρ evM1 evM2) => C1.
    move: (IHM2 _ _ _ Vρ evN1 evN2) => C2.
    unfold singleton in C1.
    rewrite IBa IBb in C1.
    move: C1 => [C1 LUB1].
    cbn in C1.
    move: C1 => /andP. move=> [C1 _].
    move: C1 => /andP. move=> [C1 _].
    have COMP: compatible a b.
    { 
      move: C1 => /implyP. move=> C1.
     eapply C1. eapply C2.
    } 
    split. auto.
    
    move=> c LUBab.
    destruct (is_bot c) eqn:IBc; try done.
    destruct C2 as [C2 LUB2].
    destruct (compatible_lub_exists C2) as [vc LUBres].
    specialize (LUB2 _ LUBres).
    have Va: valid a. { eapply EvalRel_valid in evM1.
                        unfold singleton in evM1. rewrite IBa in evM1.
                        apply valid_abs in evM1.
                        eauto with valid. } 
    have Vb: valid b. { eapply EvalRel_valid in evM2.
                        unfold singleton in evM2. rewrite IBb in evM2.
                        apply valid_abs in evM2.
                        eauto with valid. } 

    have Vc: valid c. eapply valid_lub in LUBab; eauto.
    have Vvc: valid vc. eapply EvalRel_valid; eauto.
    have EQ: lub (abs ((v1, a) :: nil)) (abs ((v2, b) :: nil)) 
          = Some (abs ((v1, a) :: (v2, b) :: nil)).
    { cbn. rewrite C1. cbn. done. } 
    specialize (LUB1 _ EQ). clear EQ.
    
    have LES: le (vc ↦ c) (abs ((v1, a) :: (v2, b) :: nil)).
    { 
      unfold singleton.
      rewrite IBc.
      rewrite le_abs.
      rewrite le_fun_cons.
      rewrite app_cons_eq.
      have LE1: (le v1 vc). eapply le_lub_left in LUBres; eauto.
      have Cv1: (compatible v1 vc). eapply le_valid_compatible; eauto. 
      rewrite Cv1. rewrite LE1. cbn.
      have LE2: (le v2 vc). eapply le_lub_right in LUBres; eauto.
      have Cv2: (compatible v2 vc). eapply le_valid_compatible; eauto. 
      rewrite Cv2. rewrite LE2. cbn.
      rewrite lub_bot_r.
      rewrite LUBab.
      rewrite le_refl; auto.
    } 
    have VS:  valid (vc ↦ c).
    unfold singleton. rewrite IBc. 
    cbn. 
    apply /andP; split; auto.
    apply /andP; split; auto. 
    apply /andP; split; auto. 
    apply /andP; split; auto. 
    apply /andP; split; auto. 
    rewrite compatible_refl; eauto.
    rewrite compatible_refl; eauto.
    destruct c; try done.
    rewrite Vvc. rewrite Vc. done.

    exists vc. split.
    eapply EvalRel_down; eauto. 
    auto.

  - (* zero *)
    move=> L1 L2.
    destruct a; try done; destruct b; try done.
    all: cbn.
    all: split; auto.
    all: move=>c h; inversion h; subst; done.
  - (* succ M *)
    move=> H1 H2.
    destruct (is_bot a) eqn:IBa.
    { destruct a; try done.
      split.
      - destruct b; done.
      - move=> c LUB. rewrite lub_bot_l in LUB. inversion LUB. subst c.
        destruct (is_bot b); done. }
    destruct (is_bot b) eqn:IBb.
    { destruct b; try done.
      split.
      - destruct a; done.
      - move=> c LUB. rewrite lub_bot_r in LUB. inversion LUB. subst c.
        rewrite IBa. done. }
    move: H1 => [Va [a0 [LEa Ea0]]].
    move: H2 => [Vb [b0 [LEb Eb0]]].
    specialize (IHM ρ a0 b0 Vρ Ea0 Eb0). destruct IHM as [C0 IH0].
    destruct a; try solve [cbn in LEa; done].
    rewrite le_succ in LEa.
    destruct b; try solve [cbn in LEb; done].
    rewrite le_succ in LEb.
    split.
    + cbn. eapply comp_down_pair; eauto.
    + move=> c LUB. cbn in LUB. clear IBa IBb.
      move: (compatible_lub_exists C0) => [w EQ].
      destruct (is_bot c); try done.
      destruct (lub a b) eqn:EqLUB; inversion LUB; subst. clear LUB.
      have Ve: valid e.
      { cbn in Va, Vb |- *.
         eapply (valid_lub Va Vb); eauto. } 
      split. auto.
      specialize (IH0 _ EQ). 
      move: (lub_up LEa LEb EqLUB EQ) => LEw.
      exists w.
      split; eauto.
  - (* nrec *)
    move=> H1 H2.
    destruct a; cbn in H1; try done.
    destruct b; cbn in H2; try done.
    split; first done.
    move=> c h. cbn in h. inversion h; subst c. cbn. done.
  - (* tnat *)
    move=> L1 L2.
    destruct a; try done; destruct b; try done.
    all: cbn.
    all: split; auto.
    all: move=> c h; inversion h; subst c; done.
  - (* tpi A B *)
    rename M1 into A. rename M2 into B.
    (* The tpi case requires full lub-of-tpi construction.
       Admitted; mirrors the abs case structurally. *)
    admit.
  - (* tuniv *)
    move=> L1 L2.
    destruct a; try done; destruct b; try done.
    all: cbn.
    all: split; auto.
    all: move=> c h; inversion h; subst c; done.
Admitted.

Lemma EvalRel_compatible {n} (M : Tm n) :
  forall (ρ : Env n) (a b : elt), valid_env ρ ->
  EvalRel M ρ a -> EvalRel M ρ b -> 
  compatible a b.
Proof.
  intros.
  eapply  EvalRel_compatible_lub; eauto.
Qed.

Lemma EvalRel_sup n (M : Tm n) (ρ : Env n) u u' v :
  valid_env ρ -> valid u -> valid u' -> compatible u u' -> 
  lub u u' = Some v ->
  EvalRel M ρ u -> EvalRel M ρ u' -> EvalRel M ρ v.
Proof.
  intros Vr Vu Vu' C L E1 E2.
  move: (EvalRel_compatible_lub Vr E1 E2) => [_ h].
  eapply h; eauto.
Qed.


Lemma EvalRel_compatible_ext {n} (M : Tm (S n)) ρ x1 x2 y1 y2 : 
  valid_env ρ -> compatible x1 x2 -> valid x1 -> valid x2 -> 
  EvalRel M (x1 .: ρ) y1 -> 
  EvalRel M (x2 .: ρ) y2 -> 
  compatible y1 y2.
Proof.
  move=> Vρ CC Vx1 Vx2 E1 E2.
  have [x EQ] : { x & lub x1 x2 = Some x}
    by  eapply compatible_lub_exists; eauto. 
  have Vx : valid x. eapply (valid_lub Vx1 Vx2); eauto.
  have Vext : valid_env (x .: ρ). eauto with valid.
  have E1': EvalRel M (x .: ρ) y1.
  eapply EvalRel_mono_env; eauto with valid.
  { unfold le_env. auto_case. eapply le_refl.
    eapply Vρ. eapply le_lub_left; eauto. } 
  have E2': EvalRel M (x .: ρ) y2.
  eapply EvalRel_mono_env; eauto with valid.
  { unfold le_env. auto_case. eapply le_refl.
    eapply Vρ. eapply le_lub_right; eauto. } 

  eapply (EvalRel_compatible Vext); eauto.
Qed.  

Lemma EvalRel_ideal {n} (M : Tm (S n)) ρ x1 x2 y1 y2 : 
  valid_env ρ -> compatible x1 x2 -> valid x1 -> valid x2 -> 
  EvalRel M (x1 .: ρ) y1 -> 
  EvalRel M (x2 .: ρ) y2 -> 
  exists x y, lub x1 x2 = Some x /\ lub y1 y2 = Some y 
         /\ EvalRel M (x .: ρ) y.
  move=> Vρ CC Vx1 Vx2 E1 E2.
  have [x EQ] : { x & lub x1 x2 = Some x}
    by  eapply compatible_lub_exists; eauto. 
  have Vx : valid x. eapply (valid_lub Vx1 Vx2); eauto.
  have Vext : valid_env (x .: ρ). eauto with valid.
  have E1': EvalRel M (x .: ρ) y1.
  eapply EvalRel_mono_env; eauto with valid.
  { unfold le_env. auto_case. eapply le_refl.
    eapply Vρ. eapply le_lub_left; eauto. } 
  have E2': EvalRel M (x .: ρ) y2.
  eapply EvalRel_mono_env; eauto with valid.
  { unfold le_env. auto_case. eapply le_refl.
    eapply Vρ. eapply le_lub_right; eauto. } 
  have [y EQy] : { y & lub y1 y2 = Some y }.
  { eapply compatible_lub_exists.
    eapply (EvalRel_compatible Vext); eauto. }
  exists x. exists y.
  repeat split; auto.
  eapply EvalRel_sup with (u := y1)(u':=y2); eauto.
  eapply EvalRel_valid; eauto.
  eapply EvalRel_valid; eauto.
  eapply EvalRel_compatible; eauto.
Qed.

