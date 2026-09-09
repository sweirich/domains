(* --------------------------------------------------------- *)
(** * Minimization *)
(* --------------------------------------------------------- *)


(* A tuple (u, v) is redundant in the context of a function `rest` when
   applying `rest` to u already produces a result at least as large as v. *)
Definition redundant (u v : elt) (rest : list (elt * elt)) : bool :=
  match app rest u with
  | Some w => le v w
  | None => false
  end.

(* Right-to-left minimization: process each pair and keep it only if it
   is not redundant with respect to the minimized tail. *)
Fixpoint minimize (f : list (elt * elt)) : list (elt * elt) :=
  match f with
  | nil => nil
  | (u, v) :: f' =>
      let m := minimize f' in
      if redundant u v m then m else (u, v) :: m
  end.

(* A function is minimal if no minimization is possible. *)
Definition minimal (f : list (elt * elt)) : bool :=
  Nat.eqb (length f) (length (minimize f)).

Lemma app_nil_eq u : app nil u = Some bot.
Proof. reflexivity. Qed.

Lemma minimize_incl f : forall x, In x (minimize f) -> In x f.
Proof.
  induction f as [|[u v] f' IHf'].
  - cbn. auto.
  - cbn. intro x.
    destruct (redundant u v (minimize f')) eqn:E.
    + move=> In. right. eauto.
    + move=> [->|In]. left; auto. right; eauto.
Qed.

Lemma coherent_with_sublist f g p :
  (forall x, In x g -> In x f) ->
  coherent_with f p ->
  coherent_with g p.
Proof.
  destruct p as [u v]. move=> Sub CH.
  unfold coherent_with in *.
  apply /forallb_forall.
  move: CH => /forallb_forall CH.
  move=> [uj vj] Ing. apply (CH _ (Sub _ Ing)).
Qed.

Lemma compatible_fun_sublist f g :
  (forall x, In x g -> In x f) ->
  compatible_fun f f ->
  compatible_fun g g.
Proof.
  move=> Sub CF.
  unfold compatible_fun in *.
  apply /forallb_forall.
  move=> [ui vi] Ini.
  apply /forallb_forall.
  move=> [uj vj] Inj.
  move: CF => /forallb_forall CF.
  move: (CF _ (Sub _ Ini)) => /forallb_forall CFi.
  apply (CFi _ (Sub _ Inj)).
Qed.

Lemma no_bot_result_sublist f g :
  (forall x, In x g -> In x f) ->
  no_bot_result f ->
  no_bot_result g.
Proof.
  move=> Sub NB.
  unfold no_bot_result in *.
  apply /forallb_forall.
  move: NB => /forallb_forall NB.
  move=> x In. eapply NB. apply Sub. auto.
Qed.

Lemma valid_subterms_sublist f g :
  (forall x, In x g -> In x f) ->
  forallb (fun '(ui,vi) => valid ui && valid vi) f ->
  forallb (fun '(ui,vi) => valid ui && valid vi) g.
Proof.
  move=> Sub V.
  apply /forallb_forall.
  move: V => /forallb_forall V.
  move=> x In. eapply V. apply Sub. auto.
Qed.

Lemma minimize_not_nil f :
  valid_fun f -> ~~ is_nil (minimize f).
Proof.
  induction f as [|[u v] f' IHf'].
  - done.
  - move=> Vf.
    have Vhead : CFT u v f'. { eapply valid_fun_head; eauto. }
    have NBv : ~~ le v bot. { eapply (val_nbot Vhead). }
    cbn [minimize].
    destruct (redundant u v (minimize f')) eqn:Hred.
    + destruct f' as [|[u' v'] f''].
      * cbn [minimize] in Hred. unfold redundant in Hred.
        rewrite app_nil_eq in Hred.
        rewrite Hred in NBv. done.
      * have Vf' : valid_fun ((u', v') :: f''). { eapply valid_fun_tail; eauto. }
        apply IHf'. auto.
    + done.
Qed.

Lemma valid_minimize f :
  valid_fun f -> valid_fun (minimize f).
Proof.
  move=> Vf.
  have NN: ~~ is_nil (minimize f). { eapply minimize_not_nil; eauto. }
  have Sub: forall x, In x (minimize f) -> In x f. { eapply minimize_incl. }
  unfold valid_fun.
  apply /andP; split. apply /andP; split. apply /andP; split.
  - eapply compatible_fun_sublist; eauto. eapply valid_fun_compatible; eauto.
  - eapply no_bot_result_sublist; eauto. eapply valid_fun_no_bot; eauto.
  - done.
  - eapply valid_subterms_sublist; eauto. eapply valid_fun_subterms; eauto.
Qed.

(* Easy direction: the minimized form is below the original. *)
Lemma le_fun_minimize_orig f :
  valid_fun f -> le_fun (minimize f) f.
Proof.
  move=> Vf.
  have Lrefl: le_fun f f. { eapply le_fun_refl; eauto. }
  apply /forallb_forall.
  move=> [ui vi] In.
  have Inf: List.In (ui, vi) f. { eapply minimize_incl; eauto. }
  move: Lrefl => /forallb_forall Lrefl.
  specialize (Lrefl _ Inf). cbn in Lrefl. auto.
Qed.

(* Hard direction: the original is below the minimized form. *)
Lemma le_fun_orig_minimize f :
  valid_fun f -> le_fun f (minimize f).
Proof.
  induction f as [|[u v] f' IHf'].
  - done.
  - move=> Vf.
    have Vhead : CFT u v f'. { eapply valid_fun_head; eauto. }
    have Vu : valid u. { eapply (key_valid Vhead). }
    have Vv : valid v. { eapply (val_valid Vhead). }
    have NBv : ~~ le v bot. { eapply (val_nbot Vhead). }
    have Cohvf' : coherent_with f' (u,v). { eapply (compat Vhead). }
    have Vsub : forallb (fun '(ui,vi) => valid ui && valid vi) f'.
    { move: (valid_fun_subterms Vf) => /=.
      move=> /andP [_ ?]. done. }
    destruct f' as [|[u' v'] f''].
    + cbn [minimize]. unfold redundant.
      rewrite app_nil_eq.
      have Hfalse : le v bot = false. { by apply negbTE. }
      rewrite Hfalse.
      eapply le_fun_refl; eauto.
    + have Vf' : valid_fun ((u', v') :: f''). { eapply valid_fun_tail; eauto. }
      have Vmin' : valid_fun (minimize ((u', v') :: f'')). { eapply valid_minimize; eauto. }
      have Cohmin' : coherent_with (minimize ((u', v') :: f'')) (u,v).
      { eapply coherent_with_sublist; [eapply minimize_incl|]. eauto. }
      specialize (IHf' Vf').
      set m := minimize ((u', v') :: f'').
      have Emin : minimize ((u,v) :: (u',v') :: f'') =
        if redundant u v m then m else (u,v) :: m.
      { reflexivity. }
      rewrite Emin.
      destruct (redundant u v m) eqn:Hred.
      * (* Redundant case: head (u,v) is dropped, so we need
           le_fun ((u,v) :: (u',v') :: f'') m. *)
        apply /forallb_forall.
        move=> [ui vi] Inui. cbn.
        destruct Inui as [Eq|Inui].
        -- inversion Eq. subst ui vi.
           unfold redundant in Hred. exact Hred.
        -- move: IHf' => /forallb_forall IHf'.
           specialize (IHf' _ Inui). cbn in IHf'. exact IHf'.
      * (* Not redundant case: head (u,v) is kept. *)
        have CU : compatible u u. { eapply compatible_refl; auto. }
        have LU : le u u. { eapply le_refl; auto. }
        destruct (valid_app_exists Vmin' Vu) as [e [E Ve]].
        have Cve : compatible v e.
        { eapply (Comp_value_app (f := m)
                                 (xi := u) (w := e)); eauto. }
        destruct (compatible_lub_exists Cve) as [t Et].
        have Vt : valid t. { eapply valid_lub in Et; eauto. }
        have Lvt : le v t. { eapply le_lub_left; eauto. }
        have Eapp : app ((u, v) :: m) u = Some t.
        { rewrite app_spec. cbn. rewrite CU LU /=.
          rewrite <- app_spec. subst m. rewrite E. exact Et. }
        rewrite le_fun_cons.
        rewrite Eapp.
        rewrite Lvt.
        rewrite Bool.andb_true_l.
        subst m.
        eapply le_fun_weaken_cons; eauto.
Qed.

(* Equivalence of the original and its minimized form. *)
Lemma eqb_fun_minimize f :
  valid_fun f -> eqb_fun f (minimize f).
Proof.
  move=> Vf.
  unfold eqb_fun.
  apply /andP; split.
  - eapply le_fun_orig_minimize; auto.
  - eapply le_fun_minimize_orig; auto.
Qed.

(* -------------------------------------------------- *)

Lemma app_respects u1 u2 (Vu1 : valid_fun u1) (Vu2 : valid_fun u2)
  v1 v2 (Vv1 : valid v1) (Vv2 : valid v2) :  
  le_fun u1 u2 -> le v1 v2 -> 
  exists w1, exists w2, (app u1 v1) = Some w1 /\ (app u2 v2) = Some w2 /\ 
                compatible w1 w2 /\ le w1 w2.
Proof.
  move=> Lu Lv.
  move: (valid_app_compatible Vu1 Vv1) => [w1 [EQ1 [Vw1 CW1]]].
  move: (valid_app_compatible Vu2 Vv2) => [w2 [EQ2 [Vw2 CW2]]].


Abort.

Module Unused.
Import Raw.


(*

(* syntactic equality on elements. does not include *any* extensionality for functions *)

Fixpoint eqb (u v : elt) : bool := 
  let fix fun_eqb f g := 
    match f , g with 
    | nil , nil => true
    | (u1 , v1) :: f , (u2 , v2) :: g => eqb u1 u2 && eqb v1 v2 && fun_eqb f g
    | _ , _ => false
    end in
  match u , v with 
  | bot , bot => true
  | tnat , tnat => true
  | tuniv k , tuniv l => k =? l
  | zero , zero => true 
  | succ u , succ v => eqb u v 
  | tpi a f , tpi b g => eqb a b && fun_eqb f g
  | abs f , abs g => fun_eqb f g
  | _ , _ => false
  end.

Fixpoint fun_eqb f g := 
 match f , g with 
    | nil , nil => true
    | (u1 , v1) :: f , (u2 , v2) :: g => eqb u1 u2 && eqb v1 v2 && fun_eqb f g
    | _ , _ => false
    end.

Fixpoint eqb_eq u {struct u} : forall v, eqb u v <-> u = v.
have fun_eqb_eq: forall f g, fun_eqb f g <-> f = g.
{ induction f.
  clear eqb_eq.
  move=> g. destruct g. cbn. done. cbn. done.
  move=> g. destruct g. destruct a as [u1 v1]. clear eqb_eq. cbn. done.
  destruct a as [u1 v1]. destruct p as [u2 v2]. cbn.
  move: (eqb_eq u1 u2) => [h1 h1'].
  move: (eqb_eq v1 v2) => [h2 h2'].
  move: (eqb_eq u1 u1) => [h4 h4'].
  move: (eqb_eq v1 v1) => [h5 h5'].
  clear eqb_eq.
  move: (IHf g) => [h3 h3'].
  split. move=> /andP [/andP [E2 E3] E1].
  repeat f_equal; eauto. 
  move=> h. inversion h. subst.
  rewrite h1'. auto. rewrite h2'. auto. rewrite h3'. auto. 
  reflexivity.
} 
move=> v. destruct u; destruct v.
all: cbn; try done. 
- split. 
  move=> h. apply (Nat.eqb_eq n n0) in h. f_equal. done.
  move=> h. inversion h. apply Nat.eqb_refl.
- split. rewrite eqb_eq. move=> ->. done.
  move: (eqb_eq u v) => h1.
  move: (eqb_eq u u) => h2.
  move=> h3. inversion h3. subst. rewrite h2. done.
- fold fun_eqb. split.
  move=> /andP [h1 h2]. rewrite eqb_eq in h1. rewrite fun_eqb_eq in h2. subst. done.
  move: (eqb_eq u v) => h1.
  move: (eqb_eq u u) => h2.
  move: (fun_eqb_eq l l0) => h3.
  move: (fun_eqb_eq l l) => h4.
  move=> h5. inversion h5. subst.
  apply /andP. rewrite h2. rewrite h4. auto.
- fold fun_eqb. split.
  move=> h. rewrite fun_eqb_eq in h. subst. done.
  move: (fun_eqb_eq l l0) => h3.
  move: (fun_eqb_eq l l) => h4.
  move=> h5. inversion h5. subst.
  rewrite h4. auto.
Admitted.

Lemma eqb_refl  : forall u, eqb u u. Admitted.
Lemma eqb_sym   : forall u v, eqb u v -> eqb v u. Admitted.
Lemma eqb_trans : forall u v w, eqb u v -> eqb v w -> eqb u w. Admitted.

*)
(* structural recursion principle for elt *)
Definition elt_rect' :=
fun (P : elt -> Type) 
  (Pf : list (elt * elt) -> Type) 
  (f : P bot) (f0 : P tnat) (f1 : forall n : nat, P (tuniv n)) 
  (f2 : P zero) (f3 : forall e : elt, P e -> P (succ e))
  (f4 : forall e : elt, P e -> forall l : list (elt * elt), Pf l -> P (tpi e l))
  (f5 : forall l : list (elt * elt), Pf l -> P (abs l))
  (fnil : Pf nil) 
  (fcons : forall u v l, P u -> P v -> Pf l -> Pf ((u,v)::l)) =>
fix F (e : elt) : P e :=
  let fix Ff (l : list (elt * elt)) : Pf l := 
    match l as f0 return Pf f0 with 
    | nil => fnil 
    | ((u,v)::t) => fcons _ _ _ (F u) (F v) (Ff t)
    end in
  match e as e0 return (P e0) with
  | bot => f
  | tnat => f0
  | tuniv n => f1 n
  | zero => f2
  | succ e0 => f3 e0 (F e0)
  | tpi e0 l => f4 e0 (F e0) l (Ff l)
  | abs l => f5 l (Ff l)
  end.

(*
Derive NoConfusion NoConfusionHom Subterm for elt.
*)

(* -------------------------------------------- *)

Inductive bound : elt -> nat -> Prop := 
  | b_bot n : bound bot n
  | b_tnat n : bound tnat (S n)
  | b_tuniv k n : bound (tuniv k) (S n)
  | b_zero n : bound zero (S n)
  | b_succ u n : bound u n -> bound (succ u) (S n)
  | b_tpi u f n : 
    bound u n -> bound_fun f n 
              -> bound (tpi u f) (S n)
  | b_abs f n : bound_fun f n
              -> bound (abs f) (S n) 
with bound_fun : list (elt * elt) -> nat -> Prop := 
  | b_nil n : bound_fun nil n
  | b_cons ui vi f n :
    bound ui n -> bound vi n -> bound_fun f n ->
    bound_fun ((ui,vi)::f) n.

Lemma rk_bounded (u:elt) : forall k, rk u <= k -> bound u k.
  eapply elt_rect' with 
    (P := fun u => forall k, rk u <= k -> bound u k)
    (Pf := fun f => forall k, rk_fun f <= k -> bound_fun f k).
  all: intros k; intros.
  all: cbn in *.
  all: try match goal with [ H : S _ <=  _ |- _ ] => 
        destruct (le_S_pred H) as [m [-> LL]] end.
  all: try solve [econstructor; eauto].
  all: fold rk_fun in *.
  - econstructor. eapply H. lia. eapply H0. lia.
  - econstructor. eapply H; lia. eapply H0; lia. eapply H1; lia.
Qed.

(* --------------------------------------------------------- *)

(* Minimality: how can we reason about it? *)

Fixpoint remove (u:elt) (v:elt) (f : list (elt * elt)) := 
  match f with 
  | nil => nil
  | (ui,vi) :: f' => if eqb u ui && eqb v vi then remove u v f'
                   else (ui,vi) :: remove u v f'
  end.

(* This seems pretty difficult to work with... *)
Definition minimal (f : list (elt * elt)) : bool := 
  forallb (fun '(ui,vi) => 
             eqb_fun f (remove ui vi f)) f.

(* NOTE: Steve points out that 
           [(zero, bot)] is minimal because we
           cannot have an empty list
   

 *)


(* -------------------------------------------- *)


(** False things *)

(* le terms have le ranks: Not TRUE!  

      abs [(3,bot)] <= abs [(1,bot)]

      abs [(id01,0)] <= [(id0,0)]

 *)
Lemma rk_le : forall k, forall u v, 
    max (rk u) (rk v) <= k -> le' u v k -> rk u <= rk v.
Proof.
  elim /strong_ind.
  move=> n ih.
  have L2: forall m f g, (m < n)%nat -> 
       max (rk_fun f) (rk_fun g) <= m ->
       le_fun' f g m -> rk_fun f <= rk_fun g.
  { 
    intros m f. 
    induction f. intros g Le1 Le2 h1. cbn. lia.
    intros g Le1 Le2 h1. destruct a as [u1 v1].
    cbn in *. fold (le_fun' f g m) in h1.   
    destruct (app' g u1 m) eqn:EA; try done.
    move: (rk_app' EA) => Le3. 
    destruct (le' v1 e m) eqn:Le4; try done.
    rewrite Bool.andb_true_l in h1. 
    apply IHf in h1; try lia.
    apply ih in Le4; try lia; auto.
Abort.    



Definition is_bot e : { e = bot } + { e <> bot }.
Proof. destruct e. 
all: try solve [right; done].
left; done.
Qed.


(* NB: this is not true, but the results are eqb....
   lub [(0,0)] [(1,1)] = [(0,0) ; (1,1)]
   lub [(1,1)] [(0,0)] = [(1,1) ; (0,0)]
 *)
Lemma lub_sym : forall u v w, lub u v = Some w -> lub v u = Some w.
Proof.
  induction u.
  all: move=> v w h.
  all: destruct v; try done.
  all: cbn; cbn in h.
  - rewrite Nat.eqb_sym. 
    destruct (n =? n0) eqn:h1; try done.
    apply Nat.eqb_eq in h1. subst. done.
  - destruct (lub u v) eqn:h1; try done.
    cbn in h. inversion h. rewrite H0.
    apply IHu in h1. rewrite h1. cbn. done.
  - destruct (compatible_fun l l0) eqn:h1; try done.
    apply compatible_fun_sym in h1.
    rewrite h1.
    destruct (lub u v) eqn:h2; try done.
    cbn in h. inversion h. clear h.
    apply IHu in h2. rewrite h2.
    cbn. 
Abort.



(* tail could be nil *)
Lemma valid_fun_tail_false a f : valid_fun (a :: f) -> valid_fun f.
Proof.
  unfold valid_fun. destruct a as [ui vi].
  cbn.
  move=> /andP [/andP [/andP [C1 C1'] C2] F1].
  move: F1 => /andP [/andP [Vui Vvi] h]. 
  apply /andP. split; auto.
  unfold compatible_fun.
Abort.

(* Do we need f to be minimal for this to hold? Yes! 
   Otherwise nothing stops us from having 
   (u, w) and (ui, wi) both in f 
*)
Lemma lemma1 f u ui w wi: 
  valid_fun f -> 
  le u ui -> u <> ui -> 
  app f u = Some w -> 
  app f ui = Some wi -> 
  le w wi /\ w <> wi.
Proof.
  intros Vf Lu Ne APu Api.
  move: Vf => /andP [/andP [h1 _] _ ].
  unfold app in *.
Abort.


Lemma rk_respects u (Vu : valid u) v (Vv : valid v) : 
  eqb u v -> rk u = rk v. 
Admitted.

Lemma le_respects u1 u2 (Vu1 : valid u1) (Vu2 : valid u2)
  v1 v2 (Vv1 : valid v1) (Vv2 : valid v2) : 
  eqb u1 u2 -> eqb v1 v2 -> le u1 v1 = le u2 v2. 
Admitted.


End Unused.


(* --------------------------------------------------------- *)

(*
Fixpoint list_ap {A B } (f : list (A -> B)) (x : list A) : list B := 
  List.flat_map (fun x1 => List.flat_map (fun x2 => (x1 x2 :: nil)) x) f.

Definition list_map2 {A B C} (f : A -> B -> C) (x : list A) (y : list B) : list C := 
  list_ap (List.map f x) y.

(* first nat is level, second is rank *)
Parameter level_rk_enum : nat -> nat -> list elt.

Axiom level_rk_enum_sound : 
  forall k r e, List.In e (level_rk_enum k r) -> rk e <= r /\ level e <= k.
Axiom level_rk_enum_complete : 
  forall k r e, rk e <= r -> level e <= k -> List.In e (level_rk_enum k r).
*)


(* Work on enumerating all elements of a certain level/rank
Fixpoint level_rk_enum (k : nat) (r : nat) : list elt := 
  let fix rk_enum r := 
      (* enumerate all functions of complexity (k,r) *)
      let fix rk_enum_fun r : list (list (elt * elt))
        := match r with 
           | 0 => nil 
           | S n => let q := rk_enum r in     (* all rank r elements *)
                   let p := rk_enum_fun n in (* all rank n functions *)
                   let qp := list_map2 pair q q in (* all pairs of rank n elements *)
                   p  
           end 

      in      
      match r with 
      | 0 => ( bot :: nil) 
      | 1 => ( bot :: tnat :: tuniv k :: zero :: 
              succ bot :: tpi bot (rk_enum_fun 0) :: abs (rk_enum_fun 0) :: nil )
      | S n => let p := rk_enum n in 
              let q := rk_enum_fun n in
              List.map succ p ++ 
                list_map2 tpi p q ++ 
                List.map abs q ++ p
      end
  in match k with 
       | 0 => rk_enum r 
       | S m => rk_enum r ++ level_rk_enum m r
     end
  .

Fixpoint level_rk_enum_complete k r : 
  forall e, rk e <= r -> level e <= k -> List.In e (level_rk_enum k r).
Proof.
  have rk_enum_complete : 
    forall e, rk e <= r -> level e = k -> List.In e (level_rk_enum k r).
  { 
    induction r; intros e h1 h2. 
    - destruct e; cbn in h1; cbn in h2; subst; cbn; try lia.
      left; auto.
    - destruct r. 
      + (* r = 1 *)
        destruct e; cbn in h1; cbn in h2; subst; try lia; cbn.
        all: fold level_fun.
        * left; done.
        * right. left. done.
        * admit.
        * right. right. right. left. done. 
        * destruct e; cbn in h1; cbn; try done.
*)      




