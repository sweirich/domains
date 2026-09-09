(* Finite domain elements, *)

From Stdlib Require Import Relations List Program
     ssreflect ssrfun ssrbool.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Require Import smpl.Smpl.

From Stdlib Require Import Classes.RelationClasses Classes.Morphisms Lia Arith.

Require Import axioms.
Require Import basics.
Require Import preord.
Require Import categories.
Require Import sets.
Require Import finsets.
Require Import esets.
Require Import effective.
Require Import directed.

From Equations Require Import Equations.


Lemma option_eta {A} (o:option A) : match o with Some x => Some x | None => None end = o.
destruct o; done.
Qed.

Lemma forall_ext {A} (f g : A -> bool) (l : list A)  :
  (forall x, List.In x l -> f x = g x) ->
  (forallb f l = forallb g l).
Proof.
  destruct forallb eqn:F1;  destruct (forallb g l) eqn:G1; firstorder.
  + move: F1 => /forallb_forall F1.
    move: (forallb_forall g l)=> [G2 G3].
    rewrite G1 in G3.
    symmetry.
    apply G3.
    intros x InX.
    rewrite <- H; eauto.
  + move: G1 => /forallb_forall G1.
    move: (forallb_forall f l)=> [F2 F3].
    rewrite F1 in F3.
    apply F3.
    intros x InX.
    rewrite -> H; eauto.
Qed.

Lemma list_max_In {A} f {l:list A} x k :  List.In x l -> List.list_max (map f l) <= k -> f x <= k.
Proof.
  induction l; cbn. done.
  intros h1 h2.
  destruct h1.
  - subst. lia.
  - eapply IHl; eauto.
    unfold List.list_max.
    lia.
Qed.

Lemma In_list_max {A} x {l :list A} {f : A -> nat} : In x l -> f x <= List.list_max (map f l).
Proof.
  induction l; cbn. done.
  move=> [h1|h2].
  subst. lia.
  apply IHl in h2.
  unfold List.list_max in h2.
  lia.
Qed.

Lemma andb_cong a b1 b2 : b1 = b2 -> a && b1 = a && b2.
Admitted.

Lemma strong_ind (P : nat -> Prop) :
  (forall m, (forall k : nat, k < m -> P k)%nat -> P m) -> forall n, P n.
Proof. intro h. 
       induction n as [ n IHn ] using                  (well_founded_induction lt_wf). eauto. Qed.

Module Raw.

(* Finite elements: raw form. Includes invalid functions. *)
Inductive elt := 
  | bot : elt 
  | tnat : elt 
  | tuniv : nat -> elt
  | zero : elt
  | succ : elt -> elt
  | tpi  : elt -> list (elt * elt) -> elt
  | abs : list (elt * elt) -> elt.


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


Derive NoConfusion NoConfusionHom Subterm for elt.


(* The rank of a term is the maximum depth of its tree.

   NB: original definition
   rk(f) = 1 + max(rk(ui), rk(f (ui))) if 
   f = (u1 → v1,...,ul → vl) is minimal and l > 0. 

 An important property of the rank is that
   rk(u ∨ v) <= max(rk(u), rk(v)) and
   rk(f (u)) < rk(f) for all u.
 *)

Fixpoint rk (u : elt) : nat :=
  let fix rk_fun f :=
    match f with
      | nil => 0
      | (ui, vi) :: tl => max (max (rk ui) (rk vi)) (rk_fun tl)
    end in
  match u with 
  | bot => 0 
  | tnat => 1
  | tuniv k => 1
  | zero => 1 
  | succ v => 1 + rk v
  | tpi a f => 1 + (max (rk a) (rk_fun f))
  | abs f => 1 + rk_fun f
  end.

Fixpoint rk_fun (f : list (elt * elt)) := 
    match f with
      | nil => 0
      | (ui, vi) :: tl => max (max (rk ui) (rk vi)) (rk_fun tl)
    end.

(* We can only compute the lub of compatible functions. *)
Fixpoint compatible u v {struct u} : bool := 
  let compatible_fun (f g : list (elt * elt)) : bool :=
    List.forallb (fun '(ui,vi) => 
      List.forallb (fun '(uj,vj) => 
         (compatible ui uj) ==> (compatible vi vj)) g) f
  in
  match u , v with 
  | _ , bot => true
  | bot , _ => true
  | tnat , tnat => true
  | zero , zero => true
  | succ u , succ v => compatible u v
  | tpi a f , tpi b g => 
      (compatible a b) && (compatible_fun f g)
  | abs f , abs g => compatible_fun f g 
  | tuniv i , tuniv j => Nat.eqb i j
  | _ , _ => false
  end.

(* Functions are compatible when it is valid to 
   combine them together. *)

Definition compatible_fun (f g : list (elt * elt)) : bool :=
  List.forallb (fun '(ui,vi) => 
     List.forallb (fun '(uj,vj) => 
       (compatible ui uj) ==> (compatible vi vj)) g) f.


(* Least upper bound of two terms *)
(* This function is only defined on compatible elements *)
Fixpoint lub (u v : elt) : option elt :=
  match u, v with
  | bot,    v    => Some v
  | u,      bot  => Some u
  | tnat,   tnat => Some tnat
  | zero,   zero => Some zero
  | tuniv i, tuniv j =>
      if Nat.eqb i j then Some (tuniv i) else None
  | succ u, succ v =>
      option_map succ (lub u v)
  | tpi a f, tpi b g =>
      if compatible_fun f g
      then option_map (fun c => tpi c (f ++ g)) (lub a b)
      else None
  | abs f, abs g =>
      if compatible_fun f g then Some (abs (f ++ g)) else None
  | _, _ => None
  end.

(* Fold lub over a list of elements *)
Definition lub_list (xs : list elt) : option elt := 
  List.fold_right (fun e o => option_bind (lub e) o) (Some bot) xs.   



(* cannot use equations as it doesn't support mutual definitions *)

(* We need a termination metric for this definition... 
   it is (max (rk u) (rk v)). *)
Fixpoint le' (u v : elt) k : bool := 
  let app g u m : option elt := 
    lub_list (List.map (fun '(ui,vi) => 
                          if le' ui u m then vi else bot) g) in
      
  let le_fun f g m := 
    List.forallb (fun '(ui,vi) => match (app g ui m) with 
                               | Some v => le' vi v m
                               | None => false
                               end) f 
  in
  match u , v with 
  | bot , _ => true
  | tnat , tnat => true
  | zero , zero => true
  | succ u0 , succ v0 => 
      match k with 
      | 0 => false 
      | S m => le' u0 v0 m
      end
  | tpi a f , tpi b g => 
      match k with 
      | 0 => false 
      | S m => (le' a b m) && (le_fun f g m)
      end
  | tuniv i , tuniv j => Nat.eqb i j
  | abs f , abs g => 
      match k with 
      | 0 => false 
      | S m => le_fun f g m
      end
  | _ , _ => false
  end.

Definition le (u v : elt) := le' u v (max (rk u) (rk v)).

Definition app_m (f : list (elt * elt)) (u : elt) m : option elt := 
   lub_list (List.map (fun '(ui,vi) => 
                         if le' ui u m then vi else bot) f).
Definition app (f : list (elt * elt)) (u : elt) : option elt := 
   lub_list (List.map (fun '(ui,vi) => 
                         if le ui u then vi else bot) f).

Definition le_fun' f g m := 
  List.forallb (fun '(ui,vi) => 
                  match (app_m g ui m) with 
                  | Some v => le' vi v m
                  | None => false
                  end) f.
Definition le_fun f g := 
  List.forallb (fun '(ui,vi) => 
                  match (app g ui) with 
                  | Some v => le vi v 
                  | None => false
                  end) f.

Lemma le_succ u v : le (succ u) (succ v) = le u v.
Proof.
  reflexivity.
Qed.

Definition eqb (u v:elt) := le u v && le v u.

(* inductive version of app *)
Fixpoint app' (f : list (elt * elt)) (u : elt) : option elt := 
  match f with
  | nil => Some bot
  | ((ui,vi) :: tail) => 
      let appt := app' tail u in 
      if (le ui u) then match appt with 
                          | Some t => lub vi t | None => None end else appt
  end.


(* --------------------------------------------------------- *)




(* A valid function is one that is compatible with itself. 
   i.e. all compatible domains produce compatible results

   A term is valid when all of its subterms are valid, including
   functions.
*)

Fixpoint valid u : bool := 
  let valid_fun f := 
    (compatible_fun f f) &&
    (List.forallb (fun '(ui,vi) => (valid ui) && (valid vi)) f)
  in
  match u with 
  | abs f => valid_fun f
  | tpi a f =>  (valid a) && (valid_fun f)
  | succ v => valid v
  | _ => true
  end.

Definition valid_fun f := 
    (compatible_fun f f) &&
    (List.forallb (fun '(ui,vi) => (valid ui) && (valid vi)) f).

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

Lemma le_S_pred : forall m n, S m <= n -> exists j, n = S j /\ (m <= j).
    intros m n Le. 
    inversion Le; subst; eexists; split; eauto; try lia.
Qed.

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

(* -------------------------------------------- *)

Lemma In_rk_fun1 {ui vi l} : In (ui, vi) l -> rk ui <= rk_fun l.
induction l.
- intro h. inversion h.
- intros [->|h1].
  + cbn. lia.
  + destruct a as [uj vj]. cbn.
    apply IHl in h1. lia.
Qed.


Lemma In_rk_fun2 {ui vi l} : In (ui, vi) l -> rk vi <= rk_fun l.
induction l.
- intro h. inversion h.
- intros [->|h1].
  + cbn. lia.
  + destruct a as [uj vj]. cbn.
    apply IHl in h1. lia.
Qed.

Lemma rk_fun_app {f g} : (rk_fun (f ++ g)) = max (rk_fun f) (rk_fun g).
Proof.
  induction f.
  all: cbn. done.
  destruct a as [u v].
  rewrite IHf.
  lia.
Qed.

(* This is more difficult than it should be. Need to prove
   it by strong induction on the depth of the two terms. 
*)
Lemma compatible_sym : forall u v, compatible u v -> compatible v u.
Proof.
  have LEMMA: 
     forall (k : nat) (u v : elt), 
       Init.Nat.max (rk u) (rk v) <= k -> compatible u v -> compatible v u.
  { 
    elim /strong_ind.
    move=> m ih u v Le. 
    destruct u; destruct v; cbn in *; try done.
    all: try match goal with [ H : S _ <=  _ |- _ ] => 
        destruct (le_S_pred H) as [m0 [-> LL]] end.
    - cbn. rewrite PeanoNat.Nat.eqb_sym. done.
    - eauto.
    - fold rk_fun in *.
      move=> /andP [h1 /forallb_forall h2].
      apply /andP.  split. eapply ih; eauto. lia.
      apply /forallb_forall.
      intros [ui vi] Inl0.
      apply /forallb_forall.
      intros [uj vj] Inl.
      apply /implyP.
      specialize (h2 _ Inl). cbn in h2.
      move: h2 => /forallb_forall h2.
      specialize (h2 _ Inl0). cbn in h2.
      move: h2 => /implyP h2.
      move: (In_rk_fun2 Inl) => Levj. 
      move: (In_rk_fun2 Inl0) => Levi. 
      intro x. eapply ih; eauto. lia.
      eapply h2.
      eapply ih; eauto. 
      move: (In_rk_fun1 Inl) => Leuj. 
      move: (In_rk_fun1 Inl0) => Leui. 
      lia.
    - fold rk_fun in *.
      move=> /forallb_forall h2.
      apply /forallb_forall.
      intros [ui vi] Inl0.
      apply /forallb_forall.
      intros [uj vj] Inl.
      apply /implyP.
      specialize (h2 _ Inl). cbn in h2.
      move: h2 => /forallb_forall h2.
      specialize (h2 _ Inl0). cbn in h2.
      move: h2 => /implyP h2.
      move: (In_rk_fun2 Inl) => Levj. 
      move: (In_rk_fun2 Inl0) => Levi. 
      intro x. eapply ih; eauto. lia.
      eapply h2.
      eapply ih; eauto. 
      move: (In_rk_fun1 Inl) => Leuj. 
      move: (In_rk_fun1 Inl0) => Leui. 
      lia.
  }   
  move=> u v. eapply LEMMA; eauto.
Qed.

(* NB: compatibility is not transtive because of bot *)

(* Terms that are compatible have a least upper bound *)
Lemma compatible_lub_exists u v : 
  compatible u v -> { w & lub u v = Some w}.
Proof.
  move: v.
  induction u.
  all: destruct v; cbn.
  all: intro h; try done.
  all: try solve [eexists; eauto].
  - rewrite h.
    eexists; eauto.
  - edestruct IHu as [w ->]; eauto.
    eexists; cbn; eauto.
  - move: h => /andP [h1 h2].
    edestruct IHu as [w ->]; eauto.
    exists (tpi w (l ++ l0)).
    rewrite /compatible_fun h2.
    cbn; eauto.
  - eexists.   
    rewrite /compatible_fun h.
    cbn; eauto.
Qed.


(* We can append compatible functions together *)
Definition valid_append f g : 
  valid_fun f -> valid_fun g -> compatible_fun f g 
  -> valid_fun (f ++ g).
Proof.
  move=> /andP [Cf Vf] /andP [Cg Vg] Cfg.
  apply /andP. split.
  - unfold compatible_fun in *.
    apply forallb_forall. 
    move=> [ui vi] Ini.
    apply forallb_forall.
    move=> [uj vj] Inj.
    move: Cf => /forallb_forall Cf. 
    move: Cg => /forallb_forall Cg.
    move: Cfg => /forallb_forall Cfg.
    destruct (in_app_or _ _ _ Ini) as [Ifi|Igi];
    destruct (in_app_or _ _ _ Inj) as [Ifj|Igj];
    try move: (Cf _ Ifi) => /forallb_forall Cfi; 
    try move: (Cf _ Ifj) => /forallb_forall Cfj;
    try move: (Cg _ Igi) => /forallb_forall Cgi;
    try move: (Cg _ Igj) => /forallb_forall Cgj.
    + eapply (Cfi _ Ifj).
    + specialize (Cfg _ Ifi). cbn in Cfg.
      move: Cfg => /forallb_forall Cfg.
      specialize (Cfg _ Igj). cbn in Cfg.
      done.
    + specialize (Cfg _ Ifj). cbn in Cfg.
      move: Cfg => /forallb_forall Cfg.
      specialize (Cfg _ Igi). cbn in Cfg.
      admit.
    + eapply (Cgi _ Igj).
  - admit.
Admitted.

Lemma lub_rk u v w : 
  lub u v = Some w -> rk w = max (rk u) (rk v).
Proof.
  move: v w.
  induction u.
  all: intros v w.
  all: cbn.
  all: destruct v.
  all: intros h; inversion h; subst.
  all: cbn; auto.
  - destruct PeanoNat.Nat.eqb; inversion h. cbn. reflexivity.
  - destruct (lub u v) eqn:LU; cbn in h; inversion h. 
    cbn. f_equal. eauto. 
  - fold rk_fun.
    destruct (lub u v) eqn:LU;
    destruct compatible_fun eqn:C; 
    inversion h.
    cbn. fold rk_fun. f_equal.
    apply IHu in LU. rewrite LU.
    rewrite rk_fun_app. 
    lia.
  - destruct compatible_fun eqn:C. 2: done.
    inversion h. cbn.
    f_equal. fold rk_fun.
    rewrite rk_fun_app. 
    reflexivity.
Qed.

Lemma lub_list_rk xs u : 
  lub_list xs = Some u -> rk u = List.list_max (List.map rk xs).
Proof.  
  move: u.
  induction xs.
  - intros u h; inversion h. subst. done.
  - cbn; intros u h. 
    destruct fold_right eqn:L. 2: done.
    cbn in h. 
    apply IHxs in L. unfold List.list_max in L. rewrite <- L.
    eapply lub_rk.
    done.
Qed.    

Lemma lub_bot_l x : lub bot x = Some x.
Proof.
  reflexivity.
Qed.


(* 
   rk(f (u)) <= rk(f) for all u.
*)
Lemma rk_app: forall m f u w, 
       app_m f u m = Some w -> rk w <= rk_fun f.
Proof.
    intros m f u w.
    unfold app_m.
    intros h. rewrite (lub_list_rk h). clear h.
    induction f.
    - cbn. auto.
    - destruct a as [ui vi]. cbn.
      eapply Nat.max_le_compat.
      2: { eapply IHf. } 
      destruct (le' ui u m). lia. cbn. lia.
Qed.


(* le terms have le ranks: Not TRUE!  [(3,bot)] <= [(1,bot)] *)
Lemma le_rk : forall k, forall u v, 
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
    destruct (app_m g u1 m) eqn:EA; try done.
    move: (rk_app EA) => Le3. 
    destruct (le' v1 e m) eqn:Le4; try done.
    rewrite Bool.andb_true_l in h1. 
    apply IHf in h1; try lia.
    apply ih in Le4; try lia; auto.
Abort.    

    

Lemma rk_enough : forall k u v,
  max (rk u) (rk v) <= k -> (le' u v (max (rk u) (rk v))) = (le' u v k).
Proof.
  elim /strong_ind.
  move=> m ih u v Le.
  destruct m.
  - destruct u; destruct v; cbn in *; auto.
    all: try lia.
  - have LEM1:
      forall g ui r, r <= m -> (max (rk_fun g) (rk ui)) <= r ->
                app_m g ui r = app_m g ui m.
      { subst. 
        move=> g ui r Le1 Le2.
        unfold app_m.
        f_equal.
        eapply map_ext_in.
        move=> [uj vj] Ing.
        move: (In_rk_fun1 Ing) => h1.
        move: (In_rk_fun2 Ing) => h2.
        rewrite <- ih; try lia.
        rewrite <- (ih m); try lia.
        reflexivity.
      }
      have LEM2: 
        forall l l0 r, 
          max (rk_fun l) (rk_fun l0) <= r -> r <= m -> 
          le_fun' l l0 r = le_fun' l l0 m.
      {
        subst. 
        move=> f g r Le1 Le2.
        eapply forall_ext.
        move=> [ui vi] Inl.
        move: (In_rk_fun1 Inl) => h1.
        move: (In_rk_fun2 Inl) => h2.
        rewrite LEM1; try lia.
        destruct app_m eqn:EA; try done.
        move: (rk_app EA) => Le3.
        rewrite <- ih; try lia.
        rewrite <- (ih m); try lia.
        auto.
      } 

    destruct u; destruct v. 
    all: try solve [cbn in *; auto].  
    all: cbn in *.
    all: fold rk_fun in *.
    + erewrite (ih m); eauto. lia.
    + rewrite <- ih; try lia. rewrite <- (ih m); try lia.
      f_equal.
      eapply LEM2; try lia.
    + eapply LEM2; try lia.
Qed.


Lemma rk_app_enough :
      forall r g ui, (max (rk_fun g) (rk ui)) <= r ->
                app_m g ui r = app_m g ui (max (rk_fun g) (rk ui)).
  move=> r g ui Le1.
  unfold app_m.
  f_equal.
  eapply map_ext_in.
  move=> [uj vj] Ing.
  move: (In_rk_fun1 Ing) => h1.
  move: (In_rk_fun2 Ing) => h2.
  rewrite <- rk_enough; try lia.
  rewrite <- (@rk_enough (Init.Nat.max (rk_fun g) (rk ui))); try lia.
  reflexivity.
Qed.

Lemma app_m_app :
  forall r g ui, (max (rk_fun g) (rk ui)) <= r -> app_m g ui r = app g ui.
Proof.
  intros.
  unfold app.
  unfold app_m.
  f_equal.
  eapply map_ext_in.
  move=> [uj vj] Ing.
  move: (In_rk_fun1 Ing) => h1.
  move: (In_rk_fun2 Ing) => h2.
  unfold le.
  rewrite <- rk_enough; try lia.
  done.
Qed.

Lemma rk_fun_enough : 
        forall r l l0, 
          max (rk_fun l) (rk_fun l0) <= r ->
          le_fun' l l0 r = le_fun' l l0 (max (rk_fun l) (rk_fun l0)).
Proof.
  move=> r f g Le1.
  eapply forall_ext.
  move=> [ui vi] Inl.
  move: (In_rk_fun1 Inl) => h1.
  move: (In_rk_fun2 Inl) => h2.
  rewrite rk_app_enough; try lia.
  rewrite (@rk_app_enough (Init.Nat.max (rk_fun f) (rk_fun g))); 
    try lia.
  destruct app_m eqn:EA; try done.
  move: (rk_app EA) => Le3.
  rewrite <- rk_enough; try lia.
  rewrite <- (@rk_enough (Init.Nat.max (rk_fun f) (rk_fun g))); try lia.
  auto.
Qed. 

Lemma le_fun'_le_fun r l l0 :
  max (rk_fun l) (rk_fun l0) <= r ->
  le_fun' l l0 r = le_fun l l0.
Proof.
  intros h. unfold le_fun', le_fun.
  eapply forall_ext.
  move=> [ui vi] Inl.
  move: (In_rk_fun1 Inl) => h1.
  move: (In_rk_fun2 Inl) => h2.
  rewrite <- (app_m_app (r := r)); try lia.
  destruct app_m eqn:Ev; try done.
  move: (rk_app Ev) => h3.
  unfold le.
  rewrite <- rk_enough; try lia. 
  done.
Qed.

Lemma le_tpi a f b g : le (tpi a f) (tpi b g) = 
  (le a b) && (le_fun f g).
Proof.
  unfold le.
  change (rk (tpi a f)) with (S (max (rk a) (rk_fun f))).
  change (rk (tpi b g)) with (S (max (rk b) (rk_fun g))).
  rewrite <- Nat.succ_max_distr.
  cbn.
  remember (max (rk a) (rk_fun f)) as r1.
  remember (max (rk b) (rk_fun g)) as r2.
  remember (max r1 r2) as r.
  f_equal.
  rewrite <- rk_enough. done. lia.
  erewrite <- (le_fun'_le_fun (r:=r)). 2: lia.
  reflexivity.
Qed.

Lemma le_abs f g : le (abs f) (abs g) = le_fun f g.
  unfold le. cbn. fold rk_fun.
  remember (max (rk_fun f) (rk_fun g)) as r.
  rewrite <- (le_fun'_le_fun (r:=r)). 2: lia.
  reflexivity.
Qed.  

Lemma Forall2_rk_fun f g:
  Forall2 (fun '(u1,v1) '(u2, v2) => rk u1 <= rk u2 /\ rk v1 <= rk v2) f g ->
  rk_fun f <= rk_fun g.
Proof.
  move: g.
  induction f.
  - intros g h. inversion h. done.
  - intros g h. inversion h. subst. clear h.
    destruct a as [u1 v1].
    destruct y as [u2 v2].
    cbn. 
    specialize (IHf l' H3).
    destruct H1.
    lia.
Qed.


Lemma app_spec : app = app'.
smpl extensionality.
induction x.
- smpl extensionality. cbn. auto.
- smpl extensionality. intros u.
  destruct a as [ui vi].
  cbn.
  destruct (le ui u) eqn:LE.
  + rewrite <- IHx. 
    reflexivity.
  + rewrite <- IHx.
    unfold basics.option_bind. replace (lub bot) with (@Some elt). 
    2: { smpl extensionality. intro y. reflexivity. } 
    rewrite option_eta.
    reflexivity.
Qed.

(* Compatibility is only reflexive for valid terms. *)
Lemma compatible_refl u : valid u -> compatible u u.
Proof.
  induction u.
  all: cbn.
  all: auto.
  - intro h. apply PeanoNat.Nat.eqb_refl.
  - move=> /andP [h1 /andP [h2 h3]].
    apply /andP. split; auto.
  - move=> /andP [h1 _].    
    apply h1.
Qed.


(* The lub of valid elements is valid *)
Lemma valid_lub u v w : valid u -> valid v -> 
                        lub u v = Some w -> valid w.
Proof.
  move: v w.
  induction u.
  all: intros v w Vu Vw h.
  all: destruct v; cbn in h, Vu, Vw; inversion h; subst; try done.
  - destruct Nat.eqb; inversion h. done.
  - destruct (lub u v) eqn:EQ; inversion h. cbn. 
    eapply IHu; eauto.
  - move: Vu => /andP [Vu h1].
    move: Vw => /andP [Vw h3].
    destruct (compatible_fun l l0) eqn:Co. 2: done.
    destruct (lub u v) eqn:LUB. 2: done.
    inversion h. cbn. clear h H0.
    apply /andP. split; eauto.
    eapply valid_append; eauto.
  - destruct (compatible_fun l l0) eqn:Co. 2: done.
    inversion h. cbn.
    eapply valid_append; eauto.
Qed.


Lemma valid_fun_tail a f : valid_fun (a :: f) -> valid_fun f.
Proof.
  unfold valid_fun. destruct a as [ui vi].
  cbn.
  move=> /andP [/andP [/andP [C1 C1'] C2] F1].
  move: F1 => /andP [/andP [Vui Vvi] h]. 
  apply /andP. split; auto.
  unfold compatible_fun.
Admitted.

Lemma app_exists f u : valid_fun f -> valid u -> 
   { w & app f u = Some w & valid_fun ((u,w)::f) }.
Proof.
  rewrite app_spec.
  induction f.
  - intros h Vu. cbn. eexists. eauto. unfold valid_fun. cbn. rewrite compatible_refl; auto. cbn.
    rewrite Vu. cbn. auto.
  - intros h Vu.
    destruct a as [ui vi].
    cbn.
    move: (valid_fun_tail h) => Vf.
    destruct (IHf Vf) as [v IH]; auto.
    rewrite IH.
    destruct (le ui u) eqn:Ei.
Admitted.

Lemma lemma1 f u ui w wi: 
  valid_fun f -> le u ui -> app f u = Some w -> 
  app f ui = Some wi -> le w wi.
Proof.
  intros Vf Lu APu Api.
  unfold app in *.
Admitted.
  
End Raw.

(* -------------------------------------------------------- *)


Module Valid.

Definition elt := { u : Raw.elt & Raw.valid u }.

(* A finite function is functional and not equivalent to bot *)
Definition finfun := { 
    f : list (Raw.elt * Raw.elt) 
        & Raw.valid_fun f 
        & exists a b, Raw.app f a = Some b /\ not (Raw.eqb b Raw.bot) 
   }.


Definition compatible (u v : elt) := 
  Raw.compatible (projT1 u) (projT1 v).

Definition lub (u v : elt) (h : compatible u v) : elt. 
Proof.
  destruct (Raw.compatible_lub_exists h) as [w Lw].
  exists w. eapply (Raw.valid_lub (projT2 u) (projT2 v) Lw).
Defined.

Definition bot : elt. exists Raw.bot. auto. Defined.
Definition tnat : elt. exists Raw.tnat. auto. Defined.

Definition le (u v : elt) : bool :=
  Raw.le (projT1 u) (projT1 v).

Definition le_fun (u v : finfun) : bool :=
  Raw.le_fun (projT1 u) (projT1 v).

Definition app (f : finfun) (v : elt) : elt.
  move: f => [rf Vf].
  move: v => [rv Vv].
  destruct (Raw.app_exists Vf Vv) as [w h].
  exists w. unfold Raw.valid_fun in i.
  cbn in i.
  move: i => /andP [h1 /andP [/andP[_ h2]_]]. done.
Defined.

Definition veq (u : elt) (v: elt) : Prop := 
  Raw.eqb (projT1 u) (projT1 v).
Definition veq_fun (u v : finfun) : Prop := 
  le_fun u v && le_fun v u.

End Valid.

#[export] Instance eq_elt_equivalence : Equivalence Valid.veq.
unfold Valid.veq.
constructor.
- intros [u Vu].
  cbn.
Admitted.

#[export] Instance eqfun_elt_equivalence : Equivalence Valid.veq_fun.
Admitted.

Instance Proper_app : Proper (Valid.veq_fun ==> Valid.veq ==> Logic.eq) Valid.app.
intros x y Exy. intros w v Ewv.
Admitted.


Module Q.

Definition elt  := quot Valid.veq. 

Definition finfun := quot Valid.veq_fun.

Parameter valid_fun : list (elt * elt) -> Prop.

Parameter to_finfun : forall (l : list (elt * elt)), valid_fun l -> finfun.


Definition bot  : elt. exact (to_quot Valid.bot). Defined.
Definition zero : elt. Admitted.
Definition succ : elt -> elt. Admitted.
Definition tpi : elt -> finfun -> elt. Admitted.
Definition abs : finfun -> elt. Admitted.
Definition tuniv : nat -> elt. Admitted.
Definition tnat : elt. exact (to_quot Valid.tnat). Defined.

Definition compatible : elt -> elt -> bool. Admitted.
Definition lub : forall u v, compatible u v -> elt. Admitted.
Definition app : finfun -> elt -> elt. Admitted.
Definition le : elt -> elt -> Prop. Admitted.
Definition le_fun : finfun -> finfun -> Prop. Admitted.

Definition complexity : elt -> nat.

  

(* needed for induction principle *)
Definition app_valid (f : list (elt * elt)) (Vf : valid_fun f) (u : elt) : elt. Admitted.

Definition le_fun_valid :
  forall (f g : list (elt * elt)) (Vf : valid_fun f) (Vg : valid_fun g), bool.
Admitted. 
(*  List.forallb (fun '(ui,vi) => lub (app_valid Vg ui) vi) f. *)

Definition eq_fun (f : Valid.finfun) (g : Valid.finfun) := 
  forall (u : Valid.elt), Valid.veq (Valid.app f u) (Valid.app g u).


Definition elt_ind : forall (P : elt -> Prop) (Pf : finfun -> Prop), 
    (P bot) ->
    (P zero) -> 
    (forall e, P e -> P (succ e)) ->
    (forall f, Pf f -> P (abs f)) -> 
    (forall e f, P e -> Pf f -> P (tpi e f)) -> 
    P tnat ->
    (forall k, P (tuniv k)) ->
    (forall l (Vf: valid_fun l), (forall u v, In (u,v) l -> P u /\ P v) -> Pf (to_finfun Vf)) ->
    forall e, (P e) /\ forall f, Pf f.
Admitted.

(* not provable (yet!) *)
(*
Definition elt_rectNonDep : forall (P : Type) (Pf : Type), 
    P ->
    P  -> 
    (elt -> P -> P) ->
    (Pf -> P) -> 
    (P -> Pf -> P) -> 
    P ->
    (nat -> P) ->
    (H : forall f (Vf: valid_fun f), (g : list (P * P)) -> Pf) ->
    (forall f (Vf: valid_fun f) g (Vg: valid_fun g) 
       (to_finfun Vf) = (to_finfun Vg) ->
       forall (Ef Eg : list(P * P)),
        (H Vf Ef) = (H Vg Eg)) ->
    (elt -> P) /\ (finfun -> Pf).
Abort. *)

(*
Definition elt_rect : forall (P : elt -> Type) (Pf : finfun -> Type), 
    (P bot) ->
    (P zero) -> 
    (forall e, P e -> P (succ e)) ->
    (forall f, Pf f -> P (abs f)) -> 
    (forall e f, P e -> Pf f -> P (tpi e f)) -> 
    P tnat ->
    (forall k, P (tuniv k)) ->
    (H : forall l (Vf: valid_fun l), (forall u v, In (u,v) l -> P u * P v) -> Pf (to_finfun Vf))) ->
    (forall f (Vf: valid_fun f) g (Vg: valid_fun g) 
       (to_finfun Vf) = (to_finfun Vg) ->
       (Ef : forall u v, In (u,v) f -> P u * Pv)
       (Eg : forall u v, In (u,v) g -> P u * Pv), 
        (H Vf Ef) = (H Vg Eg)) ->
    forall e, (P e) * forall f, Pf f.
*)


(* Section 3 *)
Inductive wt : elt -> elt -> Prop := 
  | wt_fun f (Vf : valid_fun f) a g : 
    (forall ui vi, List.In (ui,vi) f ->
              wt ui a /\ wt vi (app g ui)) ->
    wt (abs (@to_finfun f Vf)) (tpi a g).

Inductive type : elt -> Prop := .

