(* Finite domain elements, raw definitions and properties *)

From Stdlib Require Import Relations List Program
     ssreflect ssrfun ssrbool.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Require Import smpl.Smpl.

From Stdlib Require Import Classes.RelationClasses Classes.Morphisms Lia Arith.


Require Import utils.all.
Require Import categories.all.
Require Import preord.
Require Import categories.
Require Import sets.
Require Import finsets.
Require Import esets.
Require Import effective.
Require Import directed.

From Equations Require Import Equations.

(* Library stuff *)

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
intros ->. reflexivity.
Qed.

Lemma le_S_pred : forall m n, S m <= n -> exists j, n = S j /\ (m <= j).
    intros m n Le. 
    inversion Le; subst; eexists; split; eauto; try lia.
Qed.

(* If we fold with a monoid, then we can decompose appends into sub folds *)
Lemma fold_right_app : 
  forall {A : Type} (base : A) (op : A -> A -> A),
  (forall y : A, op base y = y) -> 
  (forall x y z : A, op x (op y z) = op (op x y) z) -> 
  forall l l' : list A, fold_right op base (l ++ l') = op (fold_right op base l) (fold_right op base l').
Proof.
  intros A base op idL assoc.
  induction l; move=> l'.
  cbn. rewrite idL. done.
  cbn. rewrite IHl.
  rewrite assoc. done.
Qed.


Lemma strong_ind (P : nat -> Prop) :
  (forall m, (forall k : nat, k < m -> P k)%nat -> P m) -> forall n, P n.
Proof. intro h. 
       induction n as [ n IHn ] using    
        (well_founded_induction lt_wf). eauto. Qed.

Module Raw.

(* Finite elements: raw form.

   Functions are represented as finite mappings from 
   arguments to results.

 *)
Inductive elt := 
  | bot   : elt 
  | tnat  : elt 
  | tuniv : elt
  | zero  : elt
  | succ  : elt -> elt
  | tpi   : elt -> list (elt * elt) -> elt
  | abs   : list (elt * elt) -> elt.


(* --------------------------------------------------- *)
(* The rank of a term is the maximum depth of its tree.

   NB: paper definition is:
   rk(f) = 1 + max(rk(ui), rk(f (ui))) if 
   f = (u1 → v1,...,ul → vl) is minimal and l > 0. 

   Below, we define it over all terms, including nonminimal ones.

 Properties of rank:
   [rk_lub]    rk(lub u v) = max(rk u, rk v) 
   [rk_app]    rk(app f u) <= rk(f) for all u

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
  | tuniv => 1
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

(* --------------------------------------------------- *)
(* ** compatibility and lub *)

(* We can only compute the lub of compatible functions.
   NB: compatible <-> Comp *)
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
  | tuniv , tuniv => true
  | _ , _ => false
  end.

Definition coherent_with f '(u, v) := 
  forallb (fun '(uj,vj) => compatible u uj ==> compatible v vj) f.

Definition compatible_fun (f g : list (elt * elt)) : bool :=
  List.forallb (fun '(ui,vi) => 
     List.forallb (fun '(uj,vj) => 
       (compatible ui uj) ==> (compatible vi vj)) g) f.

(* Two functions are compatible when all pairs in the first are 
   coherent with the second *)
Lemma compatible_fun_spec f g : 
  compatible_fun f g = List.forallb (coherent_with g) f.
Proof. reflexivity. Qed.

(* Least upper bound of two terms *)
(* This function is only defined on compatible elements *)
Fixpoint lub (u v : elt) : option elt :=
  match u, v with
  | bot,    v    => Some v
  | u,      bot  => Some u
  | tnat,   tnat => Some tnat
  | zero,   zero => Some zero
  | tuniv, tuniv => Some tuniv
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

Definition lub_opt (o1 : option elt) (o2: option elt) : option elt := 
  match o1,o2 with 
    | Some e1 , Some e2 => lub e1 e2
    | _ , _ => None
  end.

Definition lub_list_opt : list (option elt) -> option elt := 
  List.fold_right lub_opt (Some bot).

(* Fold lub over a list of elements. *)
Definition lub_list (xs : list elt) : option elt := 
  lub_list_opt (List.map Some xs).   

(*
Unset Implicit Arguments.
Section AllInP.
  Context {A : Type}.

  Equations forallb_InP (l : list A) (H : forall x : A, In x l -> bool) : bool :=
  | nil, _ := true ;
  | (cons x xs), H := (H x _) && (forallb_InP xs (fun x inx => H x _)).

End AllInP.

Lemma forallb_InP_spec {A} (f : A -> bool) (l : list A) :
  forallb_InP l (fun x _ => f x) = List.forallb f l.
Proof.
  remember (fun x _ => f x) as g.
  funelim (forallb_InP l g) => //; simpl. f_equal.
  now rewrite (H0 f).
Qed.

Section MapInP.
  Context {A B : Type}.

  Equations map_InP (l : list A) (f : forall x : A, In x l -> B) : list B :=
  map_InP nil _ := nil;
  map_InP (cons x xs) f := cons (f x _) (map_InP xs (fun x inx => f x _)).
End MapInP.

Lemma map_InP_spec {A B : Type} (f : A -> B) (l : list A) :
  map_InP l (fun (x : A) _ => f x) = List.map f l.
Proof.
  remember (fun (x : A) _ => f x) as g.
  funelim (map_InP l g) => //; simpl. f_equal. cbn in H.
  now rewrite (H f0).
Qed.

Definition max_rk '(u, v) := max (rk u) (rk v).


Definition app' g ui le' : option elt := 
  lub_list (map_InP  
              (fun '(uj,vj) inL => 
                 if compatible uj ui && 
                    le' uj ui _ then vj else bot) g).

Definition le_fun f g le' := 
    forallb_InP (fun '(ui,vi) inL => 
                   match (app g ui le') with 
                   | Some v => le' vi v _
                   | None => false
                   end) f. 
*)

(*
From Stdlib Require Import Wellfounded.Wellfounded.

Print Instances WellFounded.
Set Typeclasses Debug.

Equations? le (u : elt) (v: elt) : bool
 by wf (u,v) (fun (x y : elt*elt) => (max_rk x < max_rk y)%nat) :=
 le bot _ := true ;
 le tnat tnat := true ;
 le zero zero := true ;
 le (succ u0) (succ v0) := le u0 v0 ;
(*  le (tpi a f) (tpi b g) := le a b && le_fun f g le ; *)
 le _ _ := false.
 
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
  | tuniv , tuniv => true
  | abs f , abs g =>
      match k with
      | 0 => false
      | S m => le_fun f g m
      end
  | _ , _ => false
  end.

Section Helpers.

Parameter le' : forall (u v : elt) -> bool.



End Helpers.
*)

(* --------------- le ---------------- *)

(* For finite functions, when do we have f <= g ?
   We want an extensional definition that says:
   forall x, app f x <= app g x 
   However, we also want a decidable definition. 
   so we look at all of the (ui,vi) in f and see what they do in g.
*) 

(* ACKTUALLY le should be called leb because it is decidable. *)

(* The termination metric for this definition is (max (rk u) (rk v)). *)
(* NB: cannot use equations as it doesn't support mutual definitions *)
Fixpoint le' (u v : elt) k : bool := 
  let app g ui m : option elt := 
    lub_list (List.map 
                (fun '(uj,vj) => 
                   if compatible uj ui && le' uj ui m then vj else bot) g) in
      
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
  | tuniv , tuniv => true
  | abs f , abs g =>
      match k with
      | 0 => false
      | S m => le_fun f g m
      end
  | _ , _ => false
  end.


Definition app' (f : list (elt * elt)) (u : elt) m : option elt := 
   lub_list (List.map (fun '(ui,vi) => 
           if compatible ui u && le' ui u m then vi else bot) f).


Definition le_fun' f g m := 
  List.forallb (fun '(ui,vi) => 
                  match (app' g ui m) with 
                  | Some v => le' vi v m
                  | None => false
                  end) f.

(* leFinEl *)
Definition le (u v : elt) := le' u v (max (rk u) (rk v)).


(* EvalFun *)
Definition app (f : list (elt * elt)) (u : elt) : option elt := 
   lub_list (List.map (fun '(ui,vi) => 
           if compatible ui u && le ui u then vi else bot) f).

(* leFun *)
Definition le_fun f g := 
  List.forallb (fun '(ui,vi) => match (app g ui) with 
                  | Some v => le vi v 
                  | None => false
                  end) f.

(* strict less than (still decidable) *)
Definition lt u v := le u v && ~~(le v u).

(* decidable equality *)
Definition eqb (u v:elt) := le u v && le v u.
Definition eqb_fun f g := le_fun f g && le_fun g f.

(* inductive version of app *)
Fixpoint app_alt (f : list (elt * elt)) (u : elt) : option elt := 
  match f with
  | nil => Some bot
  | ((ui,vi) :: tail) => 
      let appt := app_alt tail u in 
      if compatible ui u && (le ui u) then
        match appt with 
        | Some t => lub vi t | None => None end else appt
  end.

Lemma app_spec : app = app_alt.
Proof.
  ext.
  induction x.
  - ext. cbn. auto.
  - ext. 
    destruct a as [ui vi].
    cbn.
    destruct (compatible ui x0 && le ui x0) eqn:LE.
    + rewrite <- IHx. 
      reflexivity.
    + rewrite <- IHx.
      unfold basics.option_bind. 
      replace (lub bot) with (Some (A:=elt)). 
      2: { ext. reflexivity. } 
      rewrite option_eta.
      reflexivity.
Qed. 

Lemma app_nil_eq : forall f, app nil f = Some bot.
reflexivity. Qed.


Lemma app_cons_eq : 
  forall ui vi f u, app (cons (ui,vi) f) u = if compatible ui u && le ui u then 
                                          match app f u with 
                                          | Some t => lub vi t
                                          | None => None
                                          end
                                        else app f u.
Proof. 
  intros. rewrite app_spec. cbn. reflexivity. Qed.

(***** EXAMPLES *******)

Definition one  := succ zero.
(* identity function, but only defined on 0 *)
Definition id0  : elt := abs ((zero,zero) :: nil).
(* identity function, only defined on 0 and 1 *)
Definition id01 : elt := abs ((zero,zero) :: (one, one) :: nil). 
(* the second has strictly more information than the first *)
Lemma le_id0_id01 : lt id0 id01.
Proof. reflexivity. Qed.

(* note we have some contravariance in our information 
   ordering.
   a function that takes the second as an argument is strictly 
   smaller than one that takes the first.
 *)
Example example_le_fun : 
  lt (abs ((id01,zero) :: nil)) (abs ((id0, zero) :: nil)).
Proof. reflexivity. Qed.


(* the mapping id01->0 is redundant because it is subsumed by 
   id0->0. *)
Example example_redundant : 
  eqb (abs ((id01,zero) :: (id0, zero) :: nil)) 
          (abs ((id0, zero) :: nil)).
Proof. reflexivity. Qed.


(* identity function, only defined on 0 and U0. 
   NOTE: This element is semantically ill-typed. *)
Definition id_0U0  : elt := 
  abs ((zero,zero) :: (tuniv,tuniv) :: nil).

(* even though it is ill-typed, we can include it as a subterm 
   of a term that equivalent to a well-typed term. *)
Example example_redundant_illtyped_typed : 
  eqb (abs ((id_0U0,zero) :: (id0, zero) :: nil)) 
          (abs ((id0, zero) :: nil)).
Proof. reflexivity. Qed.

(* Therefore, we will need to require minimal descriptions of 
   functions if we hope to make our typing relation stable under 
   equivalence. And hope that this is enough to rule out ill-typed
   examples like the one above. 
 *)



(* --------------------------------------------------------- *)
(* --------------------------------------------------------- *)

(** * Theory about rk *)

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

Lemma rk_fun_append {f g} : 
  rk_fun (f ++ g) = max (rk_fun f) (rk_fun g).
Proof.
  induction f.
  all: cbn. done.
  destruct a as [u v].
  rewrite IHf.
  lia.
Qed.

Lemma rk_lub u v w : 
  lub u v = Some w -> rk w = max (rk u) (rk v).
Proof.
  move: v w.
  induction u.
  all: intros v w.
  all: cbn.
  all: destruct v.
  all: intros h; inversion h; subst.
  all: cbn; auto.
  - destruct (lub u v) eqn:LU; cbn in h; inversion h.
    cbn. f_equal. eauto. 
  - fold rk_fun.
    destruct (lub u v) eqn:LU;
    destruct compatible_fun eqn:C; 
    inversion h.
    cbn. fold rk_fun. f_equal.
    apply IHu in LU. rewrite LU.
    rewrite rk_fun_append. 
    lia.
  - destruct compatible_fun eqn:C. 2: done.
    inversion h. cbn.
    f_equal. fold rk_fun.
    rewrite rk_fun_append. 
    reflexivity.
Qed.

Lemma rk_lub_list xs u : 
  lub_list xs = Some u -> rk u = List.list_max (List.map rk xs).
Proof.  
  move: u.
  induction xs.
  - intros u h; inversion h. subst. done.
  - cbn; intros u h. unfold lub_list_opt, lub_opt in h. 
    destruct fold_right eqn:L. 2: done.
    cbn in h. 
    apply IHxs in L. unfold List.list_max in L. rewrite <- L.
    eapply rk_lub.
    done.
Qed.    

(* 
   rk(f(u)) <= rk(f) for all u   
*)
Lemma rk_app': forall m f u w, 
       app' f u m = Some w -> rk w <= rk_fun f.
Proof.
    intros m f u w.
    unfold app'.
    intros h. rewrite (rk_lub_list h). clear h.
    induction f.
    - cbn. auto.
    - destruct a as [ui vi]. cbn.
      eapply Nat.max_le_compat.
      2: { eapply IHf. } 
      destruct (compatible ui u && le' ui u m). 
      lia. cbn. lia.
Qed.


(** * Raw Theory about compatibility *)

(* These properties are proven by strong induction on 
   rank of u and v.
*)

Lemma compatible_fun_sym' f g 
  (ih : forall (u v : elt), 
      Init.Nat.max (rk u) (rk v) <= (max (rk_fun f) (rk_fun g)) ->
      compatible u v -> compatible v u) :
  compatible_fun f g -> compatible_fun g f.
Proof.
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
Qed.

Lemma compatible_sym' : forall (k : nat) (u v : elt), 
  Init.Nat.max (rk u) (rk v) <= k ->
  compatible u v -> compatible v u.
Proof.
    elim /strong_ind.
    move=> m ih.
    move=>u v Le. 
    destruct u; destruct v; cbn in *; try done.
    all: try match goal with [ H : S _ <=  _ |- _ ] =>
        destruct (le_S_pred H) as [m0 [-> LL]] end.
    - eauto.
    - fold rk_fun in *.
      move=> /andP [h1 h2].
      apply /andP; split.
      + eapply ih; eauto. lia.
      + move: h2. eapply compatible_fun_sym'; eauto. 
        eapply ih. lia.
    - fold rk_fun in *.
      eapply compatible_fun_sym'; eauto.
Qed.

Lemma compatible_sym : forall (u v : elt), 
  compatible u v -> compatible v u.
Proof.
  intros u v.
  eapply compatible_sym'; eauto.
Qed.  

Lemma compatible_fun_sym : 
  forall f g, compatible_fun f g -> compatible_fun g f.
Proof. 
  intros f g.
  eapply compatible_fun_sym'; eauto.
  eapply compatible_sym'; eauto.
Qed.

(* NB: compatibility is not transtive because of bot *)

(* Terms are compatible iff they have a least upper bound *)
Lemma compatible_lub_exists u v : 
  compatible u v -> { w & lub u v = Some w }.
Proof.
  move: v.
  induction u.
  all: destruct v; cbn.
  all: intro h; try done.
  all: try solve [eexists; eauto].
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

Lemma lub_compatible u v w : 
  lub u v = Some w -> compatible u v.
Proof.
  move: v w.
  induction u.
  all: intros v w h.
  all: destruct v; try done.
  all: cbn in h.
  - destruct (lub u v) eqn:h1; try done.
    cbn. cbn in h. eauto.
  - cbn. destruct (compatible_fun l l0) eqn:h1; try done.
    destruct (lub u v) eqn:h2; try done.
    erewrite IHu; eauto. 
  - cbn.
    destruct (compatible_fun l l0) eqn:h1; try done.
Qed.

(*
Lemma lub_None_not_compatible u v : 
  lub u v = None -> ~~ (compatible u v).
Proof.
  move=> LUB. apply /negP. move=> COM.
  destruct (compatible_lub_exists COM) as [w EQ].
  rewrite LUB in EQ. done.
Qed.

Lemma not_compatible_lub_None u v : 
  ~~ (compatible u v) -> lub u v = None.
Proof.
  move: v.
  induction u.
  all: intros v h.
  all: destruct v; try done.
  - destruct (n =? n0) eqn:h1.
    cbn in h. rewrite h1 in h. done.
    cbn in h. cbn. rewrite h1. done.
  - destruct (lub u v) eqn:h1; cbn in h.
    apply IHu in h. rewrite h in h1. done.
    apply IHu in h. cbn. rewrite h1. done.
  - cbn. destruct (compatible_fun l l0) eqn:h1; try done.
    destruct (lub u v) eqn:h2; try done.
    cbn in h. rewrite negb_and in h. 
    move: h => /orP [h|h].
    + apply IHu in h. rewrite h2 in h. done.
    + fold (compatible_fun l l0) in h.
      rewrite h1 in h. done.
  - cbn.
    destruct (compatible_fun l l0) eqn:h1; try done.
    cbn in h.
    fold (compatible_fun l l0) in h.
    rewrite h1 in h. done.
Qed.
*)

Lemma compatible_cons_def u v l l0 :
  compatible_fun ((u, v) :: l) l0 = 
  coherent_with l0 (u,v) && compatible_fun l l0 .
Proof. 
  cbn. f_equal.
Qed.


(*
Lemma compatible_cons u v f g :
  (forall uj vj, In (uj,vj) g -> compatible u uj -> compatible v vj) ->
  compatible_fun f g ->
  compatible_fun ((u,v)::f) g.
Proof.
  intros h1 h2.
  rewrite compatible_cons_def.
  apply /andP.
  split; auto.
  apply /forallb_forall. 
  intros x Ing. destruct x. specialize (h1 _ _ Ing).
  apply /implyP.
  done.
Qed. *)

Lemma compatible_append : forall h g f, 
      compatible_fun h f -> 
      compatible_fun h g -> 
      compatible_fun h (f ++ g).
Proof.
  induction h; intros g f.
  - cbn. auto.
  - destruct a as [u v]. cbn.
    move=> /andP [h1 h2].
    move: h1 => /forallb_forall h1.
    move: h2 => /forallb_forall h2.
    move=> /andP [/forallb_forall h3 /forallb_forall h4].
    apply /andP. split.
    -- apply /forallb_forall.
       move=> x Inx. 
       destruct (in_app_or _ _ _ Inx) as [h5|h5].
    + apply h1. done.
    + eauto.
    -- apply /forallb_forall.
       move=> [ui vi] Inh.
       rewrite forallb_app.
       apply /andP. split. 
       eapply (h2 _ Inh).
       eapply (h4 _ Inh).
Qed.


(* comp_Sup *)
Lemma lub_compatible_trans u v w x: 
  lub u v = Some w -> 
  compatible x u -> 
  compatible x v -> 
  compatible x w.
Proof.
  move: v w x.
  induction u.
  all: move => v w x.
  all: destruct v; move=>h; inversion h; subst; try done.
  - destruct (lub u v) eqn:h1; try done.
    cbn in H0. inversion H0. subst.
    destruct x; try done. cbn.
    eauto.
  - cbn in h. destruct x; try done. destruct w; done. 
    destruct (compatible_fun l l0) eqn:h1. 2: done.
    destruct (lub u v) eqn:h2. 2: done.
    cbn in h. inversion h. subst.
    cbn.
    move=> /andP [hu hl].
    move=> /andP [hv hl0].
    apply /andP. split.
    eauto.
    fold (compatible_fun l1 l) in hl.
    fold (compatible_fun l1 l0) in hl0.
    eapply compatible_append; eauto.
  - cbn in h. destruct x; try done. destruct w; done. 
    destruct (compatible_fun l l0) eqn:h1. 2: done.
    cbn in h. inversion h. subst.
    cbn.
    eapply compatible_append; eauto.
Qed.


Lemma compatible_append_assoc: forall l l0 l1,
        compatible_fun l l0 -> 
        compatible_fun l0 l1 ->
        compatible_fun l (l0 ++ l1) = compatible_fun (l ++ l0) l1.
Proof.
  induction l; intros l0 l1 h1 h2.
  rewrite app_nil_l. rewrite h2. done.
  destruct a as [u v].
  cbn.
  fold (compatible_fun l (l0 ++ l1)).
  fold (compatible_fun (l ++ l0) l1).
  rewrite compatible_cons_def in h1.
  move: h1 => /andP [h1 h3]. 
  rewrite IHl; auto.
  f_equal.
  induction l0. cbn. done.
  destruct a as [uk vk].
  rewrite compatible_cons_def in h2.
  move: h2 => /andP [h2 h4].
  apply compatible_fun_sym in h3. 
  rewrite compatible_cons_def in h3.
  move: h3 => /andP [h3 h5].
  cbn in h1.
  move: h1 => /andP [h1 h1'].
  apply compatible_fun_sym in h5.
  specialize (IHl0 ltac:(eauto) ltac:(eauto) ltac:(eauto)).
  cbn.
  rewrite IHl0.
  rewrite h1. cbn.
  done.
Qed.

Lemma lub_opt_idL o : lub_opt (Some bot) o = o.
cbn. destruct o; done.
Qed.

Lemma lub_bot_l e : lub bot e = Some e.
reflexivity.
Qed.

Lemma lub_bot_r e : lub e bot = Some e.
destruct e; reflexivity.
Qed.

(* Sup-assoc *)
Lemma lub_assoc u v w w1 w2 : 
  lub u v = Some w1 -> 
  lub v w = Some w2 ->
  lub w1 w = lub u w2.
Proof.
  move: v w w1 w2.
  induction u.
  all: move=> e0 e1 w w1 h h1.
  all: destruct e0; cbn in *.
  all: destruct e1; cbn in *.
  all: inversion h; subst.
  all: inversion h1; subst.
  all: cbn; try done.
  + destruct (lub u e0) as [w0|]; try done. inversion h. subst. clear h.
      cbn. done.
    + destruct (lub u e0) as [w0|] eqn:L0; try done. inversion h. subst. clear h.
      destruct (lub e0 e1) as [w2|] eqn:L1; try done. inversion h1. subst. clear h1.
      clear H0 H1.
      move: (IHu _ _ _ _ L0 L1) => h2. 
      cbn. rewrite h2. done.
    + destruct (compatible_fun l l0) eqn:C; try done.
      destruct (lub u e0) eqn:E; try done. cbn in h. inversion h. cbn. done.
    + destruct (compatible_fun l l0) eqn:C1; try done.
      destruct (compatible_fun l0 l1) eqn:C2; try done.
      destruct (lub u e0) eqn:E; try done.
      destruct (lub e0 e1) eqn:E1; try done.
      cbn in h1. cbn in H1.
      inversion H0. subst. inversion H1. subst.
      rewrite compatible_append_assoc; eauto.
      cbn. rewrite app_assoc.
      destruct (compatible_fun (l ++ l0)); try done.
      move: (IHu _ _ _ _ E E1) => h3. rewrite h3.
      done.
    + (* abs *)
      destruct (compatible_fun l l0) eqn:C; try done.
      inversion h. cbn. done.
    + (* abs *)
      destruct (compatible_fun l l0) eqn:C1; try done.
      destruct (compatible_fun l0 l1) eqn:C2; try done.
      inversion H0. subst. inversion H1. subst.
      rewrite compatible_append_assoc; eauto.
      cbn. rewrite app_assoc. done.
Qed.


(* If coherent_with g x = false, then coherent_with (g++h) x = false.
   Follows because coherent_with (g++h) x = coherent_with g x && coherent_with h x. *)
Lemma coherent_with_app_l (x : elt * elt) g h :
  coherent_with g x = false ->
  coherent_with (g ++ h) x = false.
Proof.
  destruct x as [u v]. unfold coherent_with.
  rewrite forallb_app. move=> ->. done.
Qed.

(* If compatible_fun g f = false, then compatible_fun (h++g) f = false.
   Follows because compatible_fun (h++g) f = compatible_fun h f && compatible_fun g f. *)
Lemma compatible_fun_app_r (h g f : list (elt * elt)) :
  compatible_fun g f = false ->
  compatible_fun (h ++ g) f = false.
Proof.
  unfold compatible_fun. rewrite forallb_app.
  move=> h1.
  apply /andP. move=> [h2 h3].
  rewrite h1 in h3.
  done.
Qed.

(* If compatible_fun f g = false, then compatible_fun f (g++h) = false.
   Follows because coherent_with (g++h) x = coherent_with g x && ..., so if
   some entry of f fails coherent_with g, it also fails coherent_with (g++h). *)
Lemma compatible_fun_app_l (f g h : list (elt * elt)) :
  compatible_fun f g = false ->
  compatible_fun f (g ++ h) = false.
Proof.
  induction f as [| [u v] f IHf].
  - done.
  - unfold compatible_fun. cbn.
    move=> Hf.
    fold (compatible_fun f (g ++ h)).
    apply /andP. move=> [h1 h2].
    rewrite Bool.andb_false_iff in Hf.
    fold (coherent_with (g ++ h) (u, v)) in h1.
    fold (coherent_with g (u, v)) in Hf.
    fold (compatible_fun f g) in Hf.
    destruct Hf. 
    + move: (coherent_with_app_l h H) => h3.
      rewrite h1 in h3. done.
    + apply IHf in H. rewrite h2 in H. done.
Qed.

Lemma lub_assoc_None_r v : forall e w1 w2,
  lub v e = Some w1 ->
  lub e w2 = None ->
  lub w1 w2 = None.
Proof.  
  induction v.
  all: move=> e w1 w2 L1 L2.
  all: destruct e; cbn in *; inversion L1; subst.
  all: inversion L2; subst.
  all: try solve [destruct w2; try done].
  - (* succ *)
    destruct (lub v e) eqn:LUB; try done.
    destruct w2 eqn:h2.
    all: try solve [subst; cbn in *; inversion L1; cbn; done].
    (* only succ case remains *)
    cbn in *. inversion L1; subst; clear L1. clear H0.
    cbn. f_equal.
    destruct (lub e e1) eqn:E1. done.
    eapply IHv; eauto.
  - (* tpi *)
    destruct (compatible_fun l l0) eqn:h1. 2: done.
    destruct (lub v e) eqn:h2; try done.
    inversion L1; subst. clear L1 H0.
    destruct w2 eqn:h3.
    all: try solve [cbn in *; done].
    cbn in *.
    destruct (compatible_fun l0 l1) eqn:h4.
    + destruct (compatible_fun (l ++ l0) l1) eqn:h5.
      destruct (lub e e1) eqn:h6. inversion L2.
      erewrite IHv; eauto. rewrite L2. done.
    + destruct (compatible_fun (l ++ l0) l1) eqn:h5. 2: done.
      move: (compatible_fun_app_r l h4) => h6. rewrite h6 in h5. done.
  - (* tabs *)
    destruct (compatible_fun l l0) eqn:h1. 2: done.
    destruct w2 eqn:h2.
    all: inversion L2; clear L2.
    all: inversion L1; cbn; try done.
    subst; clear L1 H0.
    destruct (compatible_fun l0 l1) eqn:h2. done. clear H1 H2.
    destruct (compatible_fun (l ++ l0) l1) eqn:h3. 2: done.
    move: (compatible_fun_app_r l h2) => h4. rewrite h3 in h4. done.
Qed.


Lemma lub_assoc_None_l v : forall e w1 w2,
  lub v e = Some w2 ->
  lub w1 v = None ->
  lub w1 w2 = None.
Proof.
  induction v.
  all: move=> e w1 w2 L1 L2.
  all: destruct e; cbn in *; inversion L1; subst.
  all: inversion L2; subst.
  all: try solve [destruct w1; try done].
  - (* succ *)
    destruct (lub v e) eqn:LUB; try done.
    destruct w1 eqn:h2.
    all: try solve [subst; cbn in *; inversion L1; cbn; done].
    cbn in *. inversion L1; subst; clear L1. clear H0.
    cbn. f_equal.
    destruct (lub e1 v) eqn:E1. done.
    eapply IHv; eauto.
  - (* tpi *)
    destruct (compatible_fun l l0) eqn:h1. 2: done.
    destruct (lub v e) eqn:h2; try done.
    inversion L1; subst. clear L1 H0.
    destruct w1 eqn:h3.
    all: try solve [cbn in *; done].
    cbn in *.
    destruct (compatible_fun l1 l) eqn:h4.
    + destruct (compatible_fun l1 (l ++ l0)) eqn:h5.
      destruct (lub e1 v) eqn:h6. inversion L2.
      erewrite IHv; eauto. rewrite L2. done.
    + destruct (compatible_fun l1 (l ++ l0)) eqn:h5. 2: done.
      move: (@compatible_fun_app_l l1 l l0 h4) => h6. rewrite h6 in h5. done.
  - (* tabs *)
    destruct (compatible_fun l l0) eqn:h1. 2: done.
    destruct w1 eqn:h2.
    all: inversion L2; clear L2.
    all: inversion L1; cbn; try done.
    subst; clear L1 H0.
    destruct (compatible_fun l1 l) eqn:h2. done. clear H1 H2.
    destruct (compatible_fun l1 (l ++ l0)) eqn:h3. 2: done.
    move: (@compatible_fun_app_l l1 l l0 h2) => h4. rewrite h3 in h4. done.
Qed.

Lemma lub_opt_assoc u v w :
  lub_opt (lub_opt u v) w = lub_opt u (lub_opt v w).
Proof.
  destruct u; destruct v; destruct w; cbn; try done.
  all: destruct (lub e e0) as [xy|] eqn:h; cbn; try done.
  all: destruct (lub e0 e1) as [yz|] eqn:h1; cbn; try done.
  - (* all lubs are defined: lub xy e1 = lub e yz *)
    eapply lub_assoc; eauto.
  - (* lub e e0 = Some xy, lub e0 e1 = None: need lub xy e1 = None *)
    eapply lub_assoc_None_r; eauto.
  - symmetry. eapply lub_assoc_None_l; eauto. 
Qed.
      

Lemma lub_list_app l1 l2 o1 o2 : 
  lub_list l1 = o1 ->
  lub_list l2 = o2 ->
  lub_list (l1 ++ l2) = lub_opt o1 o2.
Proof.
unfold lub_list. rewrite map_app.
unfold lub_list_opt.
rewrite fold_right_app. move=> y. eapply lub_opt_idL. intros. rewrite lub_opt_assoc. done.
move=> h1 h2.
rewrite h1. rewrite h2.
done.
Qed.

(* -------------------------------------- *)

(*
(* all pairs of elements in l are compatible *)
Definition pairwise_compatible (l : list elt) : bool :=
  forallb (fun x => forallb (fun y => compatible x y) l) l.
*)


(*
Lemma list_lub_compatible_trans l x w: 
  lub_list l = Some w -> (forallb (compatible x) l) -> compatible x w.
Proof.
  move:w.
  induction l.
  - move=> w h. inversion h. subst.
    destruct x; try done.
  - move=> w h.
    cbn in h. cbn. 
    fold (lub_list l) in h.
    move=> /andP [h1 h2].
    destruct (lub_list l) eqn:h3. 2: done.
    specialize (IHl _ ltac:(eauto) h2).
    cbn in h.
    eapply lub_compatible_trans; eauto.
Qed.


(* if that is the case, then the lub exists *)
Lemma pairwise_lub_exists l : 
  pairwise_compatible l -> 
  { w | lub_list l = Some w }.
Proof.
  induction l.
  - cbn. move=> h. eauto.
  - cbn.
    move=> /andP [/andP [_ h1] /forallb_forall h2]. 
    destruct IHl as [w0 EQ].
    apply /forallb_forall. move=> x xIn. specialize (h2 x xIn).
    move: h2 => /andP [h2 h3]. done. 
    unfold lub_list in EQ. rewrite EQ. fold (lub_list l) in EQ.
    cbn. 
    move: (list_lub_compatible_trans EQ h1) => h3. 
    destruct (compatible_lub_exists h3) as [w h4].
    exists w. eauto. 
Qed.
*)

(* --------------------------------------------------------- *)

(** * Raw Theory about le (totality, reduction) *)

Local Lemma rk_le_enough : forall k u v,
  max (rk u) (rk v) <= k -> 
  le' u v (max (rk u) (rk v)) = (le' u v k).
Proof.
  elim /strong_ind.
  move=> m ih u v Le.
  destruct m.
  - destruct u; destruct v; cbn in *; auto.
    all: try lia.
  - have LEM1:
      forall g ui r, r <= m -> (max (rk_fun g) (rk ui)) <= r ->
                app' g ui r = app' g ui m.
      { subst. 
        move=> g ui r Le1 Le2.
        unfold app'.
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
        destruct app' eqn:EA; try done.
        move: (rk_app' EA) => Le3.
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


Local Lemma rk_app_enough :
      forall r g ui, 
        (max (rk_fun g) (rk ui)) <= r ->
        app' g ui r = app' g ui (max (rk_fun g) (rk ui)).
  move=> r g ui Le1.
  unfold app'.
  f_equal.
  eapply map_ext_in.
  move=> [uj vj] Ing.
  move: (In_rk_fun1 Ing) => h1.
  move: (In_rk_fun2 Ing) => h2.
  rewrite <- rk_le_enough; try lia.
  rewrite <- (rk_le_enough (k := Init.Nat.max (rk_fun g) (rk ui))); try lia.
  reflexivity.
Qed.

Local Lemma rk_fun_enough : 
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
  rewrite (rk_app_enough (r:=Init.Nat.max (rk_fun f) (rk_fun g))); 
    try lia.
  destruct app' eqn:EA; try done.
  move: (rk_app' EA) => Le3.
  rewrite <- rk_le_enough; try lia.
  rewrite <- (rk_le_enough (k:=Init.Nat.max (rk_fun f) (rk_fun g))); try lia.
  auto.
Qed. 


Lemma app'_app :
  forall r g ui, (max (rk_fun g) (rk ui)) <= r -> 
            app' g ui r = app g ui.
Proof.
  intros.
  unfold app.
  unfold app'.
  f_equal.
  eapply map_ext_in.
  move=> [uj vj] Ing.
  move: (In_rk_fun1 Ing) => h1.
  move: (In_rk_fun2 Ing) => h2.
  unfold le.
  rewrite <- rk_le_enough; try lia.
  done.
Qed.

Lemma rk_app : forall f u w, 
       app f u = Some w -> rk w <= rk_fun f.
Proof.
  intros.
  rewrite <- (app'_app ltac:(reflexivity)) in H.
  eapply rk_app'. eauto.
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
  rewrite <- (app'_app (r := r)); try lia.
  destruct app' eqn:Ev; try done.
  move: (rk_app' Ev) => h3.
  unfold le.
  rewrite <- rk_le_enough; try lia. 
  done.
Qed.



Lemma le_bot v : le bot v.
 destruct v; reflexivity.
Qed.

Lemma le_bot' v m : le' bot v m.
 destruct v; destruct m; reflexivity.
Qed.

Lemma le_tuniv : le tuniv tuniv = true.
  reflexivity.
Qed.

Lemma le_succ u v : le (succ u) (succ v) = le u v.
Proof.
  reflexivity.
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
  rewrite <- rk_le_enough. done. lia.
  erewrite <- (le_fun'_le_fun (r:=r)). 2: lia.
  reflexivity.
Qed.

Lemma le_abs f g : le (abs f) (abs g) = le_fun f g.
  unfold le. cbn. fold rk_fun.
  remember (max (rk_fun f) (rk_fun g)) as r.
  rewrite <- (le_fun'_le_fun (r:=r)). 2: lia.
  reflexivity.
Qed.  

Lemma le_fun'_cons ui vi f g m : 
  le_fun' ((ui, vi) :: f) g m = 
     (match app' g ui m with 
      | Some v => le' vi v m
      | None => false
      end) && le_fun' f g m.                 
Proof.
  cbn. f_equal.
Qed.

Lemma le_fun_nil l :
  le_fun nil l.
Proof. reflexivity. Qed.

Lemma le_fun_cons u1 v1 l1 l2 : 
 le_fun ((u1, v1) :: l1) l2 = 
   (match (app l2 u1) with 
    | Some w => le v1 w && le_fun l1 l2 
    | None => false
    end).
Proof.
  cbn.
  destruct (app l2 u1) eqn: h. 2: reflexivity.
  f_equal.
Qed.

Lemma le_fun_extend g h f : 
    le_fun g f ->
    le_fun h f ->
    compatible_fun g h ->
    le_fun (g ++ h) f.
Proof.
 induction g as [|[u v]g].
 all: move=> Lg Lh Cgh.
 - done.
 - cbn in Lg. cbn.
   destruct (app f u) eqn:h1. 2: done.
   move: Lg => /andP [h2 h3]. rewrite h2. cbn.
   rewrite forallb_app.
   rewrite h3. cbn.
      eapply Lh.
Qed.


Create HintDb le.
Hint Rewrite le_bot le_tuniv le_succ le_tpi le_abs le_fun_nil le_fun_cons : le.

(* --------------------------------------------------------- *)
(** * Validity *)
(* --------------------------------------------------------- *)


(* We want finite functions to *not* include bot.

   A valid finite function is 

   - compatible with itself. 
     i.e. all compatible args produce compatible results

   - does not include bot as a result

   - is not an empty list

   - includes only valid args and results

   A term is valid when all of its subterms are valid, including
   functions.

  valid -> Coherent
*)

Definition no_bot_result (f : list (elt * elt)) := 
  List.forallb (fun p => ~~ (le (snd p) bot)) f.

Definition is_nil {A} (f : list A) := 
  match f with | nil => true | _ => false end.

Fixpoint valid u : bool :=
  let valid_fun f :=
    (compatible_fun f f) &&
    (no_bot_result f) &&
    (List.forallb (fun '(ui,vi) =>
                     (valid ui) && (valid vi)) f)
  in
  match u with
  | abs f => valid_fun f && ~~ is_nil f
  | tpi a f => valid a && (valid_fun f)
  | succ v => valid v
  | _ => true
  end.

Definition valid_fun f :=
    (compatible_fun f f) &&
    (no_bot_result f) &&
    (List.forallb (fun '(ui,vi) => (valid ui) && (valid vi)) f).


(* if a non-nil function is valid, and the tail is non-nil,
   then it is valid. *)

Lemma valid_fun_tail u v f :
  valid_fun ((u,v) :: f) ->
  valid_fun f.
Proof.
  move=> /andP [/andP [h1 h2] h3].
  rewrite compatible_cons_def in h1.
  cbn in *.
  move: h1 => /andP [/andP [h1 h9] h5].
  move: h2 => /andP [h2 h8].
  move: h3 => /andP [h3 h6].
  apply /andP; split; auto.
  apply /andP; split; auto.
  unfold compatible_fun in *.
  apply forallb_forall.
  move: h5 => /forallb_forall h5.
  move=> [ui vi] Inf. specialize (h5 _ Inf). cbn in h5.
  move: h5 => /andP [_ h5]. done.
Qed.

Record CFT u v f : Prop :=
  mkCFT { key_valid  : valid u;
          val_valid  : valid v;
          val_nbot   : ~~ le v bot;
          compat     : coherent_with f (u,v)
    }.

Lemma valid_fun_head u v f :
   valid_fun ((u,v) :: f) -> CFT u v f.
Proof.
  move=> /andP [/andP [h1 h2] h3].
  rewrite compatible_cons_def in h1.
  cbn in *.
  move: h1 => /andP [/andP [h1 h9] h5].
  move: h2 => /andP [h2 h8].
  move: h3 => /andP [/andP [h3 h7] h6].
  constructor; eauto.
Qed.

Lemma valid_fun_compatible f :
  valid_fun f -> compatible_fun f f.
Proof.  move=> /andP [/andP [h1 h2] h3]. auto. Qed.

Lemma valid_fun_no_bot f :
  valid_fun f -> no_bot_result f.
Proof.  move=> /andP [/andP [h1 h2] h3]. auto. Qed.

(* Under the new definition of [valid], non-emptiness is part of
   [valid (abs f)] but not of [valid_fun f]. The non-emptiness lemma
   for [abs] takes [valid (abs f)] directly. *)

Lemma valid_abs_nonnil f :
  valid (abs f) -> ~~ is_nil f.
Proof. cbn. move=> /andP [_ h]. exact h. Qed.

Lemma valid_fun_subterms f :
  valid_fun f ->
  forallb (fun '(ui,vi) => valid ui && valid vi) f.
Proof.
  move=> /andP [_ h3]. done.
Qed.

Lemma valid_fun_subterms_prop f:
  valid_fun f ->
  forall ui vi, In (ui,vi) f -> (valid ui) /\ (valid vi).
Proof. move => /valid_fun_subterms h3.
       move: h3 => /forallb_forall h3.
       move=> ui vi Inf.
       specialize (h3 _ Inf). cbn in h3.
       move: h3 => /andP [h3 h5].
       auto.
Qed.


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


Create HintDb valid.
Hint Resolve
  valid_fun_head valid_fun_tail key_valid val_valid compat
  valid_fun_compatible valid_fun_no_bot valid_abs_nonnil valid_fun_subterms : valid.


(* Lemmas about valid terms *)

(* Compatibility is (only) reflexive for valid terms. *)
Lemma compatible_refl u : valid u -> compatible u u.
Proof.
  induction u.
  all: cbn.
  all: auto.
  - move=> /andP [Vu Vf].
    apply /andP. split; eauto using valid.
    eapply valid_fun_compatible; eauto.
  - move=> /andP [Vf _].
    eapply valid_fun_compatible; eauto.
Qed.


Lemma no_bot_result_app : forall f g, no_bot_result f ->
                   no_bot_result g ->
                   no_bot_result (f ++ g).
Proof. intros f g Nf Ng.
      unfold no_bot_result in *.
      rewrite forallb_app.
      apply /andP. done.
Qed.

Lemma app_append f g u o1 o2: 
  app f u = o1 -> app g u = o2 -> 
  app (f ++ g) u = lub_opt o1 o2.
Proof.
  move=>h1. move=> h2.
  unfold app in *.
  rewrite map_app.
  erewrite lub_list_app; eauto. 
Qed.

(* We can append compatible functions together *)
Definition valid_append f g : 
    valid_fun f 
  -> valid_fun g 
  -> compatible_fun f g 
  -> valid_fun (f ++ g).
Proof.
  move=> /andP [/andP [Cf Nbf] Vf]
        /andP [/andP [Cg Nbg] Vg] Cfg.
  apply /andP; split. apply /andP; split.
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
      move: Cfg => /implyP Cfg.
      apply /implyP. move=> x.
      apply compatible_sym. apply Cfg.
      apply compatible_sym. auto.
    + eapply (Cgi _ Igj).
  - apply no_bot_result_app; auto.
  - clear Cf Cg Cfg.
    induction f; cbn in *. done.
    destruct a as [u v].
    move: Vf => /andP [h1 h2].
    apply /andP. split. done.
    rewrite forallb_app.
    apply /andP; split; auto.
Qed.

(* The lub of valid elements is valid *)
Lemma valid_lub u v w : valid u -> valid v -> 
                        lub u v = Some w -> valid w.
Proof.
  move: v w.
  induction u.
  all: intros v w Vu Vw h.
  all: destruct v; cbn in h, Vu, Vw; inversion h; subst; try done.
  - destruct (lub u v) eqn:EQ; inversion h. cbn.
    eapply IHu; eauto.
  - move: Vu => /andP [Vu Vfl].
    move: Vw => /andP [Vw Vfl0].
    destruct (compatible_fun l l0) eqn:Co. 2: done.
    destruct (lub u v) eqn:LUB. 2: done.
    inversion h. cbn. clear h H0.
    apply /andP. split; eauto.
    eapply valid_append; eauto.

  - destruct (compatible_fun l l0) eqn:Co. 2: done.
    move: Vu => /andP [Vu Nu]. move: Vw => /andP [Vw Nw].
    inversion h. cbn.
    apply /andP. split.
    eapply valid_append; eauto.
    destruct l; cbn in *; done.
Qed.


Lemma valid_lub_list f : forall u e, 
  (List.forallb (fun '(ui,vi) => (valid ui) && (valid vi)) f) -> valid u ->
  lub_list_opt (map Some (map (fun '(ui, vi) => if compatible ui u && le ui u then vi else bot) f)) =
    Some e -> 
  valid e.
Proof.
  induction f as [|[ui vi]f].
  all: cbn; move=> u e Vf Vu LL.
  - inversion LL. done.
  - move: Vf => /andP [/andP [Vui Vvi] Vf].
    destruct lub_list_opt eqn: h2. 2: done.
    specialize (IHf _ _ Vf Vu h2).
    destruct (compatible ui u && le ui u) eqn: h3.
    ++ eapply valid_lub in LL; eauto.
    ++ cbn in LL. inversion LL. subst. clear LL. done.
Qed.

Lemma valid_app f u w : valid_fun f -> valid u -> app f u = Some w -> valid w.
Proof.
  move: u w.
  induction f as [|[ui vi]f].
  all: cbn; move=> u w Vf Vu App.
  - inversion App; done.
  - destruct lub_list_opt eqn:h1. 2: done.
    have Ve: valid e. 
    { destruct (~~ is_nil f) eqn:h3.
      + eapply valid_lub_list in h1; eauto with valid.
      + destruct f; try done. cbn in h1. inversion h1. done.
    }
    destruct (compatible ui u && le ui u) eqn:h2.
    + apply valid_lub in App; eauto with valid.
    + cbn in App. inversion App; subst; eauto.
Qed.

Hint Resolve valid_app valid_lub : valid.

(* ------------------------------------------------------- *)

(** * Inversion lemmas for le *)

Lemma le_bot_inv : forall u, le u bot -> u = bot.
Proof.
  induction u.
  all: move=> LE1.
  all: cbn in LE1; try done.
Qed.

Lemma le_tnat_inv : forall u, le tnat u -> u = tnat.
  induction u.
  all: move=> LE1.
  all: cbn in LE1; try done.
Qed.


Lemma le_zero_inv : forall u, le zero u -> u = zero.
  induction u.
  all: move=> LE1.
  all: cbn in LE1; try done.
Qed.

Lemma le_tuniv_inv : forall u, le tuniv u -> u = tuniv.
  induction u.
  all: move=> LE1.
  all: cbn in LE1; try done.
Qed.

Lemma le_succ_inv : forall u v, le (succ u) v -> 
                           { w & (v = succ w) * (le u w) }.
Proof.
  induction u.
  all: move=> v LE1.
  all: try solve [destruct v; cbn; try done; eexists; split; eauto]. 
Qed.

Lemma le_tpi_inv : forall v u f, 
    le (tpi u f) v -> { w & { g & (v = tpi w g) * ((le u w) * (le_fun f g)) }}.
Proof.
  destruct v.
  all: move=> u f LE.
  all: try solve [cbn in LE; try done].
  rewrite le_tpi in LE. move: LE => /andP [h1 h2].
  eexists; repeat split; eauto.
Qed.

Lemma le_abs_inv : forall v f, 
    le (abs f) v -> { g & (v = abs g) * (le_fun f g) }.
Proof.
  destruct v.
  all: move=> f LE.
  all: try solve [cbn in LE; try done].
  rewrite le_abs in LE. 
  eexists; repeat split; eauto.
Qed.

(* ------------------------------------------------------- *)


Lemma le_fun_tail ui vi f g :
  le_fun ((ui,vi) :: f) g -> le_fun f g.
Proof.
  move=> /forallb_forall h.
  unfold le_fun.
  apply forallb_forall.
  move=> [uj vj] Inf.
  move: (h (uj,vj) ltac:(right; eauto)) => h1.
  done.
Qed.

Lemma le_fun_app_bot f u : 
  le_fun f nil -> (app f u) = Some bot.
Proof.
  induction f as [|[ui vi] f]. cbn. done.
  move=> h1.
  move: (le_fun_tail h1) => h3.
  move: h1 => /andP [h1 _].
  cbn.
  cbn in h1.
  apply le_bot_inv in h1. subst.
  apply IHf in h3.
  unfold app in h3.
  unfold lub_list in h3.
  cbn.
  rewrite h3.
  destruct (compatible ui u && le ui u); done. 
Qed.

Lemma le_fun_nil_compatible f g : 
  le_fun f nil -> compatible_fun f g.
Proof.
  induction f as [|[ui vi] f].
  intro h. done.
  move=> h. 
  move: (le_fun_tail h) => h1.
  move: h => /andP [h _].
  rewrite le_fun_app_bot in h. done.
  apply IHf in h1.
  apply /andP. split. 2: eapply h1.
  apply le_bot_inv in h. subst.
  apply forallb_forall.
  intros [uj vj] Ing.
  apply /implyP. intro h2.
  destruct vj; done.
Qed.

Hint Rewrite le_fun_nil_compatible : le.

(* comp-sup-sym *)
Lemma compatible_lub a b v w : 
  compatible a v -> compatible b v -> 
  lub a b = Some w -> compatible w v.
Proof.
  move => h1 h2 LUB.
  eapply compatible_sym.
  eapply lub_compatible_trans; eauto.
  eapply compatible_sym; auto.
  eapply compatible_sym; auto.
Qed.

  
(*
------------------------------------------------------------------------
-- Part 7f: Comp-down — downward closure of compatibility
--
-- LeCode u u' -> Comp u' v -> Comp u v
*)


Lemma comp_down : 
  forall u u' v, le u u' -> compatible u' v -> compatible u v.
Proof. 
  have LEMMA:
    forall k u u' v, max (rk u) (rk u') <= k -> 
                le u u' -> compatible u' v -> compatible u v.
  { 
    elim /strong_ind.
    move=> m ih.
    have LEMMA0 :
      (*
      EvalFun-guarded-comp : 
        (h : FinFun) (xi : FinEl) (t : Pair FinEl FinEl) ->
        CompFun h (cons t nil) -> Comp xi (fst t) ->
        Comp (EvalFun h xi) (snd t) *)
      forall h xi u w v, 
        (max (rk xi) (rk_fun h) < m)%nat ->
        coherent_with h (u,v) -> 
        compatible xi u -> 
        app h xi = Some w ->
        compatible w v.
    {
      induction h as [|[ui vi] h].
      all: move=> xi u w v RK CH CU APP.
      - cbn in *. inversion APP. subst. cbn. destruct v; done.
      - cbn in CH. move: CH => /andP [h1 h2].
        rewrite app_spec in APP. cbn in APP.
        destruct (compatible ui xi && le ui xi) eqn:LE.
        + destruct app_alt eqn:A; try done. 
          rewrite <- app_spec in A.
          cbn in RK.
          specialize (ih _ RK).
          move: LE => /andP [CC LE].
          (* use comp_down with ui xi and u *)
          move: (ih ui xi u ltac:(lia) LE CU) => h3.
          (* IH for the list *)
          specialize (IHh xi u e v ltac:(lia) h2 CU A).
          move: (@lub_compatible_trans vi e w v APP) => LC.
          eapply compatible_sym. eapply LC.
          move: h1 => /implyP h1. eapply h1. eapply compatible_sym. auto.
          eapply compatible_sym. auto.
        + eapply (IHh xi u w v); eauto.
          cbn in RK. lia.
          rewrite app_spec. done.
    }

    have LEMMA1 : 
      (* Transitivity: LeFunCode g h + CompFun h j -> CompFun g j *)
      (forall g h j, (max (rk_fun g) (rk_fun h) < m)%nat ->
        le_fun g h -> compatible_fun h j -> compatible_fun g j).
    { 
      move=> g.
      induction g as [|[ui vi]g]. done.
      move=> h j RK LE  CF.
      cbn in RK. 
      cbn in LE. move: LE => /andP [LE1 LE2].
      destruct (app h ui) eqn:h2; try done.

      rewrite compatible_cons_def.
      apply /andP. split.
      2: { eapply IHg; eauto. lia. }
      (* show coherent_with j (ui,vi) *)
      (*  build-CompStepFun : (s : Pair FinEl FinEl) (j h : FinFun) ->
          LeCode (snd s) (EvalFun h (fst s)) -> CompFun h j -> CompStepFun s j *)
      have build_CompStepFun: forall j,
          compatible_fun h j -> coherent_with j (ui,vi).
      {
        clear j LE2 IHg CF.
        induction j as [|[u v] j].
        move=> CF. done.
        move=> /forallb_forall CF.
        have CJ: (compatible_fun h j).
          { unfold compatible_fun.
          apply forallb_forall. move=> x Inh.
          specialize (CF _ Inh). destruct x as [uk vk]. 
          cbn in CF. 
          move: CF => /andP [h3 h4]. eapply h4. } 
        apply IHj in CJ.
        unfold coherent_with. 
        cbn. apply /andP. split. 2: auto.
        apply /implyP. move => h1.
        move: (LEMMA0 h ui u e v ltac:(lia)) => L0.
        have CH: coherent_with h (u,v).
        { unfold coherent_with. apply forallb_forall.
          move=> [uh vh] Inx. specialize (CF _ Inx).
          cbn in CF. move: CF => /andP [h3 h4].
          apply /implyP. move=> h5.
          eapply compatible_sym. move: h3 => /implyP h3.
          eapply h3. eapply compatible_sym. eauto.
        }
        specialize (L0 CH h1 h2).
        eapply ih. 3: eauto. 3: auto. 2: reflexivity. 
        move: (rk_app h2) => RK2.
        lia.
      }
      specialize (build_CompStepFun _ CF).
      unfold coherent_with in build_CompStepFun.
      move: build_CompStepFun => /forallb_forall CSF.
      apply /forallb_forall.
      move=> [uj vj] Inj. specialize (CSF _ Inj). cbn in CSF.
      auto.
    } 
 
    move=> u u' v Le.
    destruct u eqn:Eu; destruct u' eqn:Eu'.
    all: try solve [cbn in *; done].
    all: destruct v eqn:Ev; try done.
    all: try match goal with [ H : S _ <=  _ |- _ ] =>
        destruct (le_S_pred H) as [m0 [-> LL]] end.
    - rewrite le_succ. cbn in *.
      eapply ih; eauto. 
    - rewrite le_tpi.      
      move=> /andP [h1 h2].
      cbn. fold (compatible_fun l0 l1). fold (compatible_fun l l1).
      move=> /andP [h3 h4].
      cbn in Le. fold rk_fun in Le.
      apply /andP. split. 
      eapply ih; eauto. lia.
      eapply LEMMA1; eauto. lia.
    - rewrite le_abs. 
      cbn. fold (compatible_fun l0 l1). fold (compatible_fun l l1).
      cbn in Le. fold rk_fun in Le.
      eapply LEMMA1; eauto. 
  } 
  move=> u u' v. eapply LEMMA. eauto.
Qed.

(*
-- CoherentWith distributes over append
coherentWith-append : (q : Pair FinEl FinEl) (qs h : FinFun) ->
  CoherentWith q qs -> CoherentWith q h -> CoherentWith q (append qs h)
*)

Lemma coherent_with_append f p g : 
  coherent_with f p -> coherent_with g p -> coherent_with (f ++ g) p.
Proof.
  move:g.
  induction f as [|[ui vi]f].
  all: move=> g CF CG.
  all: cbn. done.
  destruct p as [u v].
  apply /andP.
  move: CF => /andP [h1 h2].
  split; eauto.
Qed.



(*
------------------------------------------------------------------------
-- Part 7h: Coherent-EvalFun
--
-- Comp-value-EvalFun: proved using LeCode-Comp and comp-Sup.

 Comp-value-EvalFun : (q : Pair FinEl FinEl) 
    (rest : FinFun) (xi : FinEl) ->
    LeCode (fst q) xi -> Coherent xi -> Coherent (snd q) ->
    CoherentWith q rest -> CompStepFun q rest ->
    Comp (snd q) (EvalFun rest xi)
*)

Lemma Comp_value_app f : forall u v xi w,
  compatible u xi ->
  coherent_with f (u,v) -> 
  app f xi = Some w ->
  compatible v w.
Proof.
  induction f as [|[ui vi] h].
  all: move=> u v xi w CC CH APP.
  - cbn in *. inversion APP. subst. cbn. destruct v; done.
  - cbn in CH. move: CH => /andP [/implyP h1 h2].
    rewrite app_spec in APP. cbn in APP. rewrite <- app_spec in APP. 
    destruct (compatible ui xi && le ui xi) eqn:LE2. 2: eapply IHh; eauto.
    destruct app eqn:A; try done. 
    specialize (IHh u v xi e CC h2 A).
    move: LE2 => /andP [CC2 LE2].
    move: (@lub_compatible_trans vi e w v APP) => LC.
    eapply LC; eauto.
    eapply h1.
    eapply compatible_sym.
    eapply (@comp_down ui xi u LE2).
    eapply compatible_sym.
    auto.
Qed.

Lemma valid_app_exists {f u} :
  valid_fun f ->
  valid u -> 
  { w & (app f u = Some w) * valid w}.
Proof.
  move: u.
  induction f as [|[ui vi]f].
  all: move=> u Vf Vu.
  - exists bot. cbn. split; auto.
  - rewrite app_spec. cbn. rewrite <- app_spec.
    destruct (~~ is_nil f) eqn:h1.
    + specialize (IHf u ltac:(eauto using valid_fun_tail) Vu).
      destruct (compatible ui u && le ui u) eqn:LE1; auto.
      move: LE1 => /andP [CC1 LE1].
      destruct IHf as [w [APP vw]].
      rewrite APP.
      have CC: (compatible vi w).
      { 
        eapply Comp_value_app in CC1; eauto.
        eapply compat. eapply valid_fun_head. eauto.
      } 
      destruct (compatible_lub_exists CC) as [w1 EQ].
      exists w1. split. done.
      eapply valid_lub in EQ; eauto.
      eauto using val_valid, valid_fun_head.
    + destruct f; try done.
      destruct (compatible ui u && le ui u) eqn:LE1.
      ++ cbn. exists vi. rewrite lub_bot_r. split. done.
         eauto using val_valid, valid_fun_head.         
      ++ cbn. exists bot. done.
Qed.

Lemma valid_app_compatible f u :
  valid_fun f -> 
  valid u -> 
  { w & (app f u = Some w) * (valid w *
         (* basically coherent_with f (u,w) *)
         (forall ui vi, In (ui,vi) f -> compatible ui u && le ui u -> compatible vi w)) }.
Proof.
  move: u.
  induction f as [|[ui vi]f].
  all: move=> u Vf Vu.
  - exists bot. cbn. split; auto.
  - rewrite app_spec. cbn. rewrite <- app_spec.
    destruct (~~ is_nil f) eqn:h1.
    + specialize (IHf u ltac:(eauto using valid_fun_tail) Vu).
      destruct IHf as [w [APP [vw CA]]].
      destruct (compatible ui u && le ui u) eqn:LE1; auto.
      ++ (* ui is compatible with u, so vi is part of w *)
         move: LE1 => /andP [CC1 LE1].
         rewrite APP.
         have CC: (compatible vi w).
         { 
           eapply Comp_value_app in CC1; eauto.
           eapply compat. eapply valid_fun_head. eauto.
         } 
         destruct (compatible_lub_exists CC) as [w1 EQ].
         exists w1. split. done.
         split.
         eapply valid_lub in EQ; eauto.
         eauto using val_valid, valid_fun_head.
         move=> uj vj [h2|h2]. 
         -- inversion h2. subst. move=> _.
            move: (@lub_compatible_trans vj w w1 vj EQ)=> h3.
            eapply h3.
            eapply compatible_refl. eapply val_valid. eapply valid_fun_head. eauto.
            eauto.
         -- specialize (CA _ _ h2). move=> h3. specialize (CA h3).
            move: h3 => /andP [h3 h7].
            move: (@lub_compatible_trans vi w w1 vj EQ)=> h4.
            eapply h4.
            move: (compat (valid_fun_head Vf)) => /forallb_forall h5.
            specialize (h5 _ h2). cbn in h5. move: h5 => /implyP h5.
            eapply compatible_sym.
            eapply h5.
            move: (@comp_down ui u) => h6. eapply h6; eauto.
            eapply compatible_sym. eauto.
            eauto.
       ++ exists w. repeat split; eauto.
          move=> uj vj [h2|h2].
          --- move=> h3. inversion h2; subst uj. subst vj. clear h2. 
              rewrite LE1 in h3. done.
          --- move=> h3. eapply CA; eauto.
     + destruct f; try done.
      destruct (compatible ui u && le ui u) eqn:LE1.
      ++ cbn. exists vi. rewrite lub_bot_r. repeat split. 
         eauto using val_valid, valid_fun_head.         
         move=> uj vj [h|h]. 2: done. inversion h. subst.
         move=> h2. eapply compatible_refl. eauto using val_valid, valid_fun_head.
      ++ cbn. exists bot. repeat split; eauto.
         move=> uj vj [h|h]. 2: done. inversion h. subst.
         move=> h2. destruct vj; done.
Qed.


(* Need to know not just that the app exists, but 
   that it is *compatible* with v. 
   Intuitively, w is the lub of several elements in f that includes v.
 *)
Lemma valid_app_cons_compatible f u v :
  le u u -> 
  valid_fun ((u,v) :: f) -> { w & (app f u = Some w) * (valid w * compatible w v )}.
Proof.
  move=> LE h.
  have Vu: valid u. eauto using key_valid, valid_fun_head.
  move: (valid_app_compatible h Vu) =>  [w [EQ [Vw h3]]].
  specialize (h3 u v ltac:(left; eauto)). 
  rewrite app_spec in EQ. cbn in EQ. rewrite <- app_spec in EQ.
  rewrite compatible_refl in EQ; eauto. cbn in EQ.
  rewrite LE in EQ.
  destruct (app f u) eqn:h2. 2: done.
  exists e. 
  split; eauto. split. 
  -- destruct (~~ is_nil f) eqn:h4.
     ++ move: (valid_fun_tail h) => h5.
        eapply (valid_app h5 Vu); eauto.
     ++ destruct f ; try done. cbn in h2. inversion h2. done.
  -- eapply compatible_sym. eapply lub_compatible; eauto.
Qed.

(*
-----------------------------------------------------------------------
-- Part 7h: Coherent-Sup and Coherent-EvalFun
------------------------------------------------------------------------

-- comp-EvalFun: evaluations of compatible functions at the same point
-- are compatible.
{-# TERMINATING #-}
mutual
  comp-EvalFun : (k h : FinFun) (xi : FinEl) ->
    CompFun k h -> CoherentFunTail k -> Coherent xi ->
    Comp (EvalFun k xi) (EvalFun h xi)
*)

Lemma compatible_app k : forall h xi w1 w2,
  compatible_fun k h -> 
  app k xi = Some w1 -> 
  app h xi = Some w2 -> compatible w1 w2.
Proof.
  induction k as [|[ui vi] k].
  all: move=> h xi w1 w2 CF A1 A2.
  - cbn in A1. inversion A1. subst. destruct w2; done.
  - cbn in CF. move: CF => /andP [h1 h2].
    rewrite app_spec in A1. cbn in A1. rewrite <- app_spec in A1.
    destruct (compatible ui xi && le ui xi) eqn:LE. 2: { eapply IHk; eauto. } 
    destruct (app k xi) eqn:A3. 2: done.
    specialize (IHk _ _ _ _ h2 A3 A2).
    apply compatible_sym in IHk. apply compatible_sym.
    move: (@lub_compatible_trans vi e w1 w2 A1) => h3.
    eapply h3; eauto.
    move: LE => /andP [CC LE].
    move: (@Comp_value_app h ui vi xi w2 CC) => h4.
    eapply compatible_sym.
    eapply h4; eauto.
Qed.

  

(* 
 EvalFun-append-eq : (k h : FinFun) (xi : FinEl) ->
    CompFun k h -> CoherentFunTail k -> Coherent xi ->
    Eq (EvalFun (append k h) xi) (Sup (EvalFun k xi) (EvalFun h xi))
*)
Lemma app_append_eq k : forall h xi, compatible_fun k h -> 
  forall w1 w2, app k xi = Some w1 -> 
           app h xi = Some w2 ->
  app (k ++ h) xi = lub w1 w2.
Proof.
  induction k as [|[u v]k].
  all: move=> h xi CF w1 w2 AP1 AP2.
  - move: (@le_fun_app_bot nil xi ltac:(done)) => h1. 
    rewrite h1 in AP1. inversion AP1. subst. clear AP1.
    rewrite app_nil_l. rewrite AP2. cbn.  eauto.
  - rewrite app_spec. cbn. rewrite <- app_spec.
    rewrite app_spec in AP1. cbn in AP1. rewrite <- app_spec in AP1.
    move: CF => /andP [h1 h2].
    destruct (compatible u xi && le u xi) eqn:LE.
    + destruct (app k xi) eqn:A3; try done.
      erewrite IHk; eauto. clear h2.
      destruct (lub e w2) eqn:L4.
      move: (lub_assoc AP1 L4) => h2. rewrite h2. done.
      move: (lub_assoc_None_r AP1 L4) => h2. rewrite h2. done.
    + erewrite IHk; eauto. 
Qed.

(* If f is valid and non-empty then f is not below nil. *)
Lemma valid_fun_not_le_fun_nil f :
  ~~ is_nil f -> valid_fun f -> not (le_fun f nil).
Proof.
  move=> Ne Vf Lfn.
  destruct f as [|[u v] f]; try done.
  move: (valid_fun_no_bot Vf) => /forallb_forall NBf.
  specialize (NBf (u,v) ltac:(left; eauto)). simpl in NBf.
  move: Lfn => /forallb_forall Lfn.
  specialize (Lfn (u,v) ltac:(left; eauto)). simpl in Lfn.
  rewrite Lfn in NBf. done.
Qed.

Lemma compatible_app_inv f g u v :
  valid_fun f -> 
  valid_fun g -> 
  valid u ->
  compatible_fun f g ->
  app (f ++ g) u = Some v -> 
  { vf & { vg &  app f u = Some vf /\ app g u = Some vg /\ lub vf vg = Some v}}.
Proof.
  move=> Vf Vg Vu Cfg APPu.
  destruct (valid_app_exists Vf Vu) as [vf [APPf Vvf]].
  destruct (valid_app_exists Vg Vu) as [vg [APPg Vvg]].
  move: (app_append_eq Cfg APPf APPg) => EQ.
  exists vf. exists vg.
  repeat split; eauto.
  rewrite APPu in EQ. done.
Qed.


(*
------------------------------------------------------------------------
-- Part 7i: Order-theoretic lemmas
--
*)

Module OTL.

(* 
*LeCode-refl : (a : FinEl) -> Coherent a -> LeCode a a
**LeFunCode-refl : (g : FinFun) -> CoherentFunTail g -> LeFunCode g g
* LeCode-Sup-left : (a b : FinEl) -> Comp a b -> Coherent a ->    Coherent b ->
    LeCode a (Sup a b)
LeCode-Sup-right : (a b : FinEl) -> Comp a b -> Coherent a -> Coherent b ->
    LeCode b (Sup a b)
* LeCode-trans : (x y z : FinEl) -> Coherent x -> Coherent y -> Coherent z ->
    LeCode x y -> LeCode y z -> LeCode x z
** LeFunCode-trans : (g h k : FinFun) ->
    CoherentFunTail g -> CoherentFunTail h -> CoherentFunTail k ->
    LeFunCode g h -> LeFunCode h k -> LeFunCode g k
LeFunCode-nil-any : (g k : FinFun) ->
    CoherentFunTail g -> CoherentFunTail k -> LeFunCode g nil -> LeFunCode g k
** EvalFun-mon : (h k : FinFun) (u : FinEl) ->
    CoherentFunTail h -> CoherentFunTail k -> Coherent u ->
    LeFunCode h k -> LeCode (EvalFun h u) (EvalFun k u)

 -- Sup is LUB: a ≤ c and b ≤ c implies Sup a b ≤ c
** LeCode-Sup-lub : (a b c : FinEl) -> LeCode a c -> LeCode b c ->
    LeCode (Sup a b) c
LeFunCode-append-combine : (g h k : FinFun) ->
    LeFunCode g k -> LeFunCode h k -> LeFunCode (append g h) k
** LeFunCode-append-left : (g h : FinFun) -> CompFun g h ->
    CoherentFunTail g -> CoherentFunTail h ->
    LeFunCode g (append g h)
LeFunCode-append-right : (g h : FinFun) -> CompFun g h ->
    CoherentFunTail g -> CoherentFunTail h ->
    LeFunCode h (append g h)
*)

Record OrderTheoreticLemmas k := MkLemmas { 
  le_refl : forall a, rk a <= k -> valid a -> le a a ;

  le_lub_left : forall a b, max (rk a) (rk b) <= k -> 
     compatible a b -> forall w, lub a b = Some w -> 
     valid a -> valid b -> le a w ;

  le_lub_right : forall a b, max (rk a) (rk b) <= k -> 
     compatible a b -> forall w, lub a b = Some w -> 
     valid a -> valid b -> le b w ;

  le_trans : forall u v w, max (max (rk u) (rk v)) (rk w) <= k -> 
     valid u -> valid v -> valid w -> le u v -> le v w -> le u w ;

  (* lub is the Least Upper Bound *)
  le_sup_lub : forall u v w1 w2, 
      max (max (rk u) (rk v)) (rk w1) <= k ->
      le u w2 -> le v w2 -> lub u v = Some w1 -> le w1 w2 ;

}.

(* First prove all of the lemmas about finfun's assuming 
   the top-level lemmas.
*)
Lemma le_fun_mono_arg :
    forall h u1 u2 k, 
      OrderTheoreticLemmas k ->
        (max (max (rk_fun h) (rk u1)) (rk u2)) <= k -> 
           valid_fun h -> valid u1 -> valid u2 -> 
           compatible u1 u2 -> le u1 u2 ->
           forall w1 w2, app h u1 = Some w1 -> app h u2 = Some w2 -> 
                    compatible w1 w2 /\ le w1 w2.
Proof.
  induction h as [|[u v]h].
    all: move=> u1 u2 k OTL RK Vh Vu1 Vu2 Cu Lu w1 w2 A1 A2.
    - cbn in *. inversion A1. inversion A2. subst. split; done.
    - rewrite -> app_spec in A1, A2. cbn in A1, A2.
      rewrite <- app_spec in A1, A2.
      cbn in RK.
      destruct (compatible u u1 && le u u1) eqn:Lu1;
        [move: Lu1 => /andP [Cu1 Lu1]|
        rewrite Bool.andb_false_iff in Lu1].
      all: destruct (app h u1) eqn:E1; try done.
      all: move: (rk_app E1) => Ru1.
      all: destruct (compatible u u2 && le u u2) eqn:Lu2;
           [move: Lu2 => /andP [Cu2 Lu2]|
            rewrite Bool.andb_false_iff in Lu2].
      all: destruct (app h u2) eqn:E2; try done.
      all: move: (rk_app E2) => Ru2.
      + (* both contribute *)
        have [Ve Ve0]: valid e /\ valid e0.
        { destruct (~~ is_nil h) eqn:Nh.        
          split; 
          [eapply (@valid_app h u1)|
           eapply (@valid_app h u2)];
            eauto using valid_fun_tail.
          destruct h; try done.
          inversion E1. inversion E2. auto.
        } 
        have Vu: valid u. eauto with valid. 
        have Vv: valid v. eauto with valid.
        have Vw1: valid w1. eapply valid_lub in A1; eauto.
        have Vw2: valid w2. eapply valid_lub in A2; eauto.

        move: (rk_app E1) => Re.
        move: (rk_app E2) => Re0.
        move: (rk_lub A1) => Rw1.
        move: (rk_lub A2) => Rw2.

        have [IHc IHl]: compatible e e0 /\ le e e0.
        { destruct (~~ is_nil h) eqn:Nh.
          - eapply (IHh u1 u2); eauto using valid_fun_tail. lia.
          - destruct h; try done. 
            inversion E1. inversion E2. auto.
        }             
        have Cve:  compatible v e. eapply lub_compatible; eauto.
        have Cve0: compatible v e0. eapply lub_compatible; eauto.

        (*         w2
                   /
        lub = w1 e0
           / \  /\
          v   e   v     *)

        have LE1 : le e w1. 
        { eapply (@le_lub_right _ OTL); 
            eauto using valid_fun_head, key_valid, val_valid. lia. }

        have LE2 : le e0 w2.
        { eapply (@le_lub_right _  OTL); 
            eauto using valid_fun_head, key_valid, val_valid. lia. }

        have LE3: le e w2.
        { eapply (@le_trans _ OTL e e0 w2); eauto. lia.  } 

        have LE4 : le v w2.
        { eapply (@le_lub_left _ OTL) in A2; eauto. lia. }

        have LE5 : le w1 w2.
        { eapply (@le_sup_lub _ OTL v e w1 w2) in A1; eauto. lia. }

        
        have Cw1w2: compatible w1 w2.
        { 
          eapply comp_down; eauto. eapply compatible_refl; eauto.
        } 
        split; eauto.

      + have Lu3 : le u u2.  (* only second, a contradiction *)
        { eapply (@le_trans _ OTL u u1 u2); 
          eauto using key_valid, valid_fun_head. lia. }
        have Cu3 : compatible u u2.
        { eapply comp_down; eauto. eapply compatible_refl; eauto. }
        rewrite Cu3 in Lu2. rewrite Lu3 in Lu2.
        destruct Lu2; done.

      + (* only the first, ok *)
        destruct (~~ is_nil h) eqn:Nh.
        ++ inversion A1; subst. clear A1.
           have Vt: valid_fun h. 
           { eauto using valid_fun_tail, val_valid. }
           have Ve0: valid e0.
           { eapply (@valid_app h u2); eauto. } 
           have [Ce0 Le0]: compatible w1 e0 /\ le w1 e0.
           { eapply (IHh u1 u2); eauto using valid_fun_tail. lia. } 
           have Le2: le e0 w2.
           { eapply (@le_lub_right _ OTL v e0); 
               eauto using lub_compatible, 
               valid_fun_head, val_valid. lia.
           }
           split.
           { eapply comp_down; eauto.
             eapply lub_compatible_trans; eauto using compatible_refl.
             eapply compatible_sym.
             eapply lub_compatible; eauto.
           } 
           {
             move: (rk_app E1) => RKw1.
             move: (rk_app E2) => RKe0.
             move: (rk_lub A2) => RKw2.
             eapply le_trans; eauto. lia.
             eapply (@valid_app h u1); eauto.
             eapply (@valid_lub v e0); eauto.
             eauto using lub_compatible, 
               valid_fun_head, val_valid. 
           } 
        ++ destruct h; try done.
           cbn in E1, E2. inversion E1; inversion E2; subst.
           inversion A1; inversion A2; subst.
           split. destruct w2; done. eapply le_bot.
      + (* neither *)
        destruct (~~ is_nil h) eqn:Nh.
        ++ inversion A1; inversion A2; subst. 
           eapply (IHh u1 u2); eauto using valid_fun_tail. lia.
        ++ destruct h; try done. 
           inversion E1. inversion E2. subst.
           inversion A1; inversion A2; subst. 
           done.
Qed.


Lemma le_fun_mono m (ih : OrderTheoreticLemmas m) h k u :
      (max (max (rk_fun h) (rk_fun k)) (rk u) <= m) -> 
       valid_fun h -> valid_fun k -> 
       le_fun h k -> valid u ->  
       forall w1 w2, app h u = Some w1 -> app k u = Some w2 -> 
                le w1 w2.
Proof.
    move: k u.
    induction h as [|[ui vi]h].
    all: move=> k u RK Vf Vk LE Vu w1 w2 EQ A2.
    - rewrite app_nil_eq in EQ. inversion EQ. apply le_bot.
    - rewrite app_spec in EQ. cbn in EQ. rewrite <- app_spec in EQ.
      cbn in RK. move: (rk_app A2) => Rw2.
      have Leu: le u u. { eapply le_refl. eapply ih. lia. eauto. }
      have Leui: le ui ui. { eapply le_refl. eapply ih. lia.
             eauto using key_valid, valid_fun_head. }

      destruct (compatible ui u && le ui u) eqn:LEui.
      + move: LEui => /andP [Cui LEui].
        have Vui: valid ui. eauto using valid_fun_head, key_valid.
        have Vvi: valid vi. eauto using valid_fun_head, val_valid.

        destruct (~~ is_nil h) eqn:Nh.
        ++ have Vh: valid_fun h. eauto using valid_fun_tail.

           move: LE => /andP [L1 L2]. cbn in RK.
           (* L1: k[ui] <= v   
              L2: h     <= k  *)

           destruct (valid_app_exists Vh Vu) as 
             [e1 [A1 Ve1]].
           rewrite A1 in EQ.
           move: (rk_app A1) => Re.

           have Vw2: valid w2. eapply (valid_app (f:= k) (u:=u)); eauto.

           destruct (app k ui) eqn:A4. 2: done.
           have Ve4: valid e. eapply (valid_app(f:=k)(u:=ui)); eauto.
           move: (rk_app A4) => Re4.

           destruct (valid_app_exists(f:=(ui,vi)::h)(u:=ui)) as
             [e5 [A5 Ve5]]; eauto.

           have L3: le e1 w2.
           { eapply (IHh k u); eauto. lia. } 

           have L4: le e w2.
           { eapply (@le_fun_mono_arg k ui u); eauto. lia. }

           have L5: le vi w2.
           { eapply (le_trans ih (v:=e)); eauto. lia. } 

           move: (rk_lub EQ) => Rw1.
           eapply (@le_sup_lub _ ih vi e1 w1); eauto.
           lia.

        ++ destruct h; try done.
           cbn in EQ. inversion EQ. clear EQ. 
           rewrite lub_bot_r in H0. inversion H0. subst. clear H0.
           cbn in LE. destruct (app k ui) eqn:A1. 2: done.
           move: LE => /andP [L1 _].
           have L2: le e w2.
           { eapply (@le_fun_mono_arg k ui u); eauto. lia. } 

           move: (rk_app A1) => Re.
           move: (le_trans ih(u:=w1)(v:=e)(w:=w2)) => h. 
           eapply h; eauto using valid_app. lia.

      + destruct (~~ is_nil h) eqn:Nh.
        ++ eapply IHh; eauto.        
           cbn in RK; lia.
           eauto using valid_fun_tail.
           cbn in LE. move: LE => /andP [_ LE]. eapply LE.
        ++ destruct h; try done.
           inversion EQ. eapply le_bot.
Qed.  

Lemma le_fun_weaken_cons m (ih : OrderTheoreticLemmas m) :
  forall f h u v,
    (max (max (rk_fun f) (rk_fun h)) (max (rk u) (rk v)) <= m)%nat ->
    valid_fun h -> valid u -> valid v ->
    forallb (fun '(ui,vi) => valid ui && valid vi) f -> 
    coherent_with h (u,v) ->
    le_fun f h -> le_fun f ((u,v) :: h).
Proof.
  induction f as [|[u1 v1] f IHf].
  - done.
  - move=> h u v RK Vh Vu Vv VF Coh LE.
    cbn in RK.
    cbn in VF. move: VF => /andP [/andP [Vu1 Vv1] VF]. 
    rewrite le_fun_cons in LE.
    destruct (app h u1) eqn:E. 2: done.
    move: LE => /andP [Lv1e LE].
    rewrite le_fun_cons.
    rewrite app_spec. cbn. rewrite <- app_spec.
    destruct (compatible u u1 && le u u1) eqn:CL.
    + move: CL => /andP [Cuu1 Luu1].
      rewrite E.
      have Ve: valid e. { eapply (@valid_app h u1 e Vh Vu1 E). }
      have Cve: compatible v e.
      { eapply (Comp_value_app (f:=h)(xi:=u1)(w:=e)); eauto. }
      destruct (compatible_lub_exists Cve) as [t EQ].
      rewrite EQ.
      move: (rk_app E) => Re.
      move: (rk_lub EQ) => Rt.
      have Vt: valid t. { eapply (valid_lub (u:=v)(v:=e)); eauto. }
      have LeT: le e t. { eapply (@le_lub_right _ ih v e); eauto. lia. }
      have Lv1t: le v1 t.
      { eapply (@le_trans _ ih v1 e t); eauto. lia. }
      apply /andP; split. done.
      eapply IHf; eauto. lia.
    + rewrite E.
      apply /andP; split. done.
      eapply IHf; eauto. lia.
Qed.


Lemma le_fun_refl  m (ih : OrderTheoreticLemmas m) f :
    (rk_fun f <= m)%nat -> valid_fun f -> le_fun f f.
Proof.
    induction f as [|[u v]f].
    all: move=> RK Vf. done.
    cbn in RK.
    have Vu: valid u. eauto using valid_fun_head, key_valid.
    have Vv: valid v. eauto using valid_fun_head, val_valid.
    rewrite le_fun_cons.
    rewrite app_spec. cbn. rewrite <- app_spec.
    rewrite compatible_refl; eauto.
    erewrite le_refl; eauto. 2: lia.
    cbn.
    destruct (~~ is_nil f) eqn:Nf.
    + move: (valid_fun_tail Vf) => Vt.
      have LEu: le u u. eapply le_refl; eauto. lia.
      destruct (valid_app_cons_compatible LEu Vf) as [w [E1 [Vw Cw]]].
      rewrite E1.
      apply compatible_sym in Cw.
      destruct (compatible_lub_exists Cw) as [w0 Lub].
      rewrite Lub.
      apply rk_app in E1.
      erewrite le_lub_left; eauto. 2: lia. cbn.
      eapply (@le_fun_weaken_cons _ ih f f u v); 
        eauto with valid.
      {  lia. }
      { eapply IHf. lia. exact Vt. }
    + destruct f; try done.
      cbn. rewrite lub_bot_r.
      erewrite le_refl; eauto. lia.
Qed.

Lemma le_fun_extend_left m (ih : OrderTheoreticLemmas m) :
    forall f g, (max (rk_fun f) (rk_fun g) <= m)%nat ->
           valid_fun f -> valid_fun g
           -> compatible_fun f g -> le_fun f (f ++ g).
Proof.
    induction f as [|[u v]f].
    all: move=> g RK Vf Vg Cfg. done.
    cbn in RK.
    specialize ih. 
    specialize (IHf g ltac:(lia)).
    rewrite le_fun_cons.
    rewrite app_spec. cbn. rewrite <- app_spec.
    rewrite compatible_cons_def in Cfg.
    have Vu : valid u. eauto using key_valid, valid_fun_head.
    have Vv : valid v. eauto using val_valid, valid_fun_head.

    move: Cfg => /andP [h1 Cfg].
    have CU: compatible u u. eapply compatible_refl; eauto.
    have LU: le u u. eapply le_refl; eauto. lia.
    rewrite CU.
    rewrite LU.
    cbn.
    have [w1 [EQ1 Vw1]] : { w1 & (app f u = Some w1) * valid w1 }.
    { destruct (~~ is_nil f) eqn:Nf.
      + have Vt: valid_fun f. eapply valid_fun_tail; eauto.
        eapply (valid_app_exists Vt Vu). 
      + destruct f; try done.
        exists bot. cbn. auto.
    }             
    destruct (valid_app_exists Vg Vu) as [w2 [EQ2 Vw2]].
    move: (app_append EQ1 EQ2) => EQ3. cbn in EQ3.
    have C12: (compatible w1 w2).
    { eapply compatible_app; eauto. } 
    destruct (compatible_lub_exists C12) as [w EQ4].
    rewrite EQ4 in EQ3. rewrite EQ3.
    move: (rk_app EQ2) => Rkw2.
    move: (rk_app EQ1) => Rkw1.
    move: (rk_lub EQ4) => Rkw.
      
    have Cvw2: compatible v w2.
    { eapply (Comp_value_app (f:=g)(xi:=u)(w:=w2)); eauto. }
    have Cvw1 : compatible v w1.
    { eapply (Comp_value_app (f:=f)(u:=u)(v:=v)(xi:=u)(w:=w1)); eauto.
      eapply compat. eapply valid_fun_head; eauto. }
    have Cvw : compatible v w.
    { apply compatible_sym.
      eapply (@compatible_lub w1 w2 v w).
      - apply compatible_sym. exact Cvw1.
      - apply compatible_sym. exact Cvw2.
      - exact EQ4. }
    destruct (compatible_lub_exists Cvw) as [e EQ5].
    rewrite EQ5.
    have Vw : valid w. { eapply (valid_lub (u:=w1)(v:=w2)); eauto. }
    move: (rk_lub EQ5) => Rke.
    apply /andP; split.
    - (* le v e *)
      eapply (@le_lub_left _ ih v w); eauto. lia.
    - (* le_fun f ((u,v) :: f ++ g) *)
      destruct (~~ is_nil f) eqn:Nf.
      + have Vt: valid_fun f. eapply valid_fun_tail; eauto.
        have Cohf : coherent_with f (u,v).
        { eapply compat. eapply valid_fun_head; eauto. }
        have Cohfg : coherent_with (f ++ g) (u,v).
        { eapply coherent_with_append; eauto. }
        have Vfg : valid_fun (f ++ g).
        { eapply valid_append; eauto. }
        have Hfg : le_fun (f++g) ((u,v) :: f ++ g).
        { eapply (@le_fun_weaken_cons _ ih (f++g) (f++g) u v); 
            eauto with valid.
          - rewrite rk_fun_append. lia.
          - eapply (@le_fun_refl _ ih (f++g)).
            + rewrite rk_fun_append. lia.
            + exact Vfg. }
        unfold le_fun in Hfg.
        rewrite forallb_app in Hfg.
        move: Hfg => /andP [Hfg _].
        exact Hfg.
      + destruct f; try done.
Qed.

Lemma le_fun_extend_right m (ih : OrderTheoreticLemmas m) :
    forall f g, (max (rk_fun f) (rk_fun g) <= m) ->
           valid_fun f -> valid_fun g
           -> compatible_fun g f -> le_fun f (g ++ f).
Proof.
  move=> f g. move: f.
  induction g as [|[u v] g'].
  - move=> f RK Vf Vg Cgf.
    cbn in RK. rewrite app_nil_l.
    eapply le_fun_refl; eauto. lia.
  - move=> f RK Vf Vg Cgf.
    cbn in RK.
    have Vu : valid u. eauto using key_valid, valid_fun_head.
    have Vv : valid v. eauto using val_valid, valid_fun_head.
    have Cohg': coherent_with g' (u,v).
    { eapply compat. eapply valid_fun_head; eauto. }
    rewrite compatible_cons_def in Cgf.
    move: Cgf => /andP [Cohf Cgf'].
    rewrite <- app_comm_cons.
    destruct (~~ is_nil g') eqn:Ng.
    + have Vg': valid_fun g'. { eapply valid_fun_tail; eauto. }
      specialize (IHg' f ltac:(lia) Vf Vg' Cgf').
      have Coh: coherent_with (g' ++ f) (u,v).
      { eapply coherent_with_append; eauto. }
      have Vfg: valid_fun (g' ++ f).
      { eapply valid_append; eauto. }
      eapply (@le_fun_weaken_cons _ ih f (g' ++ f) u v);
        eauto with valid.
      rewrite rk_fun_append. lia.
    + destruct g'; try done.
      rewrite app_nil_l.
      eapply (@le_fun_weaken_cons _ ih f f u v);
        eauto with valid.
      * lia.
      * eapply le_fun_refl; eauto. lia.
Qed.


Lemma le_fun_trans m (ih : OrderTheoreticLemmas m) : 
    forall g h k, (max (max (rk_fun g) (rk_fun h)) (rk_fun k) <= m)%nat -> 
             valid_fun g -> valid_fun h -> valid_fun k ->
             le_fun g h -> le_fun h k -> le_fun g k.
Proof.
  induction g as [|[u v]g].
  all: move=>h k RK Vug Vh Vk h1 h2.
  - done.
  - move: h1 => /andP [h1 Lgh]. 
    have Vu: valid u. eauto using key_valid, valid_fun_head.
    have Vv: valid v. eauto using val_valid, valid_fun_head.
    cbn in RK.
    apply /andP. split.
    + clear IHg Lgh.
      (* use le_trans for u,v *)
      destruct (valid_app_compatible Vh Vu) as [wh [Ahu [Vwh Cwh]]].
      rewrite Ahu in h1. 
      destruct (valid_app_compatible Vk Vu) as [wk [Aku [Vwk Cwk]]].
      rewrite Aku.
      move: (rk_app Ahu) => Rwh.
      move: (rk_app Aku) => Rwk.
      have LEw: le wh wk.
      { eapply (@le_fun_mono _ ih h k u); eauto. lia. } 
      eapply (@le_trans _ ih v wh wk); eauto. lia.
    + destruct (~~ is_nil g) eqn:Ng.
      ++ eapply (IHg h k); eauto. lia.
         eauto using valid_fun_tail. 
      ++ destruct g; try done.
Qed.

(*
Definition is_bot (w : elt) := 
  match w with bot => true | _ => false end.

Lemma rk_app2 f : valid_fun f -> forall u w,
  app f u = Some w -> ~~ is_bot w -> rk u <= rk_fun f.
Proof.
  induction f as [|[ui vi]f].
  cbn. move=> _ u w EQ NB. inversion EQ. subst. done.
  move=> Vf u w EQ NB. rewrite app_cons_eq in EQ.
  destruct (compatible ui u && le ui u) eqn:LEui.
  + destruct (app f u) eqn:APPf; try done.
    specialize (IHf (valid_fun_tail Vf) _ _ APPf).
    destruct (~~ is_bot e) eqn:Nb.
    - specialize (IHf ltac:(eauto)). cbn. lia.
    - destruct e ; try done.
      rewrite lub_bot_r in EQ. inversion EQ. subst.
      cbn.
Admitted.
*)

(*
(*** NOT TRUE due to contravariance ***)
Lemma le_fun_rk m (ih : OrderTheoreticLemmas m) :
    forall f g, (max (rk_fun f) (rk_fun g) <= m)%nat ->
           valid_fun f -> 
           valid_fun g ->
           le_fun f g -> rk_fun f <= rk_fun g.
Proof.
  induction f as [|[u v]f].
  move=> g RK Vf Vg LE. cbn. lia.
  move=> g RK Vf Vg LE.
  cbn in RK.
  cbn.
  cbn in LE.
  destruct (app g u) eqn:APPu; try done.
  move: LE => /andP [LEve LEf]. fold (le_fun f g) in LEf.
  move: (valid_fun_tail Vf) => Vt.
  move: (valid_fun_head Vf) => Vh.
  specialize (IHf g ltac:(lia) Vt Vg LEf).
  move: (rk_app APPu) => RK1.
  destruct (~~is_bot e) eqn:NB.
  - move: (rk_app2 Vg APPu NB) => RK2.
    move: (@rk_le _ ih v e ltac:(lia) LEve) => RKve.
    lia.
  - destruct e; try done.
    move: (val_nbot Vh) => NB2. rewrite LEve in NB2. done.
Qed.
*)

Lemma OTLs : forall k, OrderTheoreticLemmas k.
Proof.
  elim /strong_ind.
  move=> m ih.
  constructor.

  - (* le_refl *)
    move=> a RK Va.
    destruct a.
    all: cbn in RK.
    all: try solve [cbn;done].
    + rewrite le_succ.
      specialize (ih (rk a)).
      eapply le_refl; eauto.
    + fold rk_fun in RK. rewrite le_tpi.
      move: Va => /andP [Va Vl]. fold valid in Va.
      fold valid in Vl.
      specialize (ih (max (rk a) (rk_fun l))).
      apply /andP. split. eapply le_refl; eauto. lia.
      eapply le_fun_refl; eauto. lia.
    + rewrite le_abs.
      cbn in Va. move: Va => /andP [Va _].
      eapply le_fun_refl; eauto.

  - (* le_lub_left *)
    move=> u.
    induction u.
    all: move=> v RK Cu w h Vu Vv.
    all: try solve [destruct w; try done].
    all: try solve [destruct v; inversion h; subst; auto].
    + (* succ *)
    destruct v; inversion h; subst; cbn in *. 
    ++ (* needs le_refl *) eapply le_refl; eauto. 
    ++ destruct (lub u v) eqn:EQ; try done. 
      inversion H0. subst. cbn. eapply IHu; eauto. lia.
     (* tpi *)
    + cbn in RK. fold rk_fun in RK.
      move: Vu => /andP [h1 h2].
      fold valid in *. fold (valid_fun l) in h2.
      destruct v; cbn in h; inversion h; subst; cbn in RK.      
      ++ (* needs le_refl *)
        rewrite le_tpi.
        apply /andP. split. eapply le_refl; eauto.  lia.
        eapply le_fun_refl; eauto. lia.
      ++ destruct (compatible_fun l l0) eqn:E. 2: done.
         destruct (lub u v) eqn:E2. 2: done.
         cbn in h. inversion h.
         move: Vv => /andP [Vv Vl0].
         fold valid in *. fold (valid_fun l0) in Vl0.
         move: Cu => /andP [Cu Cl].
         fold compatible in *.
         rewrite le_tpi. apply /andP. split; eauto.
         eapply le_lub_left; eauto. lia.
         eapply le_fun_extend_left; eauto. fold rk_fun in RK. fold rk_fun. lia.
    + (* abs *)
      destruct v; cbn in h; inversion h; subst.
      ++ cbn in Vu. move: Vu => /andP [Vu _].
         rewrite le_abs. eapply le_fun_refl; eauto.
         eapply ih. cbn in RK. fold rk_fun in RK. lia.
      ++ destruct (compatible_fun l l0) eqn:E. 2: done.
         cbn in h. inversion h.
         rewrite le_abs.
         cbn in RK. fold rk_fun in RK.
         cbn in Vu, Vv. move: Vu => /andP [Vu _]. move: Vv => /andP [Vv _].
         eapply le_fun_extend_left; eauto.

  - (* le_lub_right *)
    move=> u v. move:u.
    induction v.
    all: move=> u RK Cu w h Vu Vv.
    all: try solve [destruct w; try done].
    all: try solve [destruct u; inversion h; subst; auto].
    + (* succ *)
    destruct u; inversion h; subst; cbn in *. 
    ++ (* needs le_refl *) eapply le_refl; eauto. 
    ++ destruct (lub u v) eqn:EQ; try done. 
      inversion H0. subst. cbn. eapply IHv; eauto. lia.
     (* tpi *)
    + cbn in RK. fold rk_fun in RK.
      move: Vv => /andP [h1 h2].
      fold valid in *. fold (valid_fun l) in h2.
      destruct u; cbn in h; inversion h; subst; cbn in RK.      
      ++ (* needs le_refl *)
        rewrite le_tpi.
        apply /andP. split. eapply le_refl; eauto.  lia.
        eapply le_fun_refl; eauto. lia.
      ++ destruct (compatible_fun l0 l) eqn:E. 2: done.
         destruct (lub u v) eqn:E2. 2: done.
         cbn in h. inversion h.
         move: Vu => /andP [Vu Vl0].
         fold valid in *. fold (valid_fun l0) in Vl0.
         move: Cu => /andP [Cu Cl].
         fold compatible in *.
         rewrite le_tpi. apply /andP. split; eauto.
         eapply le_lub_right; eauto. lia.
         eapply le_fun_extend_right; eauto. fold rk_fun in RK. fold rk_fun. lia.
    + (* abs *)
      destruct u; cbn in h; inversion h; subst.
      ++ cbn in Vv. move: Vv => /andP [Vv _].
         rewrite le_abs. eapply le_fun_refl; eauto.
         cbn in RK. fold rk_fun in RK. eauto.
      ++ destruct (compatible_fun l0 l) eqn:E. 2: done.
         cbn in h. inversion h.
         rewrite le_abs.
         cbn in RK. fold rk_fun in RK.
         cbn in Vu, Vv. move: Vu => /andP [Vu _]. move: Vv => /andP [Vv _].
         eapply le_fun_extend_right; eauto. lia.

  - (* le_trans *)
    move=> u v w RK Vu Vv Vw L1 L2.
    destruct u; destruct v; destruct w;
      try solve [cbn in L1; cbn in L2; done].
    + rewrite le_succ. rewrite -> le_succ in L1, L2.
      cbn in RK.
      eapply (@le_trans _ (ih _ RK) u v w); eauto.
    + rewrite le_tpi.  rewrite -> le_tpi in L1, L2.
      cbn in RK. fold rk_fun in RK.
      move: Vu => /andP [Vu Vl].
      move: Vv => /andP [Vv Vl0].
      move: Vw => /andP [Vw Vl1].
      move: L1 => /andP [Luv Lll0].
      move: L2 => /andP [Lvw Ll0l1].
      fold valid in Vl, Vv, Vu , Vw, Vl0 , Vl1.
      apply /andP. split.
      eapply (@le_trans _ (ih _ RK) u v w); eauto. lia.
      eapply (@le_fun_trans _ (ih _ RK) l l0 l1); eauto. lia.

    + rewrite le_abs. rewrite -> le_abs in L1, L2.
      cbn in RK. fold rk_fun in RK.
      cbn in Vu, Vv, Vw.
      move: Vu => /andP [Vu _]. move: Vv => /andP [Vv _]. move: Vw => /andP [Vw _].
      eapply (@le_fun_trans _ (ih _ RK) l l0 l1); eauto.

  - (* le_sup_lub *)
    move=> u v w1 w2 RK LE1 LE2 LUB.
    destruct u; destruct v; cbn in LUB; inversion LUB; try done.
    + apply le_succ_inv in LE1. move: LE1 => [v1 [EQ1 LE1]].
      apply le_succ_inv in LE2. move: LE2 => [v2 [EQ2 LE2]].
      destruct (lub u v) eqn:LUB2. 2: done. inversion LUB. subst.
      inversion EQ2. subst.
      rewrite le_succ.
      eapply (@le_sup_lub _ (ih _ RK) u v); eauto.
    + apply le_tpi_inv in LE1. move: LE1 => [v1 [f1 [EQ1 [LE1 LF1]]]].
      apply le_tpi_inv in LE2. move: LE2 => [v2 [f2 [EQ2 [LE2 LF2]]]].
      destruct (compatible_fun l l0) eqn:CF. 2:done.
      destruct (lub u v) eqn:LUB2. 2: done. inversion LUB. subst.
      inversion EQ2. subst.
      rewrite le_tpi.
      apply /andP. split.
      eapply (@le_sup_lub _ (ih _ RK) u v); eauto. fold rk rk_fun max. lia.
      eapply le_fun_extend; eauto.
    + apply le_abs_inv in LE1. move: LE1 => [f1 [EQ1 LF1]].
      apply le_abs_inv in LE2. move: LE2 => [f2 [EQ2 LF2]].
      destruct (compatible_fun l l0) eqn:CF. 2: done.
      inversion LUB. inversion EQ2. subst. inversion EQ2. subst.
      rewrite le_abs.
      eapply le_fun_extend; eauto.
Qed.

End OTL.

Lemma le_fun_refl f : valid_fun f -> le_fun f f.
Proof.
  eapply OTL.le_fun_refl. eapply OTL.OTLs. reflexivity.
Qed.

Lemma le_refl a : valid a -> le a a.
Proof. 
  eapply OTL.le_refl. eapply OTL.OTLs. reflexivity.
Qed.

Lemma le_lub_left a b : 
     compatible a b -> forall w, lub a b = Some w -> 
     valid a -> valid b -> le a w.
Proof. 
  eapply OTL.le_lub_left. eapply OTL.OTLs. reflexivity.
Qed.

Lemma le_lub_right a b :
     compatible a b -> forall w, lub a b = Some w -> 
     valid a -> valid b -> le b w.
Proof.
  eapply OTL.le_lub_right. 2: reflexivity.
  eapply OTL.OTLs.
Qed.

Lemma le_trans : forall u v w, 
     valid u -> valid v -> valid w -> le u v -> le v w -> le u w.
Proof. 
  move=> u v w.
  eapply OTL.le_trans. 2: reflexivity.
  eapply OTL.OTLs.
Qed.

Lemma le_fun_trans u v w :
     valid_fun u -> valid_fun v -> valid_fun w -> le_fun u v -> le_fun v w -> le_fun u w.
Proof. 
  eapply OTL.le_fun_trans. 2: reflexivity.
  eapply OTL.OTLs.
Qed.

  
Lemma le_sup_lub u v w1 w2 :
    le u w2 -> le v w2 -> lub u v = Some w1 ->
    le w1 w2.
Proof.
  eapply OTL.le_sup_lub. 2: reflexivity.
  eapply OTL.OTLs.
Qed.


Lemma le_fun_mono h k u :
       valid_fun h -> valid_fun k ->
       le_fun h k -> valid u ->
       forall w1 w2, app h u = Some w1 -> app k u = Some w2 ->
                le w1 w2.
Proof.
  eapply OTL.le_fun_mono. eapply OTL.OTLs. reflexivity.
Qed.

Lemma le_fun_mono_arg h u1 u2 :
       valid_fun h -> valid u1 -> valid u2 ->
       compatible u1 u2 -> le u1 u2 ->
       forall w1 w2, app h u1 = Some w1 -> app h u2 = Some w2 ->
                compatible w1 w2 /\ le w1 w2.
Proof.
  eapply OTL.le_fun_mono_arg with (k := max (max (rk_fun h) (rk u1)) (rk u2)).
  eapply OTL.OTLs. reflexivity.
Qed.

Lemma le_fun_weaken_cons f h u v :
  valid_fun h -> valid u -> valid v ->
  forallb (fun '(ui,vi) => valid ui && valid vi) f ->
  coherent_with h (u, v) ->
  le_fun f h -> le_fun f ((u, v) :: h).
Proof.
  eapply OTL.le_fun_weaken_cons. 2: reflexivity.
  eapply OTL.OTLs.
Qed.


(* ----------------------------------------------------- *)
(* Some corollaries of OTLs *)

(* le u v (for valid v) implies compatible u v. *)
Lemma le_valid_compatible u v : valid v -> le u v -> compatible u v.
Proof.
  move=> Vv LE.
  eapply comp_down; eauto. eapply compatible_refl; eauto.
Qed.

Lemma le_valid_compatible_pair u1 u2 v: 
   valid v -> le u1 v -> le u2 v -> compatible u1 u2.
Proof.
   move=> Vw Lu Lv.
   eapply comp_down; eauto.
   eapply compatible_sym.
   eapply comp_down; eauto.
   eapply compatible_refl; eauto.
Qed.

Lemma comp_down_pair : 
      forall u1 u2 v1 v2, compatible v1 v2 -> le u1 v1 -> le u2 v2 ->
                     compatible u1 u2.
Proof.
      move=> u1 u2 v1 v2 C1 LE1 LE2.
      move: (comp_down LE1 C1) => C2.
      apply compatible_sym in C2.
      move: (comp_down LE2 C2) => C3. 
      eapply compatible_sym.
      auto.
Qed.



(* extensional introduction form for le_fun *)
Lemma le_fun_ext f1 f2 :
  valid_fun f1 ->
  valid_fun f2 ->
  (forall u w1 w2, valid u ->
              app f1 u = Some w1 -> app f2 u = Some w2 ->
              compatible w1 w2 && le w1 w2) ->
  le_fun f1 f2.
Proof.
  move=> Vf1 Vf2 h.
  have Lrefl: le_fun f1 f1. { eapply le_fun_refl; eauto. }
  apply /forallb_forall.
  move=> [ui vi] In.
  move: (valid_fun_subterms_prop Vf1 In) => [Vui Vvi].
  move: (valid_app_exists Vf1 Vui) => [w1 [E1 Vw1]].
  move: (valid_app_exists Vf2 Vui) => [w2 [E2 Vw2]].
  rewrite E2.
  specialize (h _ _ _ Vui E1 E2).
  move: h => /andP [_ Lw12].
  move: Lrefl => /forallb_forall Lrefl.
  move: (Lrefl _ In) => /=.
  rewrite E1. move=> Lvi1.
  eapply le_trans with (v := w1); eauto.
Qed.

Lemma valid_elt x y f : 
  valid_fun f -> In (x,y) f -> valid x /\ valid y.
Proof.
  move=> /andP [_ /forallb_forall V] IN.
  specialize (V _ IN).
  move: V => /andP [Vx Vy].
  easy.
Qed.

Lemma le_app f ui vi : forall u v,
  valid_fun f ->
  valid u ->
  app f u = Some v -> In (ui,vi) f -> le ui u -> le vi v.
Proof. 
  induction f.
  - easy.
  - move=> u v Vf Vu APP IN LEu.
    destruct (valid_elt Vf IN) as [Vui Vvi].
    destruct IN as [h1|h1].
    + subst.
      rewrite app_cons_eq in APP.
      have CC: compatible ui u. eapply le_valid_compatible; eauto.
      rewrite CC in APP.
      rewrite LEu in APP.
      cbn in APP.
      destruct (app f u) eqn:EA; try done.
      eapply le_lub_left in APP; eauto.
      eapply lub_compatible; eauto.
      eauto with valid.
    + destruct a as [uj vj].
      rewrite app_cons_eq in APP.
      have Vft: valid_fun f. eauto with valid.
      destruct (compatible uj u && le uj u) eqn:CC.
      ++ destruct (app f u) eqn:EA; try done.
         specialize (IHf _ _ Vft Vu EA h1 LEu).
         have Ve: valid e. eapply (valid_app Vft Vu); eauto.
         have Vvj: valid vj. eauto with valid.
         have Vv: valid v. eapply (valid_lub Vvj Ve); eauto.
         have LEv: le e v. 
         { eapply le_lub_right in APP; eauto.
           eapply lub_compatible; eauto. } 
         eapply le_trans with (v := e); eauto.      
      ++ destruct (app f u) eqn:EA; try done.
         specialize (IHf _ _ Vft Vu EA h1 LEu).
         inversion APP; subst; eauto.
Qed.

Lemma valid_tpi_intro a f :
  valid a -> valid_fun f -> valid (tpi a f).
Proof.
  move=> Va Vf. cbn. apply /andP. split; [exact Va|exact Vf].
Qed.

Lemma valid_tpi_inv a f :
  valid (tpi a f) -> valid a /\ valid_fun f.
Proof.
  move=> V. cbn in V. move: V => /andP [Va Vf].
  split; [exact Va|exact Vf].
Qed.



(* extract app f u and its validity when valid (tpi a f) holds. *)
Lemma app_tpi_valid a f u :
  valid (tpi a f) -> valid u ->
  forall t, app f u = Some t -> valid t.
Proof.
  move=> V Vu t A.
  cbn in V. move: V => /andP [_ Vf].
  fold (valid_fun f) in Vf.
  destruct (~~ is_nil f) eqn:Nf.
  - eapply valid_app; eauto.
  - destruct f; try done. cbn in A. inversion A. done.
Qed.

(* existence of app f u when valid (tpi a f) holds. *)
Lemma app_tpi_exists a f u :
  valid (tpi a f) -> valid u ->
  { t & (app f u = Some t) * (valid t)}.
Proof.
  move=> V Vu.
  cbn in V. move: V => /andP [_ Vf].
  fold (valid_fun f) in Vf.
  destruct (~~ is_nil f) eqn:Nf.
  - eapply valid_app_exists; eauto.
  - destruct f; try done. exists bot. cbn. auto.
Qed.


Definition is_bot (a : elt) :bool := 
  match a with 
  | bot => true
  | _ => false
  end.
  
Definition singleton (a b: elt) : elt :=
  if is_bot b then bot 
  else abs (cons (a,b) nil).


(* ------------------ inversion for lub -------------------- *)

(** * inversion lemmas for lub *)

Lemma lub_bot_inv u v :
  lub u v = Some bot -> u = bot /\ v = bot.
Proof.
  destruct u; destruct v; try done.
  all: cbn.
  destruct (lub u v); done.
  destruct (compatible_fun l l0); try done.
  destruct (lub u v); done.
  destruct (compatible_fun l l0); try done.
Qed.
Lemma lub_bot_inv_r u v : 
  lub u v = Some bot -> v = bot.
Proof. move=> h. eapply (lub_bot_inv h). Qed.
Lemma lub_bot_inv_l u v : 
  lub u v = Some bot -> u = bot.
Proof. move=> h. eapply (lub_bot_inv h). Qed.

Lemma lub_tuniv_inv (u v:elt) :
  ~~ is_bot u -> ~~ is_bot v ->
  lub u v = Some tuniv ->
  (u = tuniv) /\ (v = tuniv).
Proof.
  destruct u; destruct v; try done.
  all: cbn.
  move=> _ _ h. inversion h. subst. eauto.
  destruct (lub u v) eqn:hl; try done.
  destruct (compatible_fun l l0); try done.
  destruct (lub u v); done.
  destruct (compatible_fun l l0); try done.
Qed.

Lemma lub_tnat_inv (u v:elt) :
  ~~ is_bot u -> ~~ is_bot v ->
  lub u v = Some tnat ->
  (u = tnat) /\ (v = tnat).
Proof.
  destruct u; destruct v; try done.
  all: cbn.
  destruct (lub u v) eqn:hl; try done.
  destruct (compatible_fun l l0); try done.
  destruct (lub u v); done.
  destruct (compatible_fun l l0); try done.
Qed.

Lemma lub_zero_inv (u v:elt) :
  ~~ is_bot u -> ~~ is_bot v ->
  lub u v = Some zero ->
  (u = zero) /\ (v = zero).
Proof.
  destruct u; destruct v; try done.
  all: cbn.
  destruct (lub u v) eqn:hl; try done.
  destruct (compatible_fun l l0); try done.
  destruct (lub u v); done.
  destruct (compatible_fun l l0); try done.
Qed.


Lemma lub_succ_inv (u v:elt) (w : elt) :
  ~~ is_bot u -> ~~ is_bot v ->
  lub u v = Some (succ w) ->
  { u1 & { v1 & (u = succ u1) * ((v = succ v1)
       * (lub u1 v1 = Some w))}}.
Proof.
  destruct u; destruct v; try done.
  all: cbn.
  - destruct (lub u v) eqn:hl; try done.
    move=> _ _ h. inversion h. subst. eauto.
  - destruct (compatible_fun l l0); try done.
    destruct (lub u v); done.
  - destruct (compatible_fun l l0); try done.
Qed.

Lemma lub_abs_inv (u v:elt) (f : list (elt * elt)) :
  ~~ is_bot u -> ~~ is_bot v ->
  lub u v = Some (abs f) ->
  { f1 & { f2 & (u = abs f1) * ((v = abs f2)
       * (f = f1 ++ f2)%list )}}.
Proof.
  destruct u; destruct v; try done.
  all: cbn.
  destruct (lub u v); done.
  destruct (compatible_fun l l0); try done.
  destruct (lub u v); done.
  destruct (compatible_fun l l0); try done.
  move=> _ _ h. inversion h. subst. eauto.
Qed.

Lemma lub_tpi_inv (u v:elt) a f :
  ~~ is_bot u -> ~~ is_bot v ->
  lub u v = Some (tpi a f) ->
  { a1 & { f1 & { a2 & { f2 & (u = tpi a1 f1) * ((v = tpi a2 f2)
       * ((lub a1 a2 = Some a)
       * (f = f1 ++ f2)%list))}}}}.
Proof.
  destruct u; destruct v; try done.
  all: cbn.
  destruct (lub u v); done.
  destruct (compatible_fun l l0); try done.
  destruct (lub u v) eqn:h1; try done.
  destruct (compatible_fun l l0) eqn:h2; try done.
  move=> _ _ h. inversion h. subst.
  exists u. exists l. exists v. exists l0. eauto.
  move=> _ _ h. inversion h. subst.
  exists u. exists l. exists v. exists l0. eauto.
  destruct (compatible_fun l l0) eqn:h2; try done.
 Qed.

(* Inverse of valid_append: validity of f ++ g entails validity of each
   piece plus compatibility between them. *)
Lemma valid_fun_append_inv f g :
  valid_fun (f ++ g) ->
  valid_fun f /\ valid_fun g /\ compatible_fun f g.
Proof.
  move=> /andP [/andP [Cfg NBfg] Valfg].
  unfold compatible_fun in Cfg. rewrite forallb_app in Cfg.
  move: Cfg => /andP [Cf_app Cg_app].
  unfold no_bot_result in NBfg. rewrite forallb_app in NBfg.
  move: NBfg => /andP [NBf NBg].
  rewrite forallb_app in Valfg.
  move: Valfg => /andP [Valf Valg].
  (* From Cf_app (forallb (coherent_with (f ++ g)) f) extract: f-f and f-g *)
  have Cff : compatible_fun f f.
  { unfold compatible_fun. apply /forallb_forall => p Hp.
    move: Cf_app => /forallb_forall Cf_app.
    move: (Cf_app p Hp). destruct p as [u v]. unfold coherent_with.
    rewrite forallb_app => /andP [Cf_p _]. exact Cf_p. }
  have Cfg' : compatible_fun f g.
  { unfold compatible_fun. apply /forallb_forall => p Hp.
    move: Cf_app => /forallb_forall Cf_app.
    move: (Cf_app p Hp). destruct p as [u v]. unfold coherent_with.
    rewrite forallb_app => /andP [_ Cg_p]. exact Cg_p. }
  have Cgg : compatible_fun g g.
  { unfold compatible_fun. apply /forallb_forall => p Hp.
    move: Cg_app => /forallb_forall Cg_app.
    move: (Cg_app p Hp). destruct p as [u v]. unfold coherent_with.
    rewrite forallb_app => /andP [_ Cg_p]. exact Cg_p. }
  repeat split.
  - unfold valid_fun. apply /andP; split; [apply /andP; split|]; assumption.
  - unfold valid_fun. apply /andP; split; [apply /andP; split|]; assumption.
  - exact Cfg'.
Qed.

Lemma le_fun_append f g f1 g1 :
 valid_fun (f ++ g) ->
 valid_fun (f1 ++ g1) ->
 le_fun f f1 -> le_fun g g1 -> le_fun (f ++ g) (f1 ++ g1).
Proof.
  move=> Vfg V1g1 LF LG.
  destruct (valid_fun_append_inv V1g1) as [Vf1 [Vg1 Cf1g1]].
  unfold le_fun. rewrite forallb_app. apply /andP; split.
  - (* f side *)
    apply /forallb_forall => -[ui vi] Hf.
    have Hin_fg : In (ui, vi) (f ++ g) by apply in_or_app; left.
    destruct (valid_fun_subterms_prop Vfg Hin_fg) as [Vui Vvi].
    move: LF => /forallb_forall LF.
    move: (LF (ui, vi) Hf) => /=.
    destruct (app f1 ui) as [vf|] eqn:APPf1; last done.
    move=> Lvi_vf.
    destruct (valid_app_exists Vg1 Vui) as [vg [APPg1 Vvg]].
    have Vvf : valid vf by eapply (valid_app Vf1 Vui APPf1).
    have Cvfvg : compatible vf vg
      by eapply compatible_app; eauto.
    destruct (compatible_lub_exists Cvfvg) as [w LUB].
    rewrite (app_append APPf1 APPg1) /= LUB.
    have Vw : valid w
      by eapply (valid_app V1g1 Vui); rewrite (app_append APPf1 APPg1) /= LUB.
    have Le_vf_w : le vf w by eapply le_lub_left; eauto.
    eapply le_trans; [exact Vvi | exact Vvf | exact Vw | exact Lvi_vf | exact Le_vf_w].
  - (* g side — symmetric *)
    apply /forallb_forall => -[ui vi] Hg.
    have Hin_fg : In (ui, vi) (f ++ g) by apply in_or_app; right.
    destruct (valid_fun_subterms_prop Vfg Hin_fg) as [Vui Vvi].
    move: LG => /forallb_forall LG.
    move: (LG (ui, vi) Hg) => /=.
    destruct (app g1 ui) as [vg|] eqn:APPg1; last done.
    move=> Lvi_vg.
    destruct (valid_app_exists Vf1 Vui) as [vf [APPf1 Vvf]].
    have Vvg : valid vg by eapply (valid_app Vg1 Vui APPg1).
    have Cvfvg : compatible vf vg
      by eapply compatible_app; eauto.
    destruct (compatible_lub_exists Cvfvg) as [w LUB].
    rewrite (app_append APPf1 APPg1) /= LUB.
    have Vw : valid w
      by eapply (valid_app V1g1 Vui); rewrite (app_append APPf1 APPg1) /= LUB.
    have Le_vg_w : le vg w by eapply le_lub_right; eauto.
    eapply le_trans; [exact Vvi | exact Vvg | exact Vw | exact Lvi_vg | exact Le_vg_w].
Qed.


(* ============================================================
   replaceKeys / replaceVals

   Dependent traversals of a finite function that replace either the
   first or the second component of each entry, with the replacement
   choice supplied per-edge via a membership-indexed function.

   Mirrors Agda LemmaForTS.replaceKeys / replaceVals.  Used by
   typing_semantics.InvTyp_Lam to build typed-keys / typed-values
   graphs from per-edge witnesses.
   ============================================================ *)

Definition replaceKeys :
  forall (g : list (elt * elt)) (f : forall p, In p g -> elt),
  list (elt * elt).
Proof.
  fix replaceKeys 1.
  intros [|p ps].
  - intros _. exact nil.
  - intros f.
    refine ((f p _, snd p) :: replaceKeys ps (fun q ein => f q _)).
    + left. reflexivity.
    + right. exact ein.
Defined.

Definition replaceVals :
  forall (g : list (elt * elt)) (f : forall p, In p g -> elt),
  list (elt * elt).
Proof.
  fix replaceVals 1.
  intros [|p ps].
  - intros _. exact nil.
  - intros f.
    refine ((fst p, f p _) :: replaceVals ps (fun q ein => f q _)).
    + left. reflexivity.
    + right. exact ein.
Defined.

Arguments replaceKeys : clear implicits.
Arguments replaceVals : clear implicits.

(* ------------------------------------------------------------
   Length / shape preservation
   ------------------------------------------------------------ *)

Lemma replaceKeys_length g f :
  length (replaceKeys g f) = length g.
Proof.
  induction g as [|p ps IH]; cbn; auto.
Qed.

Lemma replaceVals_length g f :
  length (replaceVals g f) = length g.
Proof.
  induction g as [|p ps IH]; cbn; auto.
Qed.

(* replaceVals preserves the keys (first components) of g pointwise. *)
Lemma replaceVals_map_fst g f :
  map fst (replaceVals g f) = map fst g.
Proof.
  induction g as [|p ps IH]; cbn; auto.
  f_equal. apply IH.
Qed.

(* replaceKeys preserves the values (second components) of g pointwise. *)
Lemma replaceKeys_map_snd g f :
  map snd (replaceKeys g f) = map snd g.
Proof.
  induction g as [|p ps IH]; cbn; auto.
  f_equal. apply IH.
Qed.

(* ------------------------------------------------------------
   Membership characterizations

   Each entry of replaceKeys g f is (f p Hin, snd p) for some p ∈ g.
   Each entry of replaceVals g f is (fst p, f p Hin) for some p ∈ g.

   The forward witness Hin is the proof of membership in g; by
   proof-irrelevance on Prop, f's output is determined by p alone.
   ------------------------------------------------------------ *)

Lemma replaceKeys_In_fwd g f q :
  In q (replaceKeys g f) ->
  exists p (Hin : In p g), q = (f p Hin, snd p).
Proof.
  induction g as [|p ps IH]; cbn; intros Hq.
  - inversion Hq.
  - destruct Hq as [Heq | Hrec].
    + exists p, (or_introl eq_refl). by rewrite Heq.
    + destruct (IH _ Hrec) as [p' [Hin' ->]].
      exists p', (or_intror Hin'). reflexivity.
Qed.

Lemma replaceKeys_In_bwd g f p (Hin : In p g) :
  In (f p Hin, snd p) (replaceKeys g f).
Proof.
  induction g as [|q qs IH]; cbn in Hin |- *.
  - contradiction.
  - destruct Hin as [Heq | Hrec].
    + left. subst q. f_equal.
    + right. exact (IH (fun r ein => f r (or_intror ein)) Hrec).
Qed.

Lemma replaceVals_In_fwd g f q :
  In q (replaceVals g f) ->
  exists p (Hin : In p g), q = (fst p, f p Hin).
Proof.
  induction g as [|p ps IH]; cbn; intros Hq.
  - inversion Hq.
  - destruct Hq as [Heq | Hrec].
    + exists p, (or_introl eq_refl). by rewrite Heq.
    + destruct (IH _ Hrec) as [p' [Hin' ->]].
      exists p', (or_intror Hin'). reflexivity.
Qed.

Lemma replaceVals_In_bwd g f p (Hin : In p g) :
  In (fst p, f p Hin) (replaceVals g f).
Proof.
  induction g as [|q qs IH]; cbn in Hin |- *.
  - contradiction.
  - destruct Hin as [Heq | Hrec].
    + left. subst q. f_equal.
    + right. exact (IH (fun r ein => f r (or_intror ein)) Hrec).
Qed.

(* ------------------------------------------------------------
   Validity preservation for replaceKeys.

   Given that:
     - g is valid,
     - the replacement function produces valid keys,
     - replaced-key compatibility implies original-key compatibility
       (this is the compatibility-preservation we get in InvTyp_Lam:
        the typed key z ≤ x, so if z1, z2 are compatible then x1, x2 are),
   then replaceKeys g f is also valid.

   Notation: the hypothesis is contravariant in compatibility because
   compatible_fun only checks one direction (key compat → value compat).
   ------------------------------------------------------------ *)

Lemma replaceKeys_valid_fun g f :
  valid_fun g ->
  (forall p Hin, valid (f p Hin)) ->
  (forall p1 Hin1 p2 Hin2,
     compatible (f p1 Hin1) (f p2 Hin2) ->
     compatible (fst p1) (fst p2)) ->
  valid_fun (replaceKeys g f).
Proof.
  move=> Vg Vf Hcompat.
  have NB_g : no_bot_result g by eapply valid_fun_no_bot; exact Vg.
  have Cfg : compatible_fun g g by eapply valid_fun_compatible; exact Vg.
  have All_g : forallb (fun '(ui,vi) => valid ui && valid vi) g
    by eapply valid_fun_subterms; exact Vg.
  unfold valid_fun. apply /andP; split; [apply /andP; split|].
  - (* compatible_fun (replaceKeys g f) (replaceKeys g f) *)
    unfold compatible_fun. apply /forallb_forall.
    move=> qi Hin_i. destruct qi as [zi vi].
    apply /forallb_forall.
    move=> qj Hin_j. destruct qj as [zj vj].
    apply /implyP. move=> Cij.
    apply replaceKeys_In_fwd in Hin_i.
    destruct Hin_i as [pi [Hin_pi Eq_i]]. injection Eq_i as -> ->.
    apply replaceKeys_In_fwd in Hin_j.
    destruct Hin_j as [pj [Hin_pj Eq_j]]. injection Eq_j as -> ->.
    have Cpij : compatible (fst pi) (fst pj) by eapply Hcompat; exact Cij.
    move: Cfg => /forallb_forall Cfg.
    destruct pi as [pi1 pi2]; destruct pj as [pj1 pj2]; cbn in *.
    move: (Cfg _ Hin_pi) => /= /forallb_forall Hfg.
    move: (Hfg _ Hin_pj) => /= /implyP H. by apply H.
  - (* no_bot_result (replaceKeys g f) *)
    unfold no_bot_result. apply /forallb_forall.
    move=> qi Hin_i. destruct qi as [zi vi].
    apply replaceKeys_In_fwd in Hin_i.
    destruct Hin_i as [pi [Hin_pi Eq_i]]. injection Eq_i as -> ->.
    move: NB_g => /forallb_forall NB_g.
    destruct pi as [pi1 pi2]; cbn in *.
    exact (NB_g _ Hin_pi).
  - (* forallb (valid . valid) *)
    apply /forallb_forall.
    move=> qi Hin_i. destruct qi as [zi vi].
    apply replaceKeys_In_fwd in Hin_i.
    destruct Hin_i as [pi [Hin_pi Eq_i]]. injection Eq_i as -> ->.
    apply /andP. split.
    + exact (Vf pi Hin_pi).
    + move: All_g => /forallb_forall All_g.
      move: (All_g _ Hin_pi). destruct pi as [pi1 pi2]; cbn.
      by move=> /andP [_ ?].
Qed.


End Raw.


(* -------------------------------------------------------- *)

(* Module of valid finite functions *)
Module Valid.

Definition elt : Set := 
  { u : Raw.elt & Raw.valid u }.
(* finfun records [valid_fun f] only.
   Use [nefinfun] (non-empty finfun) for the [abs] case. *)
Definition finfun : Set :=
  { f : list (Raw.elt * Raw.elt) & Raw.valid_fun f }.

Definition nefinfun : Set :=
  { f : list (Raw.elt * Raw.elt) & Raw.valid_fun f /\ ~~ Raw.is_nil f }.

(* --------------- constructors --------------- *)

Definition bot : elt. exists Raw.bot. auto. Defined.
Definition tnat : elt. exists Raw.tnat. auto. Defined.
Definition tuniv : elt. exists Raw.tuniv. auto. Defined.
Definition zero : elt. exists Raw.zero. auto. Defined.
Definition succ (u : elt) : elt.
  exists (Raw.succ (projT1 u)). cbn. eapply projT2. Defined.

Definition tabs (f : nefinfun) : elt.
exists (Raw.abs (projT1 f)).
destruct f as [rf [h1 h2]]. cbn.
apply /andP. split; assumption.
Defined.

(* Under the new definition of [valid], [tpi a f] is valid iff
   [valid a /\ valid_fun f] — and [valid_fun nil = true], so empty
   graphs are still allowed. *)
Definition tpi_finfun (a : elt) (f : finfun) : elt.
exists (Raw.tpi (projT1 a) (projT1 f)).
cbn. apply /andP. split. eapply projT2.
destruct f as [rf h1]. cbn. exact h1.
Defined.

Definition tpi_empty (a : elt) : elt.
  refine (tpi_finfun a (existT _ nil _)).
  done.
Defined.

(* create either a abs (u,v) or bot *)
Definition singleton (u v : elt) : elt.
destruct (Raw.le (projT1 v) Raw.bot) eqn:h.
- exact bot.
- exists (Raw.abs (cons (projT1 u,projT1 v) nil)).
  destruct u as [u Vu].
  destruct v as [v Vv].
  have h1: ~~ (Raw.le v Raw.bot).
  { destruct v; try done. } clear h.
  cbn [Raw.valid projT1 bot].
  cbn [Raw.no_bot_result forallb snd].
  rewrite h1.
  cbn [Raw.compatible_fun forallb].
  rewrite Raw.compatible_refl; eauto.
  rewrite Raw.compatible_refl; eauto.
  rewrite Vu. rewrite Vv.
  done.
Defined.


(* --------------- destructors --------------- *)


(* -------------- compatible ----------------- *)

Definition compatible (u : elt) (v : elt) : bool := 
  Raw.compatible (projT1 u) (projT1 v).

(* --------------------- lub ----------------- *)

Definition lub (u : elt) (v : elt) : option elt.
  destruct (Raw.lub (projT1 u) (projT1 v)) as [w|] eqn:E.
  - apply Some. exists w. eapply (@Raw.valid_lub (projT1 u) (projT1 v)). 
    eapply projT2. eapply projT2. assumption.
  - apply None.
Defined.



(* -------------------- le ------------------- *)
Definition le : elt -> elt -> bool := 
  fun u v => (Raw.compatible (projT1 u) (projT1 v) 
           && Raw.le (projT1 u) (projT1 v)).

Definition le_fun (u v : finfun) : bool :=
  Raw.compatible_fun (projT1 u) (projT1 v) 
  && Raw.le_fun (projT1 u) (projT1 v).

Lemma le_refl : forall u, le u u.
move=> [u Vu]. unfold le.
rewrite Raw.le_refl; eauto.
rewrite Raw.compatible_refl; eauto.
Qed.

Lemma le_trans : forall u v w, le u v -> le v w -> le u w.
Proof.
move=> [u Vu] [v Vv] [w Vw].
move=> /andP [Cu Lu] /andP [Cv Lv].
apply /andP. 
cbn [projT1] in *.
split.
eapply Raw.comp_down; eauto.
eapply (@Raw.le_trans u v w); eauto.
Qed.


Lemma le_bot : forall u, le bot u = true.
move=> [ru Vu]. unfold le. cbn. destruct ru.
all: reflexivity.
Qed.

Lemma le_tnat : le tnat tnat = true.
Admitted.

Lemma le_respects : forall (u1 u2 v1 v2 : elt), 
  Raw.eqb (projT1 u1) (projT1 u2) ->
  Raw.eqb (projT1 v1) (projT1 v2) ->
  (le u1 v1) ==> (le u2 v2).
Proof.
  move=> [u1 Vu1] [u2 Vu2] [v1 Vv1] [v2 Vv2]. 
  unfold le. cbn [projT1].
  move=> /andP [Lu1 Lu2] /andP [Lv1 Lv2].
  apply /implyP. move=> /andP [Cuv1 Luv1].
Admitted.


(** -------------- equal ------------- *)

Definition eqb : elt -> elt -> bool := 
  fun u v => le u v && le v u.
Definition eqb_fun (u v : finfun) : Prop := 
  le_fun u v && le_fun v u.

Lemma eqb_bot_inv u : eqb bot u -> u = bot.
Proof.
  intro h. unfold eqb in h. 
  destruct u as [ru Vu].
  cbn in h.
  destruct ru; cbn in h; try done.
  unfold bot.
  f_equal.
  ext.
Qed.

Lemma eqb_zero_inv u : eqb zero u -> u = zero.
Proof. 
  destruct u as [ru Vu]. unfold zero, eqb. cbn.
  destruct ru; cbn; try done.
  intro h.
  f_equal.
  ext.
Qed.

Lemma eqb_succ_inv u v : eqb (succ u) v -> 
                         exists u', v = succ u' /\ eqb u u.
Proof.
  destruct v as [rv Vv]. unfold eqb. cbn.
  destruct rv; cbn; try done.
  unfold Raw.eqb. repeat rewrite Raw.le_succ.
  cbn in Vv.
  exists (existT _ rv Vv).
  f_equal.
  ext.
Admitted.





(** ----------------- application -------------- *)

Definition app (f : elt) (u : elt) : elt.
exists (match (projT1 f) with
    | Raw.abs rf => match (Raw.app rf (projT1 u)) with
                   | Some v => v
                   | None => Raw.bot
                   end
    | _ => Raw.bot
   end).
destruct f as [rf Vf]. destruct u as [ru Vu].
cbn. destruct rf; try done.
cbn in Vf. move: Vf => /andP [Vf _].
fold (Raw.valid_fun l) in Vf.
move: (Raw.valid_app_exists Vf Vu) => [w [EQ Vw]].
rewrite EQ. done.
Defined.


Lemma app_respects : forall (f1 f2 : elt) (u1 u2 : elt), 
  eqb f1 f2 -> 
  eqb u1 u2 ->
  eqb (app f1 u1) (app f2 u2).
Proof.
Admitted.


  Definition is_bot (v : Valid.elt) : bool := 
    match projT1 v with 
    | Raw.bot => true
    | _ => false
    end.

  Definition is_abs (v : Valid.elt) : option Valid.finfun.
    destruct v as [rv Vv]. destruct rv eqn:E.
    1-5: exact None.
    1: exact None.
    cbn in Vv. move: Vv => /andP [Vf _].
    apply Some. exists l. exact Vf.
  Defined.

  Definition abs (f : Valid.nefinfun) : elt.
    exists (Raw.abs (projT1 f)).
    destruct f as [f [Vf Nf]]. cbn.
    apply /andP. split; assumption.
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


End Valid.

#[export] Instance eq_elt_equivalence : Equivalence Valid.eqb.
unfold Valid.eqb.
constructor.
- intros [u Vu].
  cbn.
Admitted.

#[export] Instance eqfun_elt_equivalence : Equivalence Valid.eqb_fun.
Admitted.

Instance Proper_app : Proper (Valid.eqb ==> Valid.eqb ==> Logic.eq) Valid.app.
intros x y Exy. intros w v Ewv.
Admitted.


Module Q.

Definition elt  := quot Valid.eqb. 

Definition finfun := quot Valid.eqb_fun.

Parameter valid_fun : list (elt * elt) -> Prop.

Parameter to_finfun : forall (l : list (elt * elt)), valid_fun l -> finfun.


Definition bot  : elt. exact (to_quot Valid.bot). Defined.
Definition zero : elt. Admitted.
Definition succ : elt -> elt. Admitted.
Definition tpi : elt -> finfun -> elt. Admitted.
Definition abs : finfun -> elt. Admitted.
Definition tuniv : elt. Admitted.
Definition tnat : elt. exact (to_quot Valid.tnat). Defined.

Definition compatible : elt -> elt -> bool. Admitted.
Definition lub : forall u v, compatible u v -> elt. Admitted.
Definition app : finfun -> elt -> elt. Admitted.
Definition le : elt -> elt -> Prop. Admitted.
Definition le_fun : finfun -> finfun -> Prop. Admitted.

Definition complexity : elt -> nat.
Admitted.
  

(* needed for induction principle *)
Definition app_valid (f : list (elt * elt)) (Vf : valid_fun f) (u : elt) : elt. Admitted.

Definition le_fun_valid :
  forall (f g : list (elt * elt)) (Vf : valid_fun f) (Vg : valid_fun g), bool.
Admitted. 
(*  List.forallb (fun '(ui,vi) => lub (app_valid Vg ui) vi) f. *)

Definition eq_fun (f : Valid.elt) (g : Valid.elt) := 
  forall (u : Valid.elt), Valid.eqb (Valid.app f u) (Valid.app g u).


Definition elt_ind : forall (P : elt -> Prop) (Pf : finfun -> Prop), 
    (P bot) ->
    (P zero) -> 
    (forall e, P e -> P (succ e)) ->
    (forall f, Pf f -> P (abs f)) -> 
    (forall e f, P e -> Pf f -> P (tpi e f)) -> 
    P tnat ->
    P tuniv ->
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
    P tuniv ->
    (H : forall l (Vf: valid_fun l), (forall u v, In (u,v) l -> P u * P v) -> Pf (to_finfun Vf))) ->
    (forall f (Vf: valid_fun f) g (Vg: valid_fun g) 
       (to_finfun Vf) = (to_finfun Vg) ->
       (Ef : forall u v, In (u,v) f -> P u * Pv)
       (Eg : forall u v, In (u,v) g -> P u * Pv), 
        (H Vf Ef) = (H Vg Eg)) ->
    forall e, (P e) * forall f, Pf f.
*)


End Q.
