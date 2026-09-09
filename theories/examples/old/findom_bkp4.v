(* Finite domain elements, *)

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
  | tuniv : nat -> elt
  | zero  : elt
  | succ  : elt -> elt
  | tpi   : elt -> list (elt * elt) -> elt
  | abs   : list (elt * elt) -> elt.

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

   NB: original definition is:
   rk(f) = 1 + max(rk(ui), rk(f (ui))) if 
   f = (u1 → v1,...,ul → vl) is minimal and l > 0. 
   Below, we define it over all terms, including invalid ones.

 Properties of rank:
   [rk_lub]    rk(u ∨ v)  = max(rk(u), rk(v)) 
   [rk_app]    rk(f (u)) <= rk(f) for all u
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

Definition compatible_fun (f g : list (elt * elt)) : bool :=
  List.forallb (fun '(ui,vi) => 
     List.forallb (fun '(uj,vj) => 
       (compatible ui uj) ==> (compatible vi vj)) g) f.

Definition lub_fun (f g : list (elt * elt)) : list (elt * elt) := 
  (f ++ g).


(* idempotency? *)
(* associativity? *)
(* commutativity? *)

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




(* For finite functions, when do we have f <= g ?
   We want an extensional definition that says:
   forall x, app f x <= app g x 
   However, we also want a decidable definition. 
   so we look at all of the (ui,vi) in f and see what they do in g.
*) 

(* The termination metric for this definition is (max (rk u) (rk v)). *)
(* NB: cannot use equations as it doesn't support mutual definitions *)
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

Definition app' (f : list (elt * elt)) (u : elt) m : option elt := 
   lub_list (List.map (fun '(ui,vi) => 
                         if le' ui u m then vi else bot) f).
Definition app (f : list (elt * elt)) (u : elt) : option elt := 
   lub_list (List.map (fun '(ui,vi) => 
                         if le ui u then vi else bot) f).

Definition le_fun' f g m := 
  List.forallb (fun '(ui,vi) => 
                  match (app' g ui m) with 
                  | Some v => le' vi v m
                  | None => false
                  end) f.
Definition le_fun f g := 
  List.forallb (fun '(ui,vi) => 
                  match (app g ui) with 
                  | Some v => le vi v 
                  | None => false
                  end) f.


Definition sem_eqb (u v:elt) := le u v && le v u.
Definition sem_eqb_fun f g := le_fun f g && le_fun g f.

(* inductive version of app *)
Fixpoint app_alt (f : list (elt * elt)) (u : elt) : option elt := 
  match f with
  | nil => Some bot
  | ((ui,vi) :: tail) => 
      let appt := app_alt tail u in 
      if (le ui u) then
        match appt with 
        | Some t => lub vi t | None => None end else appt
  end.


(* The level of an element is its maximum universe level *)

Fixpoint level (u : elt) : nat :=
  let fix level_fun f :=
    match f with
      | nil => 0
      | (ui, vi) :: tl => max (max (level ui) (level vi)) (level_fun tl)
    end in
  match u with 
  | bot => 0 
  | tnat => 0
  | tuniv k => k
  | zero => 0
  | succ v => level v
  | tpi a f => max (level a) (level_fun f)
  | abs f => level_fun f
  end.

Fixpoint level_fun (f : list (elt * elt)) :=
 match f with
      | nil => 0
      | (ui, vi) :: tl =>
          max (max (level ui) (level vi)) (level_fun tl)
 end.

(* --------------------------------------------------------- *)

Lemma app_spec : app = app_alt.
Proof.
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
      unfold basics.option_bind. 
      replace (lub bot) with (Some (A:=elt)). 
      2: { smpl extensionality. intro y. reflexivity. } 
      rewrite option_eta.
      reflexivity.
Qed. 

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

Lemma rk_fun_app {f g} : 
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
      destruct (le' ui u m). lia. cbn. lia.
Qed.

(* --------------------------------------------------------- *)

Fixpoint list_ap {A B } (f : list (A -> B)) (x : list A) : list B := 
  List.flat_map (fun x1 => List.flat_map (fun x2 => (x1 x2 :: nil)) x) f.

Definition list_map2 {A B C} (f : A -> B -> C) (x : list A) (y : list B) : list C := 
  list_ap (List.map f x) y.

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

(*
Fixpoint compatible_fun' (f : list (elt * elt)) : Prop :=
  match f with 
  | nil => true
  | (ui,vi) :: ft => 
      compatible_fun' ft /\
      forall u, le ui u -> forall w, app ft u = Some w -> compatible vi w 
  end.

Lemma compatible_fun_compatible_fun' f :
  compatible_fun f f -> compatible_fun' f.
Proof. 
  induction f. done.
  destruct a as [ui vi].
  move=> /andP [/andP [h1 h2]] /forallb_forall h3.
  have Cf: compatible_fun f f.
  { apply /forallb_forall.
    move=> [uj vj] Inj.
    specialize (h3 _ Inj). cbn in h3.
    move: h3 => /andP [h3 h4]. eapply h4.
  } 
  cbn. split; auto.
  move=> u Le w APP.
Abort.
*)

(** * Raw Theory about compatibility *)

(* This is more difficult than it should be. Need to prove
   it by strong induction on the depth of both terms. 
*)
Lemma compatible_sym : forall u v, compatible u v -> compatible v u.
Proof.
  have LEMMA: 
     forall (k : nat) (u v : elt), 
       Init.Nat.max (rk u) (rk v) <= k -> 
       compatible u v -> compatible v u.
  { 
    elim /strong_ind.
    move=> m ih.
    have LEMMA2 : 
          forall f g, (max (rk_fun f) (rk_fun g) < m)%nat -> 
          compatible_fun f g -> compatible_fun g f.
      {
        move=> f g Le2 /forallb_forall h2. 
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
    
    move=>u v Le. 
    destruct u; destruct v; cbn in *; try done.
    all: try match goal with [ H : S _ <=  _ |- _ ] => 
        destruct (le_S_pred H) as [m0 [-> LL]] end.
    - cbn. rewrite PeanoNat.Nat.eqb_sym. done.
    - eauto.
    - fold rk_fun in *.
      move=> /andP [h1 h2].
      apply /andP; split.
      + eapply ih; eauto. lia.
      + move: h2. eapply LEMMA2; eauto. lia.
    - fold rk_fun in *.
      eapply LEMMA2; eauto.
  } 
  move=> u v. eapply LEMMA; eauto.
Qed.  

Lemma compatible_fun_sym : 
  forall f g, compatible_fun f g -> compatible_fun g f.
Proof.
  move=> f g /forallb_forall h2. 
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
  intro x. eapply compatible_sym; eauto. 
  eapply h2.
  eapply compatible_sym; eauto. 
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

Lemma lub_compatible u v w : 
  lub u v = Some w -> compatible u v.
Proof.
  move: v w.
  induction u.
  all: intros v w h.
  all: destruct v; try done.
  all: cbn in h.
  - destruct (n =? n0) eqn:h1; done.
  - destruct (lub u v) eqn:h1; try done.
    cbn. cbn in h. eauto.
  - cbn. destruct (compatible_fun l l0) eqn:h1; try done.
    destruct (lub u v) eqn:h2; try done.
    erewrite IHu; eauto. 
  - cbn.
    destruct (compatible_fun l l0) eqn:h1; try done.
Qed.

Lemma lub_not_compatible u v : 
  lub u v = None -> ~~ (compatible u v).
Proof.
  move: v.
  induction u.
  all: intros v h.
  all: destruct v; try done.
  all: cbn in h.
  - destruct (n =? n0) eqn:h1; try done.
    cbn. rewrite h1. done.
  - destruct (lub u v) eqn:h1; try done.
    cbn. cbn in h. eauto.
  - cbn. destruct (compatible_fun l l0) eqn:h1; try done.
    destruct (lub u v) eqn:h2; try done.
    rewrite negb_and. rewrite IHu. auto. done.
    fold (compatible_fun l l0).
    rewrite negb_and. rewrite h1. cbn. apply orbT.
  - cbn.
    destruct (compatible_fun l l0) eqn:h1; try done.
    fold (compatible_fun l l0).
    rewrite h1. done.
Qed.


Lemma compatible_cons u v l l0 :
  compatible_fun ((u, v) :: l) l0 = 
  forallb (fun '(uj,vj) => compatible u uj ==> compatible v vj) l0 &&
  compatible_fun l l0 .
Proof. 
  cbn. f_equal.
Qed.

Lemma compatible_append : forall f g h, 
      compatible_fun f g -> 
      compatible_fun h f -> 
      compatible_fun h g -> 
      compatible_fun h (f ++ g).
Proof.
  induction f; intros g h.
  - cbn. auto.
  - destruct a as [u v]. cbn.
    move=> /andP [h1 h2].
Admitted.

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
  rewrite compatible_cons in h1.
  move: h1 => /andP [h1 h3]. 
Admitted.

Lemma lub_opt_idL o : lub_opt (Some bot) o = o.
cbn. destruct o; done.
Qed.

Lemma lub_opt_assoc u v w : 
  lub_opt (lub_opt u v) w = lub_opt u (lub_opt v w).
Proof.
  destruct u; destruct v; destruct w; cbn; try done.
  all: destruct (lub e e0) as [w|] eqn:h; cbn; try done.
  all: destruct (lub e0 e1) as [w1|] eqn:h1; cbn; try done.
  - move: e0 e1 w h w1 h1.
    induction e.
    all: move=> e0 e1 w h w1 h1.
    all: cbn.
    all: destruct e0; cbn in *.
    all: inversion h; subst.
    all: inversion h1; subst.
    all: cbn; try done.
    all: destruct e1; try done.
    all: inversion h1; subst; try done.
    + destruct (n =? n0); try done. inversion h. cbn. done.
    + destruct (n =? n0) eqn:E1; try done. inversion h. cbn.
      destruct (n0 =? n1) eqn:E2; try done. inversion h1. rewrite E1.
      rewrite Nat.eqb_eq in E1. rewrite Nat.eqb_eq in E2. subst.
      rewrite Nat.eqb_refl. done.
    + destruct (lub e e0) as [w0|]; try done. inversion h. subst. clear h.
      cbn. done.
    + admit.
    + destruct (compatible_fun l l0) eqn:C; try done.
      destruct (lub e e0) eqn:E; try done. cbn in h. inversion h. cbn. done.
    + destruct (compatible_fun l l0) eqn:C1; try done.
      destruct (compatible_fun l0 l1) eqn:C2; try done.
      destruct (lub e e0) eqn:E; try done.
      destruct (lub e0 e1) eqn:E1; try done.
      cbn in h1. cbn in H1.
      inversion H0. subst. inversion H2. subst.
      rewrite compatible_append_assoc; eauto.
      cbn. rewrite app_assoc.
      destruct (compatible_fun (l ++ l0)); try done.
      move: (IHe _ _ _ E _ E1) => h3. rewrite h3.
      done.
Admitted.
      

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


(* all pairs of elements in l are compatible *)
Definition pairwise_compatible (l : list elt) : bool :=
  forallb (fun x => forallb (fun y => compatible x y) l) l.

Lemma lub_compatible_trans u v w x: 
  lub u v = Some w -> compatible x u -> compatible x v -> compatible x w.
Proof.
  move: v w x.
  induction u.
  all: move => v w x.
  all: destruct v; move=>h; inversion h; try done.
  - destruct (n =? n0) eqn:h1; try done.
    inversion H0. subst. auto.
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

Lemma le_cons u1 v1 l1 l2 : 
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

Lemma rk_app : forall f u w, 
       app f u = Some w -> rk w <= rk_fun f.
Proof.
  intros.
  rewrite <- (app'_app ltac:(reflexivity)) in H.
  eapply rk_app'. eauto.
Qed.


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
*)

Definition no_bot_result (f : list (elt * elt)) := 
  List.forallb (fun p => ~~ (le (snd p) bot)) f.

Definition is_nil {A} (f : list A) := 
  match f with | nil => true | _ => false end.

Fixpoint valid u : bool := 
  let valid_fun f := 
    (compatible_fun f f) &&
    (no_bot_result f) &&
    (~~ is_nil f) &&
    (List.forallb (fun '(ui,vi) => 
                     (valid ui) && (valid vi)) f)
  in
  match u with 
  | abs f => valid_fun f
  | tpi a f => valid a && valid_fun f
  | succ v => valid v
  | _ => true
  end.

Definition valid_fun f := 
    (compatible_fun f f) &&
    (no_bot_result f) &&
    (~~ is_nil f) &&
    (List.forallb (fun '(ui,vi) => (valid ui) && (valid vi)) f).


Lemma valid_fun_compatible f :
  valid_fun f -> compatible_fun f f.
Proof.  move=> /andP [/andP [/andP [h1 h2] h4] h3].  auto. Qed.

Lemma valid_fun_no_bot f :
  valid_fun f -> no_bot_result f.
Proof.  move=> /andP [/andP [/andP [ h1 h2] h4] h3].  auto. Qed.

Lemma valid_fun_nonnil f :
  valid_fun f -> ~~ is_nil f.
Proof.  move=> /andP [/andP [/andP [_ h2] h4] h3].  auto. Qed.

Lemma valid_fun_subterms f :
  valid_fun f -> List.forallb (fun '(ui,vi) => (valid ui) && (valid vi)) f.
Proof. move=> /andP [/andP [h2 h4] h3].  auto. Qed.

Create HintDb valid.
Hint Resolve valid_fun_compatible valid_fun_no_bot valid_fun_nonnil valid_fun_subterms : valid.


(* Compatibility is (only) reflexive for valid terms. *)
Lemma compatible_refl u : valid u -> compatible u u.
Proof.
  induction u.
  all: cbn.
  all: auto.
  - intro h. apply PeanoNat.Nat.eqb_refl.
  - move=> /andP [Vu Vf].   
    apply /andP. split; eauto using valid.    
    eapply valid_fun_compatible; eauto.
  - move=> Vf. 
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

(* If we have a non-bot result from application, there must be 
   some tuple in the function that triggered it. *)
Lemma app_inv g u e : 
  no_bot_result g -> 
  app g u = Some e ->
  ~~ (le e bot) ->
  exists ui, exists vi, List.In (ui,vi) g /\ le ui u.
Proof.
  move: u e.
  rewrite app_spec.
  induction g as [|[ui vi]t].
  all: intros u e NR AA NB.
  - cbn in AA. inversion AA. subst. done.
  - cbn in AA. 
    destruct (le ui u) eqn:h2.
    destruct (app_alt t u) eqn:h4. 2: done.
    exists ui. exists vi. split. left. done. done.
    cbn in NR. move: NR => /andP [ _ NR].
    specialize (IHt _ _ NR AA NB).
    destruct IHt as [uj [vj [h1 h3]]].  
    exists uj. exists vj. split. right. done. done.
Qed.


(* We can append compatible functions together *)
Definition valid_append f g : 
  valid_fun f 
  -> valid_fun g 
  -> compatible_fun f g 
  -> valid_fun (f ++ g).
Proof.
  move=> /andP [/andP [/andP [Cf Nbf] Nf] Vf] 
        /andP [/andP [/andP [Cg Nbg] Ng] Vg] Cfg.
  apply /andP; split. apply /andP; split. apply /andP; split.
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
  - destruct f; try done.
  - clear Cf Cg Cfg Nf Ng.
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



(* --------------------------------------------------------------------- *)

(* all of these lemmas have holes in them.maybe they need to be proven 
   simultaneously??? *)


Lemma le_refl 
  (le_fun_refl : forall f, valid_fun f -> le_fun f f) : 
  forall u, valid u -> le u u.
Proof.
  induction u.
  - cbn. auto.
  - cbn. auto.
  - cbn. move=>h. eapply Nat.eqb_refl.
  - cbn. auto.
  - rewrite le_succ. cbn. auto.
  - rewrite le_tpi. 
    move=> /andP [h1 h2]. fold valid in *. fold (valid_fun l) in h2.
    apply /andP. split; eauto using le_fun_refl.
  - rewrite le_abs. cbn. eauto using le_fun_refl.
Qed.


(* application is total for compatible functions *)
Lemma valid_app_exists
  (bounded_compatible : forall u ui uj, le ui u -> le uj u -> compatible ui uj) 
  f u :
  valid_fun f -> 
  { w | app f u = Some w }.
Proof.
  move=> Vf.
  move: (valid_fun_compatible Vf) => Cf.
  unfold app.
  remember (map (fun '(ui,vi) => if le ui u then vi else bot) f) as l.
  eapply pairwise_lub_exists.
  subst. 
  unfold pairwise_compatible.
  have Cff: compatible_fun f f. exact Cf.
  unfold compatible_fun in Cf.
  move: Cf => /forallb_forall Cf.
  apply /forallb_forall.
  move=> x Inx. 
  rewrite in_map_iff in Inx.
  destruct Inx as [[ui vi] [h1 h2]].
  specialize (Cf _ h2). cbn in Cf.
  move: Cf => /forallb_forall Cf.
  apply /forallb_forall.
  move=> y Iny. 
  rewrite in_map_iff in Iny.
  destruct Iny as [[uj vj] [h3 h4]].
  specialize (Cf _ h4). cbn in Cf.
  destruct (le ui u) eqn:h5; 
  destruct (le uj u) eqn:h6; subst; cbn.
  move: Cf => /implyP Cf.
  eapply Cf.
  eapply bounded_compatible; eauto.
  destruct x; done.
  destruct y; done.
  done.
Qed.

Lemma valid_pairwise 
  (bounded_compatible : forall u ui uj, le ui u -> le uj u -> compatible ui uj) 
  f u : 
  valid_fun f -> 
  pairwise_compatible (map (fun '(ui, vi) => if le ui u then vi else bot) f). 
Proof.
  move=> Vf.
  remember (map (fun '(ui, vi) => if le ui u then vi else bot) f) as g.
  unfold pairwise_compatible.
  apply /forallb_forall. 
  move=> x Ingx.
  have Ingx': In x g. auto.
  apply /forallb_forall.
  move=> y Ingy.
  have Ingy': In y g. auto.
  subst.
  rewrite -> in_map_iff in Ingx'.
  rewrite -> in_map_iff in Ingy'.
  move: Ingx' => [[ux vx] [hx1 hx2]].
  move: Ingy' => [[uy vy] [hy1 hy2]].
  move: (valid_fun_compatible Vf) => /forallb_forall Cf. 
  specialize (Cf _ hx2). cbn in Cf.
  move: Cf => /forallb_forall Cf.
  specialize (Cf _ hy2). cbn in Cf.
  move: Cf => /implyP Cf.
  destruct (le ux u) eqn:h3;
    destruct (le uy u) eqn:h4; subst.
  - eapply Cf.
    eapply bounded_compatible; eauto.
  - destruct x; done.
  - destruct y; done.
  - done.
Qed.

(** le is trainsitive *)
Lemma le_trans : 
  forall u v w, valid u -> valid v -> valid w -> le u v -> le v w -> le u w.
Proof.
  have lemma: 
    forall k, forall u v w, max (rk u) (rk v) <= k ->
                  valid u -> valid v -> valid w -> le u v -> le v w -> le u w.
  {
    elim /strong_ind.
    move=> m ih.
    have lemma2: forall f g h, (max (rk_fun f) (rk_fun g) < m)%nat -> 
                 valid_fun f -> valid_fun g -> valid_fun h ->
                 le_fun f g -> le_fun g h -> le_fun f h.
     { 
      move=> f g h M Vf Vg Vh /forallb_forall h1 /forallb_forall h2.
      apply /forallb_forall. move=> [ui vi] Inf.
      specialize (h1 _ Inf). cbn in h1.
      destruct (app g ui) eqn:APg. 2: done.
      destruct (app_exists_tuple (g := g) (u:=ui) (e:=e)) as [uj [vj h3]]; eauto with valid.
      { destruct e; try done. destruct vi; try done.
        move: (valid_fun_no_bot Vf) => /forallb_forall Vfn.
        specialize (Vfn _ Inf). cbn in Vfn. done. } 
      destruct h3 as [h3 h4].
      specialize (h2 _ h3). cbn in h2.
      destruct (app h uj) eqn:APh.

      destruct (is_bot e) as [->|h4].
      + destruct vi; try done. 
        admit.
      + admit.
     }
    move=> u v w h L1 L2.
    destruct u; destruct v; destruct w; try done.
    - admit.
    - rewrite le_succ in L1. rewrite le_succ in L2.
      cbn in h. rewrite le_succ.
      eapply ih; eauto.
    - rewrite le_tpi in L1. rewrite le_tpi in L2. rewrite le_tpi.
      cbn in h. fold rk_fun in h.
      move: L1 => /andP [L1 L3].
      move: L2 => /andP [L2 L4].
      erewrite ih; eauto. 2: lia.
      cbn.
      eapply lemma2; eauto. lia.
    - rewrite le_abs in L1. rewrite le_abs in L2.
      rewrite le_abs. eapply lemma2; eauto. 
      cbn in h. fold rk_fun in h. lia.
  } 
  intros. eapply lemma; eauto.
Admitted.


Lemma le_fun_extend 
  (le_fun_refl : forall f, valid_fun f -> le_fun f f)
  (bounded_compatible : forall u ui uj, le ui u -> le uj u -> compatible ui uj) 
 :
  forall f g, 
  valid_fun f -> valid_fun g -> compatible_fun f g -> le_fun f (f ++ g).
Proof.
  move=> f g Vf Vg Cfg. 
  unfold le_fun.
  apply /forallb_forall.
  move=> [u v] Inf.
  have [e [h1 h2]] : exists e, app f u = Some e /\ le v e.
  { move: (le_fun_refl _ Vf) => /forallb_forall h. 
    specialize (h _ Inf). cbn in h. destruct (app f u) eqn:h1. eauto. done. } 
  erewrite app_append; try reflexivity. rewrite h1. cbn.
  destruct (valid_app_exists bounded_compatible u Vg) as [ w EQ].
  rewrite EQ.
Admitted.


(** valid functions are reflexive **)
Lemma le_fun_refl : 
  forall f, valid_fun f -> le_fun f f.
Proof.
  move=> f Vf.
  apply /forallb_forall. move=> [u v] Inf.
  unfold app.
  have PC: pairwise_compatible (map (fun '(ui, vi) => if le ui u then vi else bot) f).
  eapply valid_pairwise; eauto.
  
  
    

  Search lub_list.
  
  induction f as [|[ui vi] f']; cbn.
  - done.
  - move=> Vf [h1|h1].
    + inversion h1; subst; clear h1. 
      (* contributes to application *) 
      have Ru: le u u. admit.
      rewrite Ru.
      admit. 
    + (* doesn't *)
      
  destruct (app f u) eqn:h.



  

(* lub is an upper bound for its left argument *)
Lemma lub_le_l : forall u v w, valid u -> valid v -> lub u v = Some w -> le u w = true.
Proof.
  induction u.
  all: move=> v w Vu Vv h.
  all: try solve [destruct w; try done].
  all: try solve [destruct v; inversion h; subst; auto].
  - (* univ *)
    destruct v; inversion h; subst; cbn in *. 
    apply Nat.eqb_refl. 
    destruct (n =? n0) eqn:EQ; try done.
    inversion H0. cbn. apply Nat.eqb_refl.
  - (* succ *)
    destruct v; inversion h; subst; cbn in *. 
    + (* needs le_refl *) eapply le_refl; eauto. 
    + destruct (lub u v) eqn:EQ; try done. 
      inversion H0. subst. cbn. eapply IHu; eauto.
  - (* tpi *)
    destruct v; cbn in h; inversion h; subst.
    + (* needs le_refl *) eapply le_refl; eauto.
    + destruct (compatible_fun l l0) eqn:E. 2: done.
      destruct (lub u v) eqn:E2. 2: done.
      cbn in h. inversion h. 
      move: Vu => /andP [Vu Vl]. 
      move: Vv => /andP [Vv Vl0].
      fold valid in *. fold (valid_fun l) in Vl. fold (valid_fun l0) in Vl0.
      rewrite le_tpi. apply /andP. split; eauto. 
      (* needs le_fun_extend *)
      eapply le_fun_extend; eauto.
  - (* abs *)
    destruct v; cbn in h; inversion h; subst.
    + (* needs le_refl *) eapply le_refl; eauto.
    + destruct (compatible_fun l l0) eqn:E. 2: done.
      cbn in h. inversion h.
      rewrite le_abs. eapply le_fun_extend; eauto.
Qed.

(* If an application is defined, and is not bot, then there 
   must be some tuple in the finite function that contributes to it. 
   If it is bot, then maybe there is no tuple.
   *)
Lemma tuple_exists g u w : app_alt g u = Some w -> w <> bot ->
     exists ui, exists vi, In (ui,vi) g /\ le vi w /\ le ui u.
Proof.
  move:u w.
  induction g.
  cbn. 
  - move=> u w h. inversion h. done.
  - move=> u w h Ne. cbn in h.
    destruct a as [ui vi].
    destruct (app_alt g u) eqn: h1. 2: { destruct (le ui u); done. } 
    destruct (le ui u) eqn: h2.
    + exists ui. exists vi. split; auto. left. done. split.
      eapply lub_le_l. eauto. auto.
    + inversion h. subst. 
      destruct (IHg _ _ h1 Ne) as [uj [vj [h3 h4]]].
      exists uj. exists vj.
      split. right. auto. auto.
Qed. 






Lemma le_trans : 
  forall u v w, valid u -> valid v -> le u v -> forall w,
    
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

(* -------------------------------------------- *)




Lemma valid_app f u w :
  valid_fun f ->
  valid u -> 
  app f u = Some w ->
  valid w.
Admitted.

Lemma app_exists u f 
  (LE_refl : forall v, max (rk v1) (rk v2) <= max (rk u) (rk_fun f) -> le v v) :
  valid_fun f ->
  valid u -> { w | app f u = Some w }.
Proof.
  rewrite app_spec.
  induction f. done.
  destruct a as [ui vi]. cbn.
Admitted.

(* Requires the admitted lemma above, so that we know that 
   the application is defined. *)
Lemma le_refl' : 
  forall k u, rk u <= k -> valid u -> le u u.
Proof.
  elim /strong_ind.
  move=> m ih.
  have lemma: forall f, (rk_fun f < m)%nat -> valid_fun f -> le_fun f f.
  {
    move=> f h Vf.
    have Vff: valid_fun f. exact Vf. 
    unfold valid_fun in Vf.
    move: Vf => /andP [/andP [h1 h3] /forallb_forall h2].
    apply /forallb_forall.
    move=> [ui vi] Inf.  
    specialize (h2 _ Inf). move: h2 => /andP [Vui Vvi].
    destruct (app_exists Vff Vui) as [w EQ].
    rewrite EQ. 
    admit.
  }
  intros u Le.
  destruct u; try solve [reflexivity].
  - cbn. move=> h. eapply Nat.eqb_refl.
  - move=> h. cbn in h. rewrite le_succ; eauto.
  - move=> /andP [h1 h2].  fold valid in h1. fold valid in h2. 
    fold (valid_fun l) in h2. cbn in Le. fold rk_fun in Le. 
    rewrite le_tpi; apply /andP; split; eauto.
    eapply ih; eauto. lia.
    eapply lemma; eauto. lia. 
  - rewrite le_abs. 
    eapply lemma. cbn in Le. fold rk_fun in Le. lia.
Admitted.

Lemma le_refl u : valid u -> le u u.
eapply le_refl'; eauto.
Qed.







(* This isn't quite right yet. *)
Lemma bounded_compatible: forall u ui uj, le ui u -> le uj u -> compatible ui uj.
have lemma:
  forall k, forall u ui uj, max (rk ui) (max (rk uj) (rk u)) <= k ->
                  le ui u -> le uj u -> compatible ui uj.
  {
  elim /strong_ind. move=> m ih.
  have lemma :
    forall f fi fj,
      (max (rk_fun fi) (max (rk_fun fj) (rk_fun f)) < m)%nat ->
                  le_fun fi f -> le_fun fj f -> compatible_fun fi fj.
  {
    move=> f fi fj h hi hj.
    unfold compatible_fun.
    apply /forallb_forall.
    move=> [ui vi] Infi.
    apply /forallb_forall.
    move=> [uj vj] Infj.
    apply /implyP. move=> Ci.
    move: hi => /forallb_forall hi.
    specialize (hi _ Infi). cbn in hi.
    move: hj => /forallb_forall hj.
    specialize (hj _ Infj). cbn in hj.
    destruct (app f ui) eqn:Ai. 2: done.
    destruct (app f uj) eqn:Aj. 2: done.
    move: (rk_app Ai) => rke.
    move: (rk_app Aj) => rke0.
    admit. (* ???? *)
  } 
  move=> u ui uj Le h1 h2.
  destruct ui; destruct uj; destruct u; try done. 
  - cbn. cbn in h1. cbn in h2. admit. (* ok *)
  - cbn in h1. cbn in h2. cbn. eapply ih; eauto. cbn in Le. lia.
  - rewrite le_tpi in h1. rewrite le_tpi in h2. cbn.
    cbn in Le. fold rk_fun in Le.
    move: h1 => /andP [h11 h12].
    move: h2 => /andP [h21 h22].
    apply /andP. split.
    eapply ih; eauto. lia.
    eapply lemma; eauto. lia.
  - rewrite le_abs in h1. rewrite le_abs in h2.
    cbn. cbn in Le. fold rk_fun in Le.
    eapply lemma; eauto. 
  } 
  intros; eapply lemma; eauto.
Admitted.



Lemma le_trans : forall u v w, valid u -> valid v -> valid w -> le u v -> le v w -> le u w.
Proof.
  have lemma: 
    forall k, forall u v w, max (rk u) (rk v) <= k ->
                  valid u -> valid v -> valid w -> le u v -> le v w -> le u w.
  {
    elim /strong_ind.
    move=> m ih.
    have lemma2: forall f g h, (max (rk_fun f) (rk_fun g) < m)%nat -> 
                 valid_fun f -> valid_fun g -> valid_fun h ->
                 le_fun f g -> le_fun g h -> le_fun f h.
     { 
      move=> f g h Vf Vg Vh R /forallb_forall h1 /forallb_forall h2.
      apply /forallb_forall. move=> [ui vi] Inf.
      specialize (h1 _ Inf). cbn in h1.
      destruct (app g ui) eqn:APg. 2: done.
      destruct (is_bot e) as [->|h4].
      + destruct vi; try done. 
        admit.
      + admit.
     }
    move=> u v w h L1 L2.
    destruct u; destruct v; destruct w; try done.
    - admit.
    - rewrite le_succ in L1. rewrite le_succ in L2.
      cbn in h. rewrite le_succ.
      eapply ih; eauto.
    - rewrite le_tpi in L1. rewrite le_tpi in L2. rewrite le_tpi.
      cbn in h. fold rk_fun in h.
      move: L1 => /andP [L1 L3].
      move: L2 => /andP [L2 L4].
      erewrite ih; eauto. 2: lia.
      cbn.
      eapply lemma2; eauto. lia.
    - rewrite le_abs in L1. rewrite le_abs in L2.
      rewrite le_abs. eapply lemma2; eauto. 
      cbn in h. fold rk_fun in h. lia.
  } 
  intros. eapply lemma; eauto.
Admitted.


(* le terms have le ranks: Not TRUE!  [(3,bot)] <= [(1,bot)] *)
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

(* NB: this is not true, but the results are sem_eqb....
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




Lemma lub_list_le : forall w l , lub_list l = Some w -> 
  forall x, In x l -> le x w.
Admitted.




Definition is_bot e : { e = bot } + { e <> bot }.
Proof. destruct e. 
all: try solve [right; done].
left; done.
Qed.



Lemma le_app ui vi f: 
   (forall ui, le ui ui = true) ->
   In (ui, vi) f -> forall w, app f ui = Some w -> le vi w.
Proof.
  move=>Leui. 
  induction f; intro h. done.
  move: h=>[->|h] w.
  - (* found ui,vi *)
    rewrite app_spec. cbn. clear IHf.
    rewrite Leui. 
    destruct (app_alt f ui) eqn:h2. 2: done.
    eapply lub_le_l.
  - (* elsewhere *) 
    move: (IHf h) => ih.
    rewrite app_spec. cbn.
    destruct a as [uj vj].
    destruct (app_alt f ui) eqn:h2. 
    + destruct (le uj ui) eqn:h3. 
      move=> h4. 
      rewrite app_spec in ih.
      specialize (ih _ h2).
      eapply lub_sym in h4.
      eapply lub_le_l in h4.
      
    all: try solve[move=>h4; inversion h4].
    move=>h4.
    rewrite app_spec in IHf.



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
  - intros h Vu. cbn in h. done. 
  - intros h Vu.
    destruct a as [ui vi].
    cbn.
    move: (valid_fun_tail h) => Vf.
    destruct (IHf Vf) as [v IH]; auto.
    rewrite IH.
    destruct (le ui u) eqn:Ei.
Admitted.



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
  


Lemma level_fun_respects
  u (Vu : valid_fun u) v (Vv : valid_fun v) :
  eqb_fun u v -> 
  level_fun u = level_fun v.
Proof.
Admitted.

Lemma level_respects u (Vu : valid u) v (Vv : valid v) : eqb u v -> level u = level v. 
Admitted.



(* Compatible elements have the same universe level???
   No, this is not true b/c bot is compatible 
   with any term.

Lemma compatible_level u v :
  compatible u v -> level u = level v.
Abort.

*)



End Raw.

(* -------------------------------------------------------- *)


Module Valid.

Definition elt := { u : Raw.elt & Raw.valid u }.

(* A finite function is functional and not equivalent to bot *)
Definition finfun := { 
    f : list (Raw.elt * Raw.elt) 
        & Raw.valid_fun f 
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
Definition tuniv (j: nat) : elt. exists (Raw.tuniv j). auto. Defined.
Definition zero : elt. exists Raw.zero. auto. Defined.
Definition succ (u : elt) : elt.
exists (Raw.succ (projT1 u)). cbn. eapply projT2. Defined.
Definition tpi (a : elt) (f : finfun) : elt.
exists (Raw.tpi (projT1 a) (projT1 f)).
cbn. apply /andP. split. eapply projT2.
destruct f as [rf h1]. cbn.
unfold Raw.valid_fun in h1. eapply h1.
Defined.
Definition tabs (f : finfun) : elt.
exists (Raw.abs (projT1 f)).
destruct f as [rf h1].
cbn. eapply h1.
Defined.

Definition le (u v : elt) : bool :=
  Raw.le (projT1 u) (projT1 v).

Definition le_fun (u v : finfun) : bool :=
  Raw.le_fun (projT1 u) (projT1 v).

Definition In_fun (w : elt * elt) (f : finfun) :=
  let '(u,v):= w in 
  List.In ((projT1 u), (projT1 v)) (projT1 f).

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


Inductive wt : elt -> elt -> Prop := 
  | wt_bot a :
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
    wt a (tuniv j) -> 
    (forall ui vi, In_fun (ui,vi) g -> wt ui a /\ wt vi (tuniv j)) ->
    wt (tpi a g) (tuniv j)
  | wt_tabs a f g : 
    (forall ui vi, In_fun (ui,vi) f -> wt ui a /\ wt vi (app g ui)) ->
    wt (tabs f) (tpi a g).

Lemma veq_bot_inv u : veq bot u -> u = bot.
Proof.
  intro h. unfold veq in h. 
  destruct u as [ru Vu].
  cbn in h.
  destruct ru; cbn in h; try done.
  unfold bot.
  f_equal.
  ext.
Qed.

Lemma veq_zero_inv u : veq zero u -> u = zero.
Proof. 
  destruct u as [ru Vu]. unfold zero, veq. cbn.
  destruct ru; cbn; try done.
  intro h.
  f_equal.
  ext.
Qed.

Lemma veq_succ_inv u v : veq (succ u) v -> 
                         exists u', v = succ u' /\ veq u u.
Proof.
  destruct v as [rv Vv]. unfold veq. cbn.
  destruct rv; cbn; try done.
  unfold Raw.eqb. repeat rewrite Raw.le_succ.
  cbn in Vv.
  exists (existT _ rv Vv).
  f_equal.
  ext.
Admitted.

Lemma wt_bot_veq u a b : 
  veq bot u -> veq a b -> wt bot a -> wt u b.
Proof.
  intros e1 e2 h1.
  inversion h1. subst.
Admitted.  


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


Instance Proper_wt : Proper (Valid.veq ==> Valid.veq ==> Logic.eq) Valid.wt.
Proof. 
  intros u1 u2 Equ a1 a2 Eqa.
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
Admitted.
  

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

End Q.
