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
  let rk_fun f := 
    List.list_max (List.map (fun '(ui, vi) => max (rk ui) (rk vi)) f) 
  in
  match u with 
  | bot => 0 
  | tnat => 1
  | tuniv k => 1
  | zero => 1 
  | succ v => 1 + rk v
  | tpi a f => 1 + (max (rk a) (rk_fun f))
  | abs f => 1 + rk_fun f
  end.

Definition rk_fun f := 
   List.list_max (List.map (fun '(ui, vi) => max (rk ui) (rk vi)) f).

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

(* We need a termination metric for this definition... 
   it is (max (rk u) (rk v)). *)
Fixpoint le' (u v : elt) k : bool := 
  let app g u m : option elt := 
    lub_list (List.map (fun '(ui,vi) => 
                          if le' ui u m then vi else bot) g) in
      
  let le_fun f g m := 
    List.forallb (fun '(ui,vi) => match (app g ui m) with 
                               | Some v => lub v vi
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

Definition app (f : list (elt * elt)) (u : elt) : option elt := 
   lub_list (List.map (fun '(ui,vi) => 
                         if le ui u then vi else bot) f).

Definition le_fun f g := 
  List.forallb (fun '(ui,vi) => 
                  match (app g ui) with 
                  | Some v => lub v vi
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
(*
  | b_fun f n : 
    (forall ui vi, List.In (ui,vi) f -> bound ui n /\ bound vi n) ->
    bound_fun f n.
*)

Lemma le_pred : forall m n, S m <= n -> exists j, n = S j /\ (m <= j).
    intros m n Le. 
    inversion Le; subst; eexists; split; eauto; try lia.
Qed.

Lemma rk_fun_fst {a f k} :
  rk_fun (a :: f) <= k -> rk (fst a) <= k.
Proof.
  destruct a. cbn. lia.
Qed.

Lemma rk_fun_snd {a f k} :
  rk_fun (a :: f) <= k -> rk (snd a) <= k.
Proof.
  destruct a. cbn. lia.
Qed.

Lemma rk_fun_tl {a f k} :
  rk_fun (a :: f) <= k -> rk_fun f <= k.
Proof.
  destruct a. cbn. unfold rk_fun. 
  intro h. unfold List.list_max. lia.
Qed.


Fixpoint rk_bounded u {struct u } : forall k, rk u <= k -> bound u k := 
  let bound_fun f : forall k, rk_fun f <= k -> bound_fun f k := 
    list_rec (fun l => forall k, rk_fun l <= k -> bound_fun l k)
      (fun k Le => b_nil k)
      (fun a f bf => fun k le =>
         b_cons
           (@rk_bounded (fst a) k (rk_fun_fst le))  
           (@rk_bounded (snd a) k (rk_fun_snd le))  
           (bf k (rk_fun_tl le))) f
  in
  _ .
  
  have rk_bound_fun f: forall k, rk_fun f <= k -> bound_fun f k.
  {
    induction f.
    - intros k Le.
      eapply b_fun_nil. 
    - intros k Le. 
      destruct a as [ui vi].
      cbn in Le.
      eapply (@b_fun_cons ui vi).
      eapply rk_bounded. lia.
      eapply rk_bounded. lia.
  } 
  intros k Le.
  destruct u.
  all: cbn in Le.
  - eapply b_bot.
  - inversion Le; subst; eapply b_tnat.
  - inversion Le; subst; eapply b_tuniv.
  - inversion Le; subst; eapply b_zero.
  - destruct (le_pred Le) as [m [-> LL]].
    eapply b_succ; eauto.
  - destruct (le_pred Le) as [m [-> LL]].
    eapply b_tpi.
    eapply rk_bounded. lia.
    eapply rk_bound_fun. unfold rk_fun. lia.
  - destruct (le_pred Le) as [m [-> LL]].
    eapply b_abs.
    eapply rk_bound_fun. unfold rk_fun. lia.
Qed.


(* ------------------------------------------------------------------ *)

Fixpoint bounded u k (ACC : Acc Nat.lt k) { struct ACC } : 
  bound u k. 
destruct u.
- econstructor; eauto.
- destruct k.

all: try solve [eapply Some; eapply b_bot].
all: destruct k; [eapply None|]. 
eapply Some; eapply b_tnat.
eapply Some; eapply b_tuniv.
eapply Some; eapply b_zero.
destruct (bounded u k) eqn:h; 
  [eapply Some; econstructor; eauto| eapply None].
destruct (bounded u k) eqn:h; 
  [eapply Some; econstructor; eauto| eapply None].
eapply b_fun.
intros ui vi Ini.
split.


Fixpoint rk_bound u : forall k, rk u <= k -> bound u k.
Proof.
(*
  have rk_bound_fun f: forall k, rk_fun f <= k -> bound_fun f k.
  { 
    intros k Le.
    eapply b_fun. unfold rk_fun in Le.
    intros ui vi Ini.
    move: (@list_max_In _ _ f (ui,vi) k Ini Le) => h.
    split; eapply rk_bound; lia.
  } *)
  intros k Le.
  destruct u.
  all: cbn in Le.
  - eapply b_bot.
  - inversion Le; subst; eapply b_tnat.
  - inversion Le; subst; eapply b_tuniv.
  - inversion Le; subst; eapply b_zero.
  - destruct (le_pred Le) as [m [-> LL]].
    eapply b_succ; eauto.
  - destruct (le_pred Le) as [m [-> LL]].
    eapply b_tpi.
    eapply rk_bound. lia.
    eapply b_fun.
    intros ui vi Ini.
    split. 
    eapply rk_bound. 
    eapply Nat.max_lub_r in LL.


    have h: rk_fun l <= m -> bound_fun l m.
    { 
     clear Le.
     unfold rk_fun.
     intro h.
     eapply b_fun. intros ui vi.
    eapply rk_bound_fun. unfold rk_fun. lia.
  - destruct (le_pred Le) as [m [-> LL]].
    eapply b_abs.
    eapply rk_bound_fun. unfold rk_fun. lia.
Qed.

    induction f. cbn.
    eapply b_fun.
    intros ui vi Ini. inversion Ini.
    eapply b_fun.
    intros ui vi [->|h2].
    - split. cbn.

Lemma strong_ind (P : nat -> Prop) :
  (forall m, (forall k : nat, k < m -> P k)%nat -> P m) -> forall n, P n.
Proof. intro h. 
       induction n as [ n IHn ] using                  (well_founded_induction lt_wf). eauto. Qed.



Lemma compatible_sym u v : 
  compatible u v <-> compatible v u.
Proof.
  remember (max (rk u)(rk v)) as m.
  move: m u v Heqm. 
  elim /strong_ind.
  intros m ih u v ->.
  destruct u; destruct v.
  all: cbn; try done.
  - rewrite PeanoNat.Nat.eqb_sym. done.
  - cbn in ih.
    eapply ih; eauto.
  - cbn in ih.
    move: (ih (max (rk u) (rk v)) ltac:(lia) u v ltac:(eauto)) => h1.
    

Fixpoint compatible_sym u v {struct u} : 
  compatible u v <-> compatible v u.
Proof.
  have compatible_fun_sym: 
    forall f g, compatible_fun f g <-> compatible_fun g f.
  { unfold compatible_fun. 
    move=> f g.
    split.
    move=> /forallb_forall h.
    apply /forallb_forall. 
    move => [uj vj] Inj.
    apply /forallb_forall. 
    move => [ui vi] Ini.
    specialize (h _ Ini). 
    rewrite forallb_forall in h.
    specialize (h _ Inj). cbn in h.
    apply /implyP.
    move: h => /implyP h.
    intro x. rewrite compatible_sym. eapply h. 
    rewrite compatible_sym. done.
    move=> /forallb_forall h.
    apply /forallb_forall. 
    move => [uj vj] Inj.
    apply /forallb_forall. 
    move => [ui vi] Ini.
    specialize (h _ Ini). 
    rewrite forallb_forall in h.
    specialize (h _ Inj). cbn in h.
    apply /implyP.
    move: h => /implyP h.
    intro x. rewrite compatible_sym. eapply h. 
    rewrite compatible_sym. done.
  } 
  all: destruct u; destruct v; cbn; try done.
  - rewrite PeanoNat.Nat.eqb_sym. done.
  - fold (@compatible_fun l l0).
    fold (@compatible_fun l0 l).   
    split.
    move=> /andP [h1 h2]. 
    apply /andP. rewrite compatible_sym. rewrite compatible_fun_sym.
    done.
    move=> /andP [h1 h2]. 
    apply /andP. rewrite compatible_sym. rewrite compatible_fun_sym.
    done.
  - fold (@compatible_fun l l0).
    fold (@compatible_fun l0 l).   
    eapply compatible_fun_sym. 
Admitted.


(* NB: compatibility is not transtive because of bot *)

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
  - destruct (lub u v) eqn:LU;
    destruct compatible_fun eqn:C; 
    inversion h.
    cbn. f_equal.
    apply IHu in LU.
    rewrite map_app. rewrite list_max_app.
    lia.
  - destruct compatible_fun eqn:C. 2: done.
    inversion h. cbn.
    f_equal.
    rewrite map_app. rewrite list_max_app.
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
   
Fixpoint rk_enough u v k: 
  max (rk u) (rk v) <= k -> (le' u v (max (rk u) (rk v))) = (le' u v k).
Proof.
  destruct u.
  all: intro h; cbn in h. 
  all: try solve [destruct k; cbn; auto].
  - destruct k; try lia. cbn.
    destruct v; try done.
    eapply rk_enough. cbn. done.
  - destruct k; try lia. cbn.
    destruct v; try done.
    eapply rk_enough. cbn. done.
  - destruct k; try lia. cbn.
    destruct v; try done.
    eapply rk_enough. cbn. done.
  - destruct k; try lia. cbn.
    destruct v; try done.
    eapply rk_enough. cbn. done.
  - destruct k; try lia. cbn.
    destruct v; try done. cbn in *. lia.
    eapply rk_enough. destruct (rk v); cbn; lia.
  - destruct k; try lia.
    destruct v eqn:EV; try done. cbn in h. lia.
    destruct v eqn:EV; try done. cbn in h.
    cbn.
    rewrite <- (rk_enough u e). 2: lia.
    rewrite <- (rk_enough u e k). 2: lia.
    f_equal.
    eapply forall_ext.
    intros [u1 v1] In1.
    have EQ: lub_list
      (map
         (fun '(ui, vi) =>
          if
           le' ui u1
             (Nat.max (Nat.max (rk u) (List.list_max (map (fun '(ui0, vi0) => Nat.max (rk ui0) (rk vi0)) l)))
                (Nat.max (rk e) (List.list_max (map (fun '(ui0, vi0) => Nat.max (rk ui0) (rk vi0)) l0))))
          then vi
          else bot)
         l0) =   lub_list (map (fun '(ui, vi) => if le' ui u1 k then vi else bot) l0).
    2: rewrite EQ; done.
    f_equal.
    eapply map_ext_in.
    move => [ui vi] Inli.
    apply le_S_n in h.
    remember (fun '(ui0, vi0) => Nat.max (rk ui0) (rk vi0)) as f.
    move: (@list_max_In _ f _ _ k In1) => h1.
    move: (@list_max_In _ f _ _ k Inli) => h2.
    subst f.
    have h3: (max (rk (u1)) (rk (v1))) <= k. eapply h1. lia.
    have h4: max (rk ui) (rk vi) <= k. eapply h2. lia.
    rewrite <- (rk_enough ui u1). 
    rewrite <- (rk_enough ui u1 k). 
    reflexivity.
    lia.
    remember (fun '(ui0, vi0) => Nat.max (rk ui0) (rk vi0)) as f.
    
    have h5: f (u1,v1) <= List.list_max (map f l). eapply list_max_In; eauto.
    have h6: f (ui,vi) <= List.list_max (map f l0). eapply list_max_In; eauto.
    subst.
    lia.
  - 
Admitted.

Lemma le_tpi a f b g : le (tpi a f) (tpi b g) = 
  (le a b) && (le_fun f g).
Proof.
  unfold le.
  change (rk (tpi a f)) with (S (max (rk a) (rk_fun f))).
  change (rk (tpi b g)) with (S (max (rk b) (rk_fun g))).
  cbn.
  f_equal.
  rewrite <- rk_enough. done. lia.
  unfold le_fun.
  unfold app.
  unfold le.
  eapply forall_ext.
  move=> [ui vi] IN.
  enough (lub_list
      (map (fun '(ui0, vi0) => if le' ui0 ui (Nat.max (Nat.max (rk a) (rk_fun f)) 
                                             (Nat.max (rk b) (rk_fun g))) then vi0 else bot)
         g) = 
            lub_list (map (fun '(ui0, vi0) => if le' ui0 ui (Nat.max (rk ui0) (rk ui)) then vi0 else bot) g)) as -> by reflexivity.
  f_equal.
  eapply map_ext_in.
  intros [uj vj] INj.
  rewrite <- rk_enough.
  reflexivity.
  have h1: rk uj <= rk_fun g. 
  { unfold rk_fun. 
    etransitivity. 2: { eapply (@In_list_max _ (uj,vj) g). auto. } 
    lia.
  }
  have h2: rk ui <= rk_fun f. 
  { unfold rk_fun. 
    etransitivity. 2: { eapply (@In_list_max _ (ui,vi) f). auto. } 
    lia.
  } 
  lia.
Qed.

Lemma le_abs f g : le (abs f) (abs g) = le_fun f g.
Admitted.


(* le terms have le ranks *)
Lemma le_rk u v : le u v -> rk u <= rk v.
Proof.
  move: v.
  induction u.
  all: intros v h.
  all: destruct v. 
  all: try solve [cbn; done].
  all: try solve [cbn; lia].
  - rewrite le_succ in h.
    cbn.
    eapply le_n_S.
    eauto.
  - rewrite le_tpi in h.
    move: h => /andP [h1 h2].
    unfold rk. fold rk.
    eapply le_n_S.
    eapply PeanoNat.Nat.max_le_compat; auto.
    eauto.
    (* NEED STRONGER IH *)
Admitted.


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

(* 
   rk(f (u)) < rk(f) for all u.
*)
Lemma app_rk f u w : app f u = Some w -> rk w <= rk_fun f.
Proof.
  rewrite app_spec.
  move: u w.
  induction f; cbn.
  - intros _ w h. inversion h. subst. cbn.
    (* ooops! can't have an empty function *)
    admit.
  - destruct a as [ui vi].
    intros u w h.
    destruct (le ui u) eqn:LE.
    + move: (le_rk LE) => h1.
      destruct (app' f u) eqn:APP; inversion h.
      move: (IHf _ _ APP) => ih.
      move: (lub_rk h) => h2. 
      unfold rk_fun in ih. unfold List.list_max in ih.
      rewrite h2.
      admit.
    + 
Abort.

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

