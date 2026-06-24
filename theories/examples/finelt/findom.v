(* Finite domain elements, raw definitions and properties *)

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

Definition is_bot (a : elt) :bool := 
  match a with 
  | bot => true
  | _ => false
  end.

Definition singleton (a b: elt) : elt :=
  if is_bot b then bot 
  else abs (cons (a,b) nil).

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

Fixpoint _rk_fun (rk : elt -> nat) (f : list (elt*elt)) : nat :=
  match f with
    | nil => 0
    | (ui, vi) :: tl => max (max (rk ui) (rk vi)) (_rk_fun rk tl)
  end.

Fixpoint rk (u : elt) : nat :=
  match u with 
  | bot => 0 
  | tnat => 1
  | tuniv => 1
  | zero => 1 
  | succ v => 1 + rk v
  | tpi a f => 1 + (max (rk a) (_rk_fun rk f))
  | abs f => 1 + _rk_fun rk f
  end.

Notation rk_fun := (_rk_fun rk).

(** Theory about rk *)

Lemma In_rk_fun1 {p l} : In p l -> rk p.1 <= rk_fun l.
induction l as [|[]].
- intro h. inversion h.
- intros [|?%IHl].
  all: subst ; cbn ; lia.
Qed.

Lemma In_rk_fun2 {p l} : In p l -> rk p.2 <= rk_fun l.
induction l as [|[]].
- intro h. inversion h.
- intros [|?%IHl].
  all: subst ; cbn ; lia.
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

Lemma rk_bot_inv e : rk e <= 0 -> e = bot.
Proof.
  intros.
  destruct e ; cbn in * ; solve [reflexivity | lia].
Qed.

(* --------------------------------------------------- *)
(* ** compatibility and lub *)

Definition _compatible_fun (comp : elt -> elt -> bool) (f g : list (elt * elt)) : bool :=
    List.forallb (fun '(ui,vi) => 
      List.forallb (fun '(uj,vj) => 
         (comp ui uj) ==> (comp vi vj)) g) f.

(* We can only compute the lub of compatible functions.
   NB: compatible <-> Comp *)
Fixpoint compatible u v {struct u} : bool := 
  match u , v with 
  | bot , _ => true
  | _ , bot => true
  | tnat , tnat => true
  | zero , zero => true
  | succ u , succ v => compatible u v
  | tpi a f , tpi b g => 
      (compatible a b) && (_compatible_fun compatible f g)
  | abs f , abs g => _compatible_fun compatible f g
  | tuniv , tuniv => true
  | _ , _ => false
  end.

Notation compatible_fun := (_compatible_fun compatible).

Definition coherent_with f '(u, v) := 
  forallb (fun '(uj,vj) => compatible u uj ==> compatible v vj) f.

Lemma compatible_cons_def u v l l' :
  compatible_fun ((u, v) :: l) l' = 
  coherent_with l' (u,v) && compatible_fun l l'.
Proof. 
  cbn. f_equal.
Qed.

(* Two functions are compatible when all pairs in the first are 
   coherent with the second *)
Lemma compatible_fun_spec f g : 
  compatible_fun f g = List.forallb (coherent_with g) f.
Proof. reflexivity. Qed.

(* Least upper bound of two terms *)
(* This function returns garbage ([bot]) on non-compatible elements *)
Fixpoint lub (u v : elt) : elt :=
  match u, v with
  | bot,    v    => v
  | u,      bot  => u
  | tnat,   tnat => tnat
  | zero,   zero => zero
  | tuniv, tuniv => tuniv
  | succ u, succ v => succ (lub u v)
  | tpi a f, tpi b g =>
      if compatible_fun f g
      then tpi (lub a b) (f ++ g)
      else bot
  | abs f, abs g =>
      if compatible_fun f g then (abs (f ++ g)) else bot
  | _, _ => bot
  end.

(* Fold lub over a list of elements. *)
Definition lub_list (xs : list elt) : elt := 
  fold_right lub bot xs.

(* Rank of a lub *)

Lemma rk_lub (u v : elt) : rk (lub u v) <= max (rk u) (rk v).
Proof.
  induction u in v |- * ; destruct v ; cbn in * ; auto.
  all: try solve [lia].
  - specialize (IHu v).
    lia. 
  - destruct compatible_fun eqn:C ; cbn.
    2: lia.
    rewrite rk_fun_append.
    specialize (IHu v). 
    lia.
  - destruct compatible_fun eqn:C ; cbn.
    2: lia.
    now rewrite rk_fun_append.
Qed.

Lemma rk_lub_list xs : rk (lub_list xs) <= List.list_max (List.map rk xs).
Proof.
  induction xs ; cbn.
  1: easy.
  fold (lub_list xs) (List.list_max (map rk xs)).
  etransitivity.
  1: apply rk_lub.
  lia.
Qed.

Lemma rk_ind (P : elt -> Prop) :
  (forall e : elt, (forall e' : elt, rk e' < rk e -> P e')%nat -> P e) ->
  forall e : elt, P e.
Proof.
  intros ih.
  enough (forall (n : nat), forall e, rk e <= n -> P e) as h.
  {
    intros e.
    eapply h.
    reflexivity.
  }
  intros n e hle.
  induction n in e, hle |- *.
  - apply rk_bot_inv in hle as ->.
    apply ih.
    cbn.
    intros.
    lia.
  - apply ih.
    intros.
    apply IHn.
    lia.
Qed.

Lemma rk_ind2 (R : elt -> elt -> Prop) :
  (forall e1 e2 : elt,
    (forall e1' e2' : elt, max (rk e1') (rk e2') < max (rk e1) (rk e2) -> R e1' e2')%nat
    -> R e1 e2) ->
  forall e1 e2 : elt, R e1 e2.
Proof.
  intros ih.
  enough (forall (n : nat), forall e1 e2, max (rk e1) (rk e2) <= n -> R e1 e2) as h.
  {
    intros.
    eapply h.
    reflexivity.
  }
  intros n e1 e2 hle.
  induction n in e1, e2, hle |- *.
  - rewrite (rk_bot_inv e1) ; [lia|..].
    rewrite (rk_bot_inv e2) ; [lia|..].
    apply ih.
    cbn.
    intros.
    lia.
  - apply ih.
    intros.
    apply IHn.
    lia.
Qed.

(* --------------- le ---------------- *)

(* For finite functions, when do we have f <= g ?
   We want an extensional definition that says:
   forall x, app f x <= app g x 
   However, we also want a decidable definition. 
   so we look at all of the (ui,vi) in f and see what they do in g.
*) 

(* ACTUALLY le should be called leb because it is decidable. *)

(* Application, note this only makes sense if the function is a valid representation *)
Equations? _app (f : list (elt*elt)) (u : elt)
  (le_proto : forall x x' : elt, (Init.Nat.max (rk x) (rk x') < 1 + Init.Nat.max (rk_fun f) (rk u))%nat -> bool)
  : elt := 
  @_app f u le := lub_list (map_InP f
    (fun p' hp' => 
        if (le p'.1 u _) then p'.2 else bot)).
Proof.
  pose proof (In_rk_fun1 hp').
  cbn in *.
  lia.
Qed.

Lemma _rk_app f u le : rk (_app f u le) <= rk_fun f.
Proof.
  simp _app.
  etransitivity.
  1: apply rk_lub_list.
  induction f in le |- *.
  - simp map_InP. cbn. auto.
  - destruct a as [ui vi]. simp map_InP ; cbn.
    eapply Nat.max_le_compat.
    + destruct le ; cbn ; lia. 
    + rewrite -/(List.list_max _).
      etransitivity.
      2: eapply (IHf (fun x x' _ => le x x' _)).
      apply ereflexivity.
      do 3 f_equal ; cbn.
      ext.
      erewrite (proof_irrelevance _ (_app_obligation_1 _ _ _ _)).
      reflexivity.
      Unshelve.
      cbn ; lia.
Qed.

Equations _le_fun (f g : list (elt*elt))
  (le_proto : forall x x' : elt, (Init.Nat.max (rk x) (rk x') < 1 + Init.Nat.max (rk_fun f) (rk_fun g))%nat -> bool)
  : bool := 
  @_le_fun f g le :=
    forallb_InP f (fun p hp => le p.2 ((_app g p.1 (fun x x' _ => le x x' _))) _).
Next Obligation.
  pose proof (In_rk_fun1 hp).
  cbn in * ; lia.
Qed.
Next Obligation.
  pose proof (In_rk_fun2 hp).
  cbn in *.
  apply -> Nat.succ_le_mono.
  apply Nat.max_le_compat.
  1: lia.
  apply _rk_app.
Qed.

(* leFinEl *)
#[tactic="idtac"] Equations?
le (u v : elt) : bool by wf (max (rk u) (rk v)) Peano.lt :=
le bot _ := true ;
le tnat tnat := true ;
le zero zero := true ;
le (succ u') (succ v') := le u' v' ;
le (tpi a f) (tpi a' f') := (le a a') && (@_le_fun f f' (fun x x' _ => le x x')) ;
le tuniv tuniv => true ;
le (abs f) (abs f') => @_le_fun f f' le ;
le _ _ := false.
Proof.
  all: cbn ; lia.
Qed.

(* EvalFun *)
Definition app (f : list (elt*elt)) (u : elt) : elt :=
  lub_list (List.map (fun p' => if (le p'.1 u) then p'.2 else bot) f).

Lemma app_eq f u : _app f u (fun x x' => fun=> le x x') = app f u.
Proof.
  simp _app.
  rewrite map_InP_spec.
  reflexivity.
Qed.

Lemma rk_app f u : rk (app f u) <= rk_fun f.
Proof.
  rewrite -app_eq.
  apply _rk_app.
Qed.

(* leFun *)
Definition le_fun (f f' : list (elt*elt)) : bool := 
  forallb (fun p => le p.2 (app f' p.1)) f.

Lemma le_fun_eq f f' :
  _le_fun f f' (fun x x' : elt => fun=> le x x') = le_fun f f'.
Proof.
  simp _le_fun.
  unfold le_fun.
  rewrite forallb_InP_spec.
  f_equal.
  ext.
  rewrite app_eq //.
Qed.

Lemma le_abs f f' : le (abs f) (abs f') = le_fun f f'.
Proof.
  simp le.
  now apply le_fun_eq. 
Qed.

Remove Hints le_graph_equation_43 : le.
Hint Rewrite le_abs : le.

Lemma le_pi a f a' f' :
  le (tpi a f) (tpi a' f') = (le a a') && (le_fun f f').
Proof.
  simp le.
  now rewrite le_fun_eq.
Qed.

Remove Hints le_graph_equation_35 : le.
Hint Rewrite le_pi : le.

(* strict less than (still decidable) *)
Definition lt u v := le u v && ~~(le v u).

(* decidable equality *)
Definition eqb (u v:elt) := le u v && le v u.
Definition eqb_fun f g := le_fun f g && le_fun g f.

(* inductive version of app *)
Create HintDb app.

Lemma app_nil_eq : forall f, app nil f = bot.
reflexivity. Qed.

Hint Rewrite app_nil_eq : app.

Lemma app_cons_eq ui vi f u :
  app (cons (ui,vi) f) u = if (le ui u) then lub vi (app f u) else (app f u).
Proof. 
  intros.
  rewrite /app /=.
  destruct le ;reflexivity.
Qed.

Hint Rewrite app_cons_eq : app.

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

(** * Raw Theory about compatibility *)

(* These properties are proven by strong induction on 
   rank of u and v.
*)

Lemma compatible_bot u : compatible u bot.
Proof.
  by destruct u.
Qed.

Lemma _compatible_fun_sym f g 
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
  intro x. eapply ih; eauto.
  1: cbn in * ; lia.
  eapply h2.
  eapply ih; eauto. 
  move: (In_rk_fun1 Inl) => Leuj. 
  move: (In_rk_fun1 Inl0) => Leui. 
  cbn in * ; lia.
Qed.

Lemma compatible_sym (u v : elt) :
  compatible u v -> compatible v u.
Proof.
    pattern u, v.
    apply rk_ind2 ; clear u v.
    move=> u v ih.
    destruct u; destruct v; cbn in *; try done.
    - eauto.
    - fold rk_fun in *.
      move=> /andP [h1 h2].
      apply /andP; split.
      + eapply ih; eauto. lia.
      + move: h2. eapply _compatible_fun_sym; eauto.
        intros. 
        eapply ih ; auto.
        lia.
    - eapply _compatible_fun_sym; eauto.
      intros.
      eapply ih ; auto.
      lia.
Qed.

Lemma compatible_fun_sym : 
  forall f g, compatible_fun f g -> compatible_fun g f.
Proof. 
  intros f g.
  eapply _compatible_fun_sym; eauto.
  intros.
  eapply compatible_sym; eauto.
Qed.

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
Lemma compatible_lub u v x: 
  compatible x u -> 
  compatible x v -> 
  compatible x (lub u v).
Proof.
  intros hu hv.
  induction u in x, v, hu, hv |- *.
  1: now cbn.
  all: destruct v ; cbn in * ; try easy.
  all: destruct x ; cbn in * ; try done.
  - easy.
  - move: hu hv => /andP [??] /andP [??].
    destruct (compatible_fun l _) eqn:h1.
    2: done.
    apply /andP ; split ; [easy|].
    now eapply compatible_append.
  - destruct (compatible_fun l _) eqn:h1. 2: done.
    now eapply compatible_append.
Qed.

Lemma compatible_append_inv f g g' :
  compatible_fun f (g ++ g') ->
  compatible_fun f g && compatible_fun f g'.
Proof.
  move => /forallb_forall hcomp.
  apply /andP ; split.
  all: apply /forallb_forall => [[ui vi]] hin /=.
  all: move: (hcomp _ hin).
  all: rewrite forallb_app => /andP [??] //.
Qed.

Lemma compatible_lub_inv u v x:
  compatible u v ->
  compatible x (lub u v) ->
  compatible x u.
Proof.
  intros h h'.
  induction u in x, v, h, h' |- *.
  1: apply compatible_bot.
  all: destruct v ; cbn in * ; try done.
  - now destruct x.
  - move: h => /andP [hu hfun].
    rewrite hfun in h'.
    destruct x ; cbn in * ; try easy.
    move: h' => /andP [? hfun'].
    apply /andP ; split.
    1: eauto.
    move: hfun' => /compatible_append_inv /andP [??] //.
  - rewrite h in h'.
    destruct x ; cbn in * ; try easy.
    move: h' => /compatible_append_inv /andP [??] //.
Qed.

Lemma compatible_append_assoc l l' l'' :
  compatible_fun l l' -> 
  compatible_fun l' l'' ->
  compatible_fun l (l' ++ l'') = compatible_fun (l ++ l') l''.
Proof.
  intros h h'.
  induction l as [|[u v]] in l', l'', h, h' |- *.
  - cbn -[compatible_fun].
    rewrite h'. done.
  - rewrite /= -!/compatible_fun.
    rewrite compatible_cons_def in h.
    move: h => /andP [hco ?].
    unfold coherent_with in hco. 
    rewrite IHl // forallb_app hco //=.
Qed.

Lemma lub_bot_l e : lub bot e = e.
reflexivity.
Qed.

Lemma lub_bot_r e : lub e bot = e.
destruct e; reflexivity.
Qed.

(* Sup-assoc *)
Lemma lub_assoc u v w :
  compatible u v -> 
  compatible v w ->
  lub (lub u v) w = lub u (lub v w).
Proof.
  intros h h'.
  induction u in h, h', v, w |- *.
  all: cbn.
  1: easy.
  all: destruct v, w ; cbn in * ; try done.
  - now f_equal.
  - now destruct compatible_fun.
  - move: h h' => /andP [? h] /andP [? h'].
    rewrite h h' /= compatible_append_assoc //= app_assoc IHu //.
  - rewrite h lub_bot_r //. 
  - rewrite h h' //= compatible_append_assoc // app_assoc //.
Qed.

Lemma compatible_app f u v :
  forallb (fun '(ui,vi) => le ui u ==> (compatible v vi)) f ->
  compatible v (app f u).
Proof.
  intros h.
  induction f as [|[]].
  1: by apply compatible_bot.
  rewrite app_cons_eq.
  move: h => /= /andP [??].
  destruct le => /=.
  2: easy.
  now apply compatible_lub.
Qed.

(* If [u] is below [v], then they are compatible.
  Needs [v] to be valid, and will be later subsumed
  by the characterisation of compatibility as having a
  lub, but it is useful to have at this stage. *)

Lemma _compatible_le_fun f f' g 
  (ih : forall (u u' v : elt), 
      max (rk u') (max (rk u) (rk v)) <= (max (rk_fun f') (max (rk_fun f) (rk_fun g))) ->
      compatible u v -> le u' u -> compatible u' v) :
  compatible_fun f g -> le_fun f' f -> compatible_fun f' g.
Proof.
  move=> /forallb_forall hcomp.
  move=> /forallb_forall hle.
  apply /forallb_forall.
  intros [ui' vi'] Inl.
  apply /forallb_forall.
  intros [uj vj] Inl'.
  move: (In_rk_fun1 Inl) (In_rk_fun2 Inl) (In_rk_fun1 Inl') (In_rk_fun2 Inl') => /= ????. 
  apply /implyP => ?.
  move: (hle _ Inl) => /= ?.
  move: (rk_app f ui') => ?.
  eapply ih ; tea.
  1: lia.
  apply compatible_sym, compatible_app.
  apply forallb_forall => [[ui vi] hin].
  apply /implyP => ?.
  move: (hcomp _ hin) => /= /forallb_forall /(_ _ Inl') /implyP hcomp'.
  apply compatible_sym, hcomp'.
  eapply ih ; eauto.
  move: (In_rk_fun1 hin) => /= ?.
  lia.
Qed.

Lemma compatible_le u u' v :
  compatible u v ->
  le u' u ->
  compatible u' v.
Proof.
  enough (forall k u u' v,
    max (rk u) (max (rk u') (rk v)) <= k ->
    compatible u v ->
    le u' u ->
    compatible u' v) as h.
  {
    eapply h.
    reflexivity.
  }
  clear.
  intros k.
  pattern k.
  apply strong_ind.
  intros ? ih u u' v hrk hcomp hle.
  destruct u, u', v ; cbn in *; try done.
  - simp le in hle.
    eapply ih ; eauto.
  - simp le in hle.
    move: hcomp hle => /andP [??] /andP [??].
    apply /andP ; split.
    + eapply ih ; eauto.
      lia.
    + eapply _compatible_le_fun ; eauto.
      intros.
      eapply ih ; tea.
      lia.
  - simp le in hle.
    eapply _compatible_le_fun ; eauto.
    intros.
    eapply ih ; tea.
    lia.
Qed.

(* --------------------------------------------------------- *)

(** * Raw Theory about le (totality, reduction) *)

Lemma le_bot' v : le bot v.
 destruct v; reflexivity.
Qed.

Hint Rewrite le_bot' : le.

Lemma le_fun_nil l :
  le_fun nil l.
Proof. reflexivity. Qed.

Lemma le_fun_cons u1 v1 l1 l2 : 
 le_fun ((u1, v1) :: l1) l2 = le v1 (app l2 u1) && le_fun l1 l2.
Proof.
  reflexivity.
Qed.

Hint Rewrite le_fun_nil le_fun_cons : le.

Lemma le_fun_extend g h f : 
    le_fun g f ->
    le_fun h f ->
    le_fun (g ++ h) f.
Proof.
  induction g as [|[u v]g].
  all: move=> Lg Lh.
  - done.
  - cbn. simp le in Lg |- *.
    move: Lg => /andP [-> ?] /=.
    by apply IHg.
Qed.

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

Definition _valid_fun valid f :=
    (compatible_fun f f) &&
    (no_bot_result f) &&
    (List.forallb (fun '(ui,vi) => (valid ui) && (valid vi)) f).

Fixpoint valid u : bool :=
  match u with
  | abs f => _valid_fun valid f && ~~ is_nil f
  | tpi a f => valid a && (_valid_fun valid f)
  | succ v => valid v
  | _ => true
  end.

Notation valid_fun := (_valid_fun valid).

Record CFT u v f : Prop :=
  mkCFT { key_valid  : valid u;
          val_valid  : valid v;
          val_nbot   : ~~ le v bot;
          compat     : coherent_with f (u,v)
    }.

Lemma valid_fun_compatible f :
  valid_fun f -> compatible_fun f f.
Proof.  move=> /andP [/andP [h1 h2] h3]. auto. Qed.

Lemma valid_fun_no_bot f :
  valid_fun f -> no_bot_result f.
Proof.  move=> /andP [/andP [h1 h2] h3]. auto. Qed.

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
       move: h3 => /andP [h3 h5] //.
Qed.

(* Under the new definition of [valid], non-emptiness is part of
   [valid (abs f)] but not of [valid_fun f]. The non-emptiness lemma
   for [abs] takes [valid (abs f)] directly. *)

Lemma valid_abs_nonnil f :
  valid (abs f) -> ~~ is_nil f.
Proof. cbn. move=> /andP [_ h]. exact h. Qed.

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
  key_valid val_valid compat
  valid_fun_compatible valid_fun_no_bot valid_abs_nonnil valid_fun_subterms : valid.

(* Compatibility is reflexive (only) for valid terms. *)
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

Corollary le_compatible u v :
  valid v -> le u v -> compatible u v.
Proof.
  intros.
  eapply compatible_le ; tea.
  by apply compatible_refl.
Qed.

Corollary le_compatible_pair u1 u2 v: 
   valid v -> le u1 v -> le u2 v -> compatible u1 u2.
Proof.
   move=> Vw Lu Lv.
   eapply compatible_le; eauto.
   eapply compatible_sym.
   eapply le_compatible; eauto.
Qed.


(* The head and tail of a valid function are valid *)

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

Lemma valid_fun_in u v f :
  In (u,v) f -> valid_fun f -> CFT u v f.
Proof.
  move => hin hf.
  induction f as [|[]] in hin, hf |- *.
  1: done.
  move: hf => /dup [hf] /andP [/andP [h1 h2] h3].
  rewrite compatible_cons_def in h1.
  cbn in *.
  move: h1 => /andP [/andP [h1 h9] h5].
  move: h2 => /andP [h2 h8].
  move: h3 => /andP [/andP [h3 h7] h6].
  rewrite /= in hin.
  destruct hin as [[= -> ->]|hin].
  - constructor; eauto.
    cbn.
    by apply /andP.
  - edestruct IHf ; eauto using valid_fun_tail.
    split ; eauto.
    rewrite /=.
    apply /andP ; split ; auto.
    apply /implyP => ?.
    now move: h5 => /forallb_forall /(_ _ hin) /= /andP [/implyP] ? _.
Qed.

Corollary valid_fun_key_valid u v f :
  In (u,v) f -> valid_fun f -> valid u.
Proof.
  intros hin hval.
  now edestruct valid_fun_in.
Qed.

Corollary valid_fun_val_valid u v f :
  In (u,v) f -> valid_fun f -> valid v.
Proof.
  intros hin hval.
  now edestruct valid_fun_in.
Qed.

Hint Resolve valid_fun_head valid_fun_tail valid_fun_key_valid valid_fun_val_valid : valid.

(* Lemmas about valid terms *)

Lemma no_bot_result_app f g :
  no_bot_result f ->
  no_bot_result g ->
  no_bot_result (f ++ g).
Proof.
  intros Nf Ng.
  unfold no_bot_result in *.
  rewrite forallb_app.
  apply /andP. done.
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
Lemma valid_lub u v :
  compatible u v -> valid u -> valid v -> valid (lub u v).
Proof.
  intros hcomp Vu Vv.
  induction u in v, hcomp, Vu, Vv |- *.
  all: cbn in *.
  1: easy.
  all: destruct v ; cbn in * ; try easy.
  - move: hcomp => /andP [?] /dup [? ->] /=.
    move: Vu => /andP [??].
    move: Vv => /andP [??].
    rewrite IHu //=.
    by apply valid_append.
  - rewrite hcomp /=.
    move: Vu => /andP [??]. move: Vv => /andP [??].
    cbn.
    apply /andP ; split.
    1: by apply valid_append.
    by destruct l.
Qed.

Lemma valid_app f u :
  valid_fun f -> valid u -> valid (app f u).
Proof.
  intros hf hu.
  induction f as [|[ui vi]f] in hf |- *.
  1: easy.
  simp app.
  destruct (le ui u) eqn:? ; cbn ; eauto with valid.
  apply valid_lub ; eauto with valid.
  apply compatible_app.
  apply valid_fun_compatible in hf.
  cbn in hf.
  move: hf => /andP [] /andP [_ ] /forallb_forall hf _.
  apply /forallb_forall => x /hf.
  destruct x.
  move => /implyP hcomp.
  apply /implyP => ?.
  eapply hcomp ; eauto.
  eapply le_compatible_pair ; eauto.
Qed.

Hint Resolve valid_app valid_lub : valid.

(* ------------------------------------------------------- *)

(** * Inversion lemmas for le *)

Lemma le_bot_inv u : le u bot -> u = bot.
Proof.
  by destruct u ; simp le.
Qed.

Definition le_inv_view (u u' : elt) : Type :=
  match u with
  | bot => True
  | tnat => u' = tnat
  | zero => u' = zero
  | tuniv => u' = tuniv
  | succ v => {v' & (u' = succ v') * (le u u') }
  | tpi a b => {a' & { b' & (u' = tpi a' b') * ((le a a') * (le_fun b b')) }}
  | abs f => {f' & (u' = abs f') * (le_fun f f') }
  end.

Lemma le_inv u v : le u v -> le_inv_view u v.
Proof.
  destruct u, v ; simp le ; cbn.
  all: try done.
  - move => ?.
    eexists ; repeat split.
    now simp le.
  - move => /andP [??].
    by do 2 eexists ; repeat split.
  - move => ?.
    by eexists ; repeat split.
Qed.

(* ------------------------------------------------------- *)

Lemma le_fun_app_bot f u : 
  le_fun f nil -> (app f u) = bot.
Proof.
  induction f as [|[ui vi] f]. cbn. done.
  rewrite le_fun_cons => /andP [].
  rewrite app_nil_eq => /le_bot_inv -> ?.
  rewrite app_cons_eq IHf //.
  case: le => //.
Qed.

Lemma le_fun_nil_compatible f g : 
  le_fun f nil -> compatible_fun f g.
Proof.
  move => /forallb_forall hf.
  apply /forallb_forall => [[ui vi]] hin /=.
  move: (hf _ hin) => /=.
  rewrite app_nil_eq => /le_bot_inv ->.
  apply /forallb_forall => [[??]] _ //=.
  apply /implybT.
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

Lemma compatible_coherent_app f ui vi u :
  compatible ui u ->
  coherent_with f (ui,vi) ->
  compatible vi (app f u).
Proof.
  move => hcomp /forallb_forall hcoh.
  apply compatible_app, forallb_forall => [[uj vj]] hin /=.
  apply /implyP => hle.
  move: (hcoh _ hin) => /= /implyP hcomp'.
  eapply hcomp', compatible_sym, compatible_le ; tea.
  by apply compatible_sym.
Qed.

Lemma app_compatible f u ui vi :
  valid_fun f -> 
  valid u ->
  In (ui,vi) f ->
  le ui u ->
  compatible vi (app f u).
Proof.
  intros hf hu hin hle.
  induction f as [|[]] in ui, vi, hf, hin, hle |- *.
  1: by apply compatible_bot.
  rewrite app_cons_eq.
  move: hf => /= /dup [] /valid_fun_tail ? /valid_fun_head cft.
  move: hin => /= [[= ??]|] ; subst.
  - rewrite hle.
    apply compatible_lub.
    1: now eapply compatible_refl, val_valid.
    eapply compatible_coherent_app ; tea.
    2: now eapply compat.
    by apply le_compatible.
  - move => hin.
    assert (compatible vi (app f u)) by (now eapply IHf).
    destruct (le e u) eqn:?.
    2: done.
    apply compatible_lub.
    2: done.
    move: cft => /compat /forallb_forall /(_ _ hin) /implyP hcomp.
    eapply compatible_sym, hcomp; tea.
    now eapply le_compatible_pair.
Qed.

(*
-----------------------------------------------------------------------
-- Coherent-Sup and Coherent-EvalFun
------------------------------------------------------------------------

-- comp-EvalFun: evaluations of compatible functions at the same point
-- are compatible.
*)

Lemma compatible_fun_app f g u :
  valid u ->
  compatible_fun f g ->
  compatible (app f u) (app g u).
Proof.
  intros hval hcomp.
  induction f as [|[ui vi]] in g, hcomp |- *.
  1: easy.
  rewrite app_cons_eq.
  rewrite compatible_cons_def in hcomp.
  move: hcomp => /andP [??].
  destruct (le ui u) eqn:?.
  2: easy.
  apply compatible_sym, compatible_lub.
  2: now apply compatible_sym.
  eapply compatible_sym, compatible_coherent_app ; tea.
  by apply le_compatible.
Qed.

(* 
 EvalFun-append-eq : (k h : FinFun) (xi : FinEl) ->
    CompFun k h -> CoherentFunTail k -> Coherent xi ->
    Eq (EvalFun (append k h) xi) (Sup (EvalFun k xi) (EvalFun h xi))
*)
Lemma app_append_eq f g u :
  valid u ->
  valid_fun f ->
  compatible_fun f g ->
  app (f ++ g) u = lub (app f u) (app g u).
Proof.
  intros hu hval hcomp.
  induction f as [|[]] in hval, hcomp |- *.
  1: easy.
  rewrite /= !app_cons_eq.
  rewrite compatible_cons_def in hcomp.
  move: hcomp => /andP [??].
  move: hval => /dup [] /valid_fun_tail ? /valid_fun_head ?.
  destruct (le e u) eqn:?.
  2: easy.
  rewrite IHf // lub_assoc //.
  - eapply compatible_coherent_app ; tea.
    2: now eapply compat.
    now apply le_compatible.
  - now apply compatible_fun_app.
Qed.

Lemma compatible_arg_app f u u' :
  valid_fun f ->
  valid u ->
  valid u' ->
  compatible u u' ->
  compatible (app f u) (app f u').
Proof.
  intros hval hu hu' hcomp.
  induction f as [|[ui vi]] in hval |- *.
  1: easy.
  rewrite !app_cons_eq.
  move: hval => /dup [] /valid_fun_tail ? /valid_fun_head ?.
  assert (compatible vi vi)
    by now eapply compatible_refl, val_valid.
  assert ((le ui u) -> compatible vi (app f u')).
  {
    intros ?.
    eapply compatible_coherent_app.
    2: now apply compat.
    now eapply compatible_le. 
  }
  assert ((le ui u') -> compatible vi (app f u)).
  {
    intros ?.
    eapply compatible_coherent_app.
    2: now apply compat.
    apply compatible_sym in hcomp.
    now eapply compatible_le. 
  }
  all: destruct (le ui u') eqn:?.
  all: destruct (le ui u) eqn:?.
  all: try apply compatible_lub.
  all: try apply compatible_sym, compatible_lub, compatible_sym.
  all: auto.
  all: now apply compatible_sym.
Qed.

(*
------------------------------------------------------------------------
-- Part 7i: Order-theoretic lemmas
--
*)

Module OTL.

Record OrderTheoreticLemmas k := MkLemmas {
  (* reflexivity *)
  le_refl : forall a, rk a <= k -> valid a -> le a a ;

  (* lub is an upper bound *)
  le_lub_left : forall a b, max (rk a) (rk b) <= k -> 
    compatible a b -> valid a -> valid b -> le a (lub a b) ;

  le_lub_right : forall a b, max (rk a) (rk b) <= k -> 
    compatible a b -> valid a -> valid b -> le b (lub a b) ;

  (* le is transitive *)
  le_trans : forall u v w, max (max (rk u) (rk v)) (rk w) <= k -> 
     valid u -> valid v -> valid w -> le u v -> le v w -> le u w ;

  (* le is a least upper bound *)
  le_sup_lub : forall u v w, 
      max (max (rk u) (rk v)) (rk w) <= k ->
      le u w -> le v w -> le (lub u v) w ;
}.

Lemma le_lub_le_left k (ih : OrderTheoreticLemmas k) a a' b :
  max (max (rk a) (rk a')) (rk b) <= k -> 
  compatible a' b -> valid a -> valid a' -> valid b -> le a a' -> le a (lub a' b).
Proof.
  intros.
  move: (rk_lub a' b) => ?.
  eapply le_trans ; cycle -2 ; try solve [eauto with valid|lia].
  1: eapply le_lub_left ; try solve [eauto with valid|lia].
Qed.

Lemma le_lub_le_right k (ih : OrderTheoreticLemmas k) a b b' :
  max (rk a) (max (rk b) (rk b')) <= k -> 
  compatible a b' -> valid a -> valid b -> valid b' -> le b b' -> le b (lub a b').
Proof.
  intros.
  move: (rk_lub a b') => ?.
  eapply le_trans ; cycle -2 ; try solve [eauto with valid|lia].
  1: eapply le_lub_right ; try solve [eauto with valid|lia].
Qed.

Section FunLemmas.
  Context k (ih : OrderTheoreticLemmas k).

  (* First prove all of the lemmas about finfun's assuming 
    the top-level lemmas.
  *)
  Lemma le_fun_mono_arg f u1 u2 :
    (max (max (rk_fun f) (rk u1)) (rk u2)) <= k -> 
    valid_fun f -> valid u1 -> valid u2 -> le u1 u2 ->
    le (app f u1) (app f u2).
  Proof.
    intros hrk hf h1 h2 hle.
    induction f as [|[u v] f] in hrk, hf |- *.
    1: easy.
    rewrite !app_cons_eq.
    cbn in *.
    move: hf => /dup [] /valid_fun_head [????] /valid_fun_tail ?.
    move: (rk_app f u1) (rk_app f u2) => ??.
    assert (le u u2 -> compatible v (app f u2)).
    {
      move => ?.
      eapply compatible_coherent_app ; tea.
      now apply le_compatible.
    }
    assert (le u u2 -> le (app f u1) (lub v (app f u2))).
    {
      intros hle'.
      eapply le_lub_le_right ; try solve [eauto with valid|lia].
      by apply IHf ; tea ; lia.
    }
    destruct (le u u1) eqn:?.
    - assert (le u u2) as hle'
        by (eapply le_trans ; cycle -2 ; tea ; lia).
      rewrite hle'.
      eapply le_sup_lub ; eauto.
      1: move: (rk_lub v (app f u2)) => ? ; lia.
      eapply le_lub_left ; solve [eauto with valid|lia].
    - destruct (le u u2) eqn:?.
      1: auto.
      apply IHf ; solve [eauto with valid|lia].
  Qed.

  Lemma le_fun_mono f g u :
    (max (max (rk_fun f) (rk_fun g)) (rk u) <= k) -> 
    valid_fun f -> valid_fun g -> 
    le_fun f g -> valid u ->
    le (app f u) (app g u).
  Proof.
    move => hrk hf hg hle hu.
    induction f as [|[ui vi] f].
    1: easy.
    cbn in hrk.
    move: hf => /dup [] /valid_fun_head ? /valid_fun_tail ?.
    move: hle => /= /andP [??].
    simp app.
    move: (rk_app f u) (rk_app g u) (rk_app g ui) => ???.
    destruct (le ui u) eqn:?.
    2: eapply IHf ; eauto ; lia.
    eapply le_sup_lub ; eauto.
    1: lia.
    2: eapply IHf ; eauto ; lia.
    eapply le_trans ; cycle -2 ; eauto with valid.
    2: lia.
    eapply le_fun_mono_arg ; eauto with valid.
    lia.
  Qed.

  Lemma le_in_app f ui vi :
    (rk_fun f) <= k ->
    valid_fun f ->
    In (ui,vi) f ->
    le vi (app f ui).
  Proof.
    intros hrk hval hin.
    induction f as [|[u v]].
    1: done.
    move: (rk_app f ui) (In_rk_fun2 hin) (rk_lub v (app f ui)) => ???.
    simp app.
    cbn in *.
    move: hin => /= [[= ? ?]|] ; subst.
    - simp app.
      erewrite le_refl ; try solve [eauto with valid|lia].
      eapply le_lub_le_left ; try solve [eauto with valid|lia].
      2: eapply le_refl ; solve [eauto with valid|lia].
      eapply compatible_coherent_app.
      1: now apply compatible_refl ; eauto with valid.
      now apply compat, valid_fun_head.
    - intros.
      assert (le vi (app f ui))
        by (apply IHf ; solve [eauto with valid|lia]).
      destruct (le u ui) eqn:? ; try easy.
      eapply le_lub_le_right ; try solve [eauto with valid|lia].
      eapply compatible_coherent_app ; tea.
      1: now apply le_compatible ; eauto with valid.
      now eapply compat, valid_fun_head.
  Qed.

  Lemma le_fun_refl f :
    (rk_fun f <= k) -> valid_fun f -> le_fun f f.
  Proof.
    move => hrk hval.
    apply /forallb_forall => [[ui vi] ?] /=.
    now apply le_in_app.
  Qed.

  Lemma le_fun_extend_left f g :
    (max (rk_fun f) (rk_fun g) <= k) ->
    valid_fun f -> valid_fun g
    -> compatible_fun f g -> le_fun f (f ++ g).
  Proof.
    move => hrk hf hg hcomp.
    apply /forallb_forall => [[ui vi] hin] /=.
    rewrite app_append_eq ; eauto with valid.
    move: (rk_app f ui) (rk_app g ui) (In_rk_fun2 hin) => /= ???.
    eapply le_lub_le_left ; try solve [eauto with valid|lia].
    1: now apply compatible_fun_app ; eauto with valid.
    apply le_in_app ; eauto ; lia.
  Qed.

  Lemma le_fun_extend_right f g :
    (max (rk_fun f) (rk_fun g) <= k) ->
    valid_fun f -> valid_fun g
    -> compatible_fun f g -> le_fun g (f ++ g).
  Proof.
    move => hrk hf hg hcomp.
    apply /forallb_forall => [[ui vi] hin] /=.
    rewrite app_append_eq ; eauto with valid.
    move: (rk_app f ui) (rk_app g ui) (In_rk_fun2 hin) => /= ???.
    eapply le_lub_le_right ; try solve [eauto with valid|lia].
    1: now apply compatible_fun_app ; eauto with valid.
    apply le_in_app ; eauto ; lia.
  Qed.

  Lemma le_fun_trans f g h : 
    (max (max (rk_fun f) (rk_fun g)) (rk_fun h) <= k) -> 
    valid_fun f -> valid_fun g -> valid_fun h ->
    le_fun f g -> le_fun g h -> le_fun f h.
  Proof.
    move => hrk hf hg hh hle hle'.
    apply /forallb_forall => [[ui vi] hin] /=.
    move: (rk_app g ui) (rk_app h ui) (In_rk_fun1 hin) (In_rk_fun2 hin) => /= ????.
    eapply le_trans with (v := app g ui) ; cycle -2 ; try solve [eauto with valid|lia].
    1: by move: hle => /forallb_forall /(_ _ hin) //=.
    apply le_fun_mono ; try solve [eauto with valid|lia].
  Qed.

End FunLemmas.

Lemma OTLs : forall k, OrderTheoreticLemmas k.
Proof.
  elim /strong_ind.
  move=> k ih.
  constructor.

  - (* le_refl *)
    move=> a RK Va.
    destruct a.
    all: cbn in *.
    all: try solve [cbn;done].
    all: simp le.
    2,3: move: Va => /andP [??].
    2: apply /andP ; split.
    all: first [eapply le_refl | eapply le_fun_refl] ; eauto ; lia.

  - (* le_lub_left *)
    move => a b RK hcomp ha hb.
    destruct a ; cbn in *.
    1: easy.
    all: destruct b ; cbn in * ; try done.
    4: move: hcomp => /andP [? hcomp].
    4,6: rewrite hcomp.
    all: simp le.
    all: erewrite ?le_refl, ?le_fun_refl ; try solve [eauto with valid | lia].
    all: erewrite ?le_lub_left, ?le_fun_extend_left ; solve [eauto with valid | lia].

  - (* le_lub_left *)
    move => a b RK hcomp ha hb.
    destruct a ; cbn in *.
    all: destruct b ; cbn in * ; try done.
    5: move: hcomp => /andP [? hcomp].
    5,6: rewrite hcomp.
    all: simp le.
    all: erewrite ?le_refl, ?le_fun_refl ; try solve [eauto with valid | lia].
    all: erewrite ?le_lub_right, ?le_fun_extend_right ; solve [eauto with valid | lia].

  - (* le_trans *)
    move=> u v w RK Vu Vv Vw L1 L2.
    destruct u; destruct v; destruct w;
      try solve [cbn in L1; cbn in L2; done].
    all: simp le in * ; cbn in *.
    all: repeat (match goal with H : is_true (_ && _) |- _ => move: H => /andP [??] end).
    all: erewrite ?le_trans ; cycle -2 ; eauto ; try lia => /=.
    all: erewrite le_fun_trans ; cycle -2 ; eauto ; lia.

  - (* le_sup_lub *)
    move=> u v w RK LE1 LE2.
    destruct u; destruct v; try done.
    + apply le_inv in LE1. move: LE1 => [v1 [EQ1 LE1]].
      apply le_inv in LE2. move: LE2 => [v2 [EQ2 LE2]].
      subst.
      inversion EQ2 ; subst ; clear EQ2.
      cbn in * ; simp le in *.
      eapply le_sup_lub ; eauto.
    + apply le_inv in LE1. move: LE1 => [v1 [f1 [EQ1 [LE1 LF1]]]].
      apply le_inv in LE2. move: LE2 => [v2 [f2 [EQ2 [LE2 LF2]]]].
      subst.
      inversion EQ2 ; subst ; clear EQ2.
      cbn in *.
      destruct (compatible_fun l l0) eqn:?. 2:done.
      simp le.
      apply /andP. split.
      2: now eapply le_fun_extend.
      eapply le_sup_lub ; eauto ; lia.
    + apply le_inv in LE1. move: LE1 => [f1 [EQ1 LF1]].
      apply le_inv in LE2. move: LE2 => [f2 [EQ2 LF2]].
      subst.
      inversion EQ2 ; subst ; clear EQ2.
      cbn in *.
      destruct (compatible_fun l l0) eqn:?. 2: done.
      simp le.
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
  compatible a b -> valid a -> valid b -> le a (lub a b).
Proof. 
  eapply OTL.le_lub_left. eapply OTL.OTLs. reflexivity.
Qed.

Lemma le_lub_right a b :
     compatible a b -> valid a -> valid b -> le b (lub a b).
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

Lemma le_sup_lub u v w :
  le u w -> le v w -> le (lub u v) w.
Proof.
  eapply OTL.le_sup_lub. 2: reflexivity.
  eapply OTL.OTLs.
Qed.

Lemma le_fun_mono f g u :
  valid_fun f -> valid_fun g ->
  le_fun f g -> valid u ->
  le (app f u) (app g u).
Proof.
  eapply OTL.le_fun_mono. eapply OTL.OTLs. reflexivity.
Qed.

Lemma le_fun_mono_arg f u v :
  valid_fun f -> valid u -> valid v -> le u v ->
  le (app f u) (app f v).
Proof.
  eapply OTL.le_fun_mono_arg.
  eapply OTL.OTLs. reflexivity.
Qed.

Lemma le_in_app f ui vi :
  valid_fun f -> In (ui,vi) f -> le vi (app f ui).
Proof.
  eapply OTL.le_in_app.
  eapply OTL.OTLs. reflexivity.
Qed.

Lemma le_app f ui vi u :
  valid_fun f ->
  valid u ->
  In (ui,vi) f -> le ui u -> le vi (app f u).
Proof.
  intros.
  eapply le_trans ; cycle -2.
  1: now apply le_in_app.
  2-4: eauto with valid.
  apply le_fun_mono_arg ; eauto with valid.
Qed.

(* ----------------------------------------------------- *)
(* Some corollaries of OTLs *)


(* extensional introduction form for le_fun *)
Lemma le_fun_ext f1 f2 :
  valid_fun f1 ->
  valid_fun f2 ->
  (forall u, valid u -> le (app f1 u) (app f2 u)) ->
  le_fun f1 f2.
Proof.
  move=> Vf1 Vf2 h.
  apply /forallb_forall.
  move=> [ui vi] In /=.
  eapply le_trans ; cycle -2 ; eauto with valid.
  now apply le_in_app.
Qed.

(* extract app f u and its validity when valid (tpi a f) holds. *)
Lemma app_tpi_valid a f u :
  valid (tpi a f) -> valid u ->
  valid (app f u).
Proof.
  move=> V Vu.
  move: V => /= /andP [_ Vf].
  now eapply valid_app.
Qed.

Hint Immediate app_tpi_valid : valid.


(** Characterising compatibility *)

Lemma compatibilityP u v :
  valid u -> valid v ->
  compatible u v <-> exists w, (valid w /\ le u w /\ le v w).
Proof.
  intros ; split.
  - intros.
    exists (lub u v).
    repeat split.
    + auto with valid.
    + now apply le_lub_left.
    + now apply le_lub_right.
  - move => [w [? [??]]].
    now eapply le_compatible_pair.
Qed.

(* ------------------ inversion for lub -------------------- *)

(** * inversion lemmas for lub *)

Lemma lub_bot_inv u v :
  compatible u v ->
  lub u v = bot -> u = bot /\ v = bot.
Proof.
  destruct u; destruct v; rewrite /= ; try done.
  - move => /andP [_ ->] //=.
  - move => -> //=.
Qed.
Lemma lub_bot_inv_r u v :
  compatible u v -> lub u v = bot -> v = bot.
Proof. move=> ? /lub_bot_inv [] //. Qed.
Lemma lub_bot_inv_l u v : 
  compatible u v -> lub u v = bot -> u = bot.
Proof. move=> ? /lub_bot_inv [] //. Qed.

Lemma lub_tuniv_inv (u v:elt) :
  ~~ is_bot u -> ~~ is_bot v ->
  lub u v = tuniv ->
  (u = tuniv) /\ (v = tuniv).
Proof.
  destruct u; destruct v; cbn in * ; try done.
  all: by destruct compatible_fun.
Qed.

Lemma lub_tnat_inv (u v:elt) :
  ~~ is_bot u -> ~~ is_bot v ->
  lub u v = tnat ->
  (u = tnat) /\ (v = tnat).
Proof.
  destruct u; destruct v; cbn in * ; try done.
  all: by destruct compatible_fun.
Qed.

Lemma lub_zero_inv (u v:elt) :
  ~~ is_bot u -> ~~ is_bot v ->
  lub u v = zero ->
  (u = zero) /\ (v = zero).
Proof.
  destruct u; destruct v; cbn ; try done.
  all: by destruct compatible_fun.
Qed.

Lemma lub_succ_inv (u v w:elt) :
  ~~ is_bot u -> ~~ is_bot v ->
  lub u v = (succ w) ->
  { u1 & { v1 & (u = succ u1) * ((v = succ v1)
       * (lub u1 v1 = w))}}.
Proof.
  destruct u; destruct v; cbn ; try done.
  2-3: by destruct compatible_fun.
  move => _ _ [= <-].
  eauto.
Qed.

Lemma lub_tpi_inv (u v:elt) a f :
  ~~ is_bot u -> ~~ is_bot v ->
  lub u v = (tpi a f) ->
  { a1 & { f1 & { a2 & { f2 & (u = tpi a1 f1) * ((v = tpi a2 f2)
       * ((lub a1 a2 = a)
       * (f = f1 ++ f2)%list))}}}}.
Proof.
  destruct u; destruct v; cbn ; try done.
  2: by destruct compatible_fun.
  destruct compatible_fun ; try done.
  move => _ _ [= <- <-].
  eauto 10.
Qed.

Lemma lub_abs_inv (u v:elt) (f : list (elt * elt)) :
  ~~ is_bot u -> ~~ is_bot v ->
  lub u v = (abs f) ->
  { f1 & { f2 & (u = abs f1) * ((v = abs f2)
       * (f = f1 ++ f2))}}.
Proof.
  destruct u; destruct v; cbn ; try done.
  1: by destruct compatible_fun.
  destruct compatible_fun ; try done.
  move => _ _ [= <-].
  eauto 10.
Qed.

(* ------------------------------------------------------------ *)
(* Inversion lemmas for le *)

Lemma le_tnat_inv u : le tnat u -> u = tnat.
Proof. by destruct u ; simp le. Qed.

Lemma le_zero_inv u : le zero u -> u = zero.
Proof. by destruct u ; simp le. Qed.

Lemma le_tuniv_inv u : le tuniv u -> u = tuniv.
Proof. by destruct u ; simp le. Qed.

Lemma le_succ_inv {u v} : le (succ u) v -> { w & (v = succ w) * (le u w) }.
Proof. destruct v ; simp le ; try done. move=> h. by exists v. Qed.

Lemma le_tpi_inv {v u f} :
  le (tpi u f) v -> { w & { g & (v = tpi w g) * ((le u w) * (le_fun f g)) }}.
Proof. destruct v ; simp le ; try done. move=> /andP [??]. by exists v, l. Qed.

Lemma le_abs_inv {v f} :
  le (abs f) v -> { g & (v = abs g) * (le_fun f g) }.
Proof. destruct v ; simp le ; try done. move=> h. by exists l. Qed.

Lemma valid_tpi_intro a f :
  valid a -> valid_fun f -> valid (tpi a f).
Proof. move=> Va Vf. by apply /andP. Qed.

Lemma valid_tpi_inv a f :
  valid (tpi a f) -> valid a /\ valid_fun f.
Proof. by move=> /andP [??]. Qed.

(* Inductive (cons-recursive) version of [app], now total. *)
Fixpoint app_alt (f : list (elt * elt)) (u : elt) : elt :=
  match f with
  | nil => bot
  | (ui,vi) :: tail =>
      if le ui u then lub vi (app_alt tail u) else app_alt tail u
  end.

Lemma app_spec : app = app_alt.
Proof.
  ext. induction x as [|[ui vi] f].
  - ext. reflexivity.
  - ext. rewrite app_cons_eq. cbn [app_alt]. rewrite IHf //.
Qed.

(* [app f u] always exists now; this restates that it is valid. *)
Lemma valid_app_exists {f u} :
  valid_fun f -> valid u -> { w & (app f u = w) * valid w }.
Proof. move=> Vf Vu. exists (app f u). split=> //. by apply valid_app. Qed.

Lemma app_tpi_exists a f u :
  valid (tpi a f) -> valid u -> { t & (app f u = t) * valid t }.
Proof. move=> V Vu. exists (app f u). split=> //. exact (@app_tpi_valid a f u V Vu). Qed.

(* The old [compatible_app_inv] split a successful application of an
   appended function. In the total setting this is [app_append_eq]. *)
Lemma compatible_app_inv f g u :
  valid_fun f -> valid_fun g -> valid u -> compatible_fun f g ->
  { vf & { vg & (app f u = vf) * ((app g u = vg) * (lub vf vg = app (f ++ g) u)) }}.
Proof.
  move=> Vf Vg Vu C.
  exists (app f u), (app g u). split=> //. split=> //.
  symmetry. by apply app_append_eq.
Qed.

(* Rewrite lemmas for [le] on [succ]/[tpi] (the old names). *)
Lemma le_succ u v : le (succ u) (succ v) = le u v.
Proof. by simp le. Qed.

Lemma le_tpi a f b g :
  le (tpi a f) (tpi b g) = (le a b) && (le_fun f g).
Proof. apply le_pi. Qed.

(* Downward closure of compatibility (the old [comp_down]); this is
   just [compatible_le] with the arguments reordered. *)
Lemma comp_down u u' v : le u u' -> compatible u' v -> compatible u v.
Proof. move=> LE C. eapply compatible_le ; eassumption. Qed.

Lemma comp_down_pair u1 u2 v1 v2 :
  compatible v1 v2 -> le u1 v1 -> le u2 v2 -> compatible u1 u2.
Proof.
  move=> C LE1 LE2.
  eapply comp_down ; [exact LE1|].
  apply compatible_sym. eapply comp_down ; [exact LE2|].
  by apply compatible_sym.
Qed.

Lemma le_valid_compatible u v : valid v -> le u v -> compatible u v.
Proof. exact: le_compatible. Qed.

Lemma le_valid_compatible_pair u1 u2 v :
  valid v -> le u1 v -> le u2 v -> compatible u1 u2.
Proof. exact: le_compatible_pair. Qed.

Lemma valid_elt x y f :
  valid_fun f -> In (x,y) f -> valid x /\ valid y.
Proof. move=> Vf In. exact: (valid_fun_subterms_prop f Vf x y In). Qed.

(* The old [valid_app_compatible]: [app f u] exists, is valid, and is
   coherent with every entry of [f] whose key is below [u]. *)
Lemma valid_app_compatible f u :
  valid_fun f -> valid u ->
  { w & (app f u = w) * (valid w *
         (forall ui vi, In (ui,vi) f -> compatible ui u && le ui u -> compatible vi w)) }.
Proof.
  move=> Vf Vu. exists (app f u). split=> //. split.
  - by apply valid_app.
  - move=> ui vi In /andP [_ Le]. eapply app_compatible ; eassumption.
Qed.

Lemma lub_up_left : 
  forall {a a0 b}, 
    valid a0 -> valid a -> valid b ->
    compatible a0 b ->
    le a a0 -> le (lub a b) (lub a0 b).
Proof.
  move=> a a0 b Va0 Va Vb Cab LEa.
  move: (le_sup_lub a b (lub a0 b)) => h1.
  eapply h1.
  - eapply (@le_trans _ a0); eauto.
    eapply valid_lub; eauto.
    eapply le_lub_left; eauto.
  - eapply le_lub_right; eauto.
Qed.  

Lemma lub_up_right : 
  forall {a b b0}, 
    valid a -> valid b -> valid b0 ->
    compatible a b0 ->
    le b b0 -> le (lub a b) (lub a b0).
Proof.
  move=> a b b0 Va Vb Vb0 Cab LEb.
  move: (le_sup_lub a b (lub a b0)) => h1.
  eapply h1.
  eapply le_lub_left; eauto.
  eapply (@le_trans _ b0); eauto.    
  eapply valid_lub; eauto.
  eapply le_lub_right; eauto.
Qed.  


Lemma lub_up : 
  forall {a b c a0 b0 c0}, 
    valid a -> valid b ->
    valid a0 -> valid b0 ->
    compatible a0 b0 ->
    le a a0 -> le b b0 -> lub a b = c -> lub a0 b0 = c0 -> le c c0.
Proof.
  intros a b c a0 b0 c0 Va Vb Va0 Vb0 C0 La Lb LUB LUB0.
  subst.
  have Cab : compatible a b. eapply comp_down_pair; eauto.
  have Ca0 : compatible a0 b. 
  eapply (comp_down_pair _ _ _ _ C0); eauto. eapply le_refl; eauto.
  have Vc: valid (lub a b). eapply valid_lub; eauto.
  have V1: valid (lub a0 b). eapply valid_lub; eauto.
  have Vc0: valid (lub a0 b0). eapply valid_lub; eauto.
  eapply (@le_trans _ (lub a0 b)); eauto. 
  eapply lub_up_left; eauto.
  eapply lub_up_right; eauto.
Qed.


(* ------------------------------------------------------------ *)
(* Restore the implicit-argument behaviour that these lemmas had
   under the old [Set Implicit Arguments] (removed from this file).
   Placed at the end of the module so that the explicit-argument
   uses in the proofs above are unaffected; only downstream callers
   (which apply these lemmas positionally to hypotheses) see the
   implicit form. *)

Arguments le_refl {a}.
Arguments le_lub_left {a b}.
Arguments le_lub_right {a b}.
Arguments le_trans {u v w}.
Arguments le_fun_trans {u v w}.
Arguments le_sup_lub {u v w}.
Arguments le_fun_mono {f g u}.
Arguments le_fun_mono_arg {f u v}.
Arguments le_in_app {f ui vi}.
Arguments le_app {f ui vi u}.
Arguments le_fun_refl {f}.
Arguments le_fun_ext {f1 f2}.

Arguments valid_fun_tail {u v f}.
Arguments valid_fun_head {u v f}.
Arguments valid_fun_in {u v f}.
Arguments valid_append {f g}.
Arguments valid_lub {u v}.
Arguments valid_app {f u}.
Arguments app_tpi_valid {a f u}.
Arguments valid_fun_compatible {f}.
Arguments valid_fun_no_bot {f}.
Arguments no_bot_result_app {f g}.

Arguments compatible_sym {u v}.
Arguments compatible_refl {u}.
Arguments compatible_lub {u v x}.
Arguments compatible_le {u u' v}.
Arguments le_compatible {u v}.
Arguments le_compatible_pair {u1 u2 v}.
Arguments compatible_app {f u v}.
Arguments compatible_coherent_app {f ui vi u}.
Arguments compatible_fun_app {f g u}.
Arguments compatible_arg_app {f u u'}.
Arguments app_append_eq {f g u}.
Arguments le_fun_extend {g h f}.
Arguments comp_down {u u' v}.
Arguments comp_down_pair {u1 u2 v1 v2}.
Arguments le_valid_compatible {u v}.
Arguments le_valid_compatible_pair {u1 u2 v}.
Arguments valid_elt {x y f}.
Arguments valid_app_compatible {f u}.
Arguments compatible_app_inv {f g u}.

End Raw.

(* -------------------------------------------------------- *)


