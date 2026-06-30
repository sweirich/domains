(** * utils.v: Utilities for working with finite domains *)
From Stdlib Require Import Relations List Program
     ssreflect ssrfun ssrbool.
Unset Printing Implicit Defensive.

Require Import smpl.Smpl.

From Stdlib Require Import Classes.RelationClasses Classes.Morphisms Lia Arith.


Require Import utils.all.
Require Import categories.all.
Require Import preord.

From Equations Require Import Equations.

Arguments svalP [_ _] _.

(** This file collects general-purpose lemmas and combinators that are not
    specific to the model construction: list/fold utilities, strong
    induction, and a handful of [In]-proof-carrying recursors (built with the
    Equations plugin) that the rest of the development uses to define
    structurally-recursive functions over lists whose bodies need a membership
    witness. *)

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

(** Folding a monoid over an append splits into the fold of each part: given a
    unit [base] and an associative [op], [fold_right] distributes over [++]. *)
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


(** Strong (course-of-values) induction on [nat], derived from well-founded
    induction on [<]. *)
Lemma strong_ind (P : nat -> Prop) :
  (forall m, (forall k : nat, k < m -> P k)%nat -> P m) -> forall n, P n.
Proof. intro h. 
       induction n as [ n IHn ] using    
        (well_founded_induction lt_wf). eauto. Qed.


(** An arbitrary reflexive relation relates equal terms *)
Lemma ereflexivity {A} {R} `{Reflexive A R} {x y} :
  x = y -> R x y.
Proof.
  intros ->.
  reflexivity.
Qed.

(** ** Proof-carrying recursors (Equations library)

    The following combinators are like [forallb], [map], and an [option]
    eliminator, except the per-element predicate/function additionally receives
    a proof that the element belongs to the original list (resp. that the
    option is [Some]). This is what lets us define well-typed functions over
    lists of value edges where the body needs to know the element is a genuine
    member. Each comes with a [_spec] lemma showing it agrees with the ordinary
    version when the witness is ignored. *)

Section AllInP.
  Context {A : Type}.

  (** [forallb] whose test may use a membership proof for its argument. *)
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

  (** [map] whose mapping function may use a membership proof for its argument. *)
  Equations map_InP (l : list A) (f : forall x : A, In x l -> B) : list B :=
  @map_InP nil _ := nil;
  @map_InP (cons x xs) f := cons (f x _) (map_InP xs (fun x inx => f x _)).
End MapInP.

Lemma map_InP_spec {A B : Type} (f : A -> B) (l : list A) :
  map_InP l (fun (x : A) _ => f x) = List.map f l.
Proof.
  remember (fun (x : A) _ => f x) as g.
  funelim (map_InP l g) => //; simpl. f_equal. cbn in H.
  now rewrite (H f0).
Qed.

(** Test the contents of an [option], where the test receives a proof that the
    option is [Some]; [None] is treated as [false]. *)
Equations onSomeP {A} (o : option A) (p : forall (x : A), o = Some x -> bool) : bool :=
  @onSomeP _ (Some a) p := p a _ ;
  @onSomeP _ None _ => false.

Arguments onSomeP {_} _ _.

Lemma onSomeP_spec {A : Type} (o : option A) (f : A -> bool) :
  onSomeP o (fun (x : A) _ => f x) = match o with | Some v => f v | None => false end.
Proof.
  remember (fun (x : A) _ => f x) as g.
  funelim (onSomeP o g) => //.
Qed.

(** Dependent [if] on a boolean: each branch additionally receives a proof of
    the discriminee's value, so the branches can use [b = true] / [b = false]. *)
Definition if_eq {T : Type} (b : bool) (btrue : b = true -> T) (bfalse : b = false -> T) : T :=
  match b as x return (b = x) -> T with
  | true => btrue
  | false => bfalse
  end eq_refl.