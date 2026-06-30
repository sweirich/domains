(** * raw_validity.v: The value PER ([Val] / [EqVal])

    (See [MIN/Validity/*.agda].)

    This file builds the logical relation tying *syntactic* terms/types to
    *semantic* well-typed finite elements.  The two mutually-recursive
    relations are:
    - [Val k Γ M A u a (h : wt u a)] — the term [M : A] is related to the
      member [u : a] of type [a];
    - [EqVal k Γ M N A u a h] — the convertible terms [M], [N] are related to
      [u : a].

    They are defined by recursion on a global *fuel* [k] (an over-approximation
    of element rank): as [u]/[a] become more defined, the set of related
    syntactic terms shrinks; at [u = bot] every well-scoped term qualifies.  The
    Π cases quantify over [Selection]s of the function graph (see
    [selection.v]).  [ValTy]/[EqValTy] are the type-level companions.

    The major results, exported at the end of the file, are:
    - [fuel_stable] — the relations are independent of fuel above the rank, so
      the fuel index can be ignored (the rank-relative [Stage] of the Agda dev);
    - [EqVal_sym], [EqVal_trans], [EqValTy_sym], [EqValTy_trans] — [EqVal] is a
      PER;
    - [Val_EqVal] (reflexivity), [Val_Bot]/[EqVal_Bot];
    - head-expansion/contraction and up/down/restrict monotonicity lemmas;
    - [fwd_per_all] — the forward (type-transport) package. *)

(* See Validity.agda *)

From Stdlib Require Import Relations List Program
     ssreflect ssrfun ssrbool.
From Stdlib Require Import Classes.RelationClasses 
  Classes.Morphisms Lia Arith.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Require Import smpl.Smpl.
Require Import utils.all.

Require Import syntax.syntax.
Require Import syntax.typing.
Require Import syntax.relations.
Require Import syntax.reduction.

From Stdlib Require Import ProofIrrelevance.
Require Import finelt.utils.
Require Import findom.
Require Import types.
Require Import selection.

Import SyntaxNotations.
Import SubstNotations.
Import typing.Notations.

Open Scope syntax_scope.

Import Raw.

(** * Logical relations between syntactic terms/types and well-typed finite elements. *)

(* The main relations are: 

      Val Γ M A (h: wt u a) : relating syntactically typeable terms to finite elements u 
 
      EqVal Γ M N A (h: wt u a) : relating syntactically convertible terms M and N to finite elements u.

   This relation is defined by recursion on the rank of the finite elements
   and their types. As u and a are "more defined" the set of syntactic
   elements in the relation becomes smaller.  To begin, when u is bot, these relations
   include all well-scoped terms M and A.  *)


(** This module defines the "edge" operations that the [Val]/[EqVal] fixpoints
    use in their Π and universe cases (the Selection-indexed type and value
    edges [PiEdge*]/[PiApp*], the type companions [ValTy]/[EqValTy], and the
    Π-bundles [ValPi]/[EqValPi]).  Each is parameterized by the two main
    fixpoints [Val] and [EqVal] *instantiated at a smaller rank*, so that the
    recursion in [Val]/[EqVal] below stays structurally decreasing in the
    fuel. *)
Module Rec.

(* This module defines various helper operations on the logical
   relation. Each of these operations is parameterized by the
   two main fixpoints (Val and EqVal) which has been instantiated at
   a specific rank. *)

Section Helpers.
      
Variable 
   Val   : forall {n} (Γ : Ctx n),
              Tm n -> Tm n -> forall u a, wt u a -> Prop.
Variable
   EqVal : forall {n} (Γ : Ctx n),
              Tm n -> Tm n -> Tm n -> forall u a, wt u a -> Prop.

(* Unary analog of [PiEdgeEq]: for any argument [N] in the relation at
   the domain [A], the codomain [B[N..]] is in the relation (as a type). *)
(* The *type* edges, like the value edges below, quantify over a
   [Selection f u v] of the codomain (type) graph [f]: [u] is the key-join
   (typed at the domain [b]), [v] the value-join (typed at [tuniv], since
   [f]'s values are codomains in the universe -- witness [wt_Selection_codU]).
   The argument [N] is in the relation at [u]; the codomain type [B[N..]] is
   in the relation (as a type) at the value-join [v].  Selection-bounding the
   argument (key rank < rk_fun f < rk (tpi b f)) is what makes the fuel
   stability of these edges provable.  Mirrors Agda's [PiEdgeVal2P]. *)
Definition PiEdgeVal {n} (Γ : Ctx n)
  (A : Tm n) (B : Tm (S n)) (b: elt) (f : list (elt * elt))
  (h : wt (tpi b f) tuniv) :=
  forall u v (Sel : Selection f u v) (WT : wt u b)
      (N : Tm n),
      typing Γ N A ->
      (* take a related argument *)
      Val Γ N A WT ->
      (* to a related result *)
      Val Γ B[N..] Core.tuniv (wt_Selection_codU h Sel).

Definition  PiEdgeEq {n} (Γ : Ctx n)
  (A : Tm n) (B : Tm (S n)) (b: elt) (f : list (elt * elt))
  (h : wt (tpi b f) tuniv) :=
  forall u v (Sel : Selection f u v) (WT : wt u b)
      (N1 N2 : Tm n),
      conv Γ N1 N2 A ->
      (* take related arguments *)
      EqVal Γ N1 N2 A WT ->
      (* to related results *)
      EqVal Γ B[N1..] B[N2..] Core.tuniv (wt_Selection_codU h Sel).

(* [PiAppVal]/[PiAppEq]/[PiAppEqVal]: the *value*-graph edges of a
   function, following Agda's [PiAppVal2P].  We quantify over a
   [Selection f u v] of the value graph [f] (a join of edges): [u] is the
   key-join (typed at the domain [b]), [v] the value-join.  The argument
   [P] is in the relation at [u]; the result [app M P] is at the
   value-join [v] (witnessed by [wt_Selection_abs]) and codomain type
   [app g u].  Quantifying over joins -- not exact entries [In (ui,vi) f]
   -- is what lets the value-graph restriction (the [wt_abs] case)
   transport across [f' <= f].  Mirrors [PiEdgeVal]/[PiEdgeEq]. *)
Definition PiAppVal {n} (Γ : Ctx n)
  (M : Tm n) (A0 : Tm n) (B0 : Tm (S n)) b f g
  (h : wt (abs f) (tpi b g)) : Prop :=
  forall u v (Sel : Selection f u v) (WT : wt u b)
    (P : Tm n), typing Γ P A0 ->
                Val Γ P A0 WT ->
                Val Γ (Core.app M P) B0[P..] (wt_Selection_abs h Sel).

Definition PiAppEq {n} (Γ : Ctx n)
  (M : Tm n) (A0 : Tm n) (B0 : Tm (S n)) b f g
  (h : wt (abs f) (tpi b g))  :=
  forall u v (Sel : Selection f u v) (WT : wt u b)
    (N1 N2 : Tm n),
    conv Γ N1 N2 A0 ->
    EqVal Γ N1 N2 A0 WT ->
    EqVal Γ (Core.app M N1) (Core.app M N2) B0[N1..] (wt_Selection_abs h Sel).

Definition PiAppEqVal {n} (Γ : Ctx n)
  (M N : Tm n) (A0 : Tm n) (B0 : Tm (S n)) b f g
  (h : wt (abs f) (tpi b g)) :=
  forall u v (Sel : Selection f u v) (WT : wt u b)
    (P : Tm n),
        typing Γ P A0 ->
        Val Γ P A0 WT ->
        EqVal Γ (Core.app M P) (Core.app N P) B0[P..] (wt_Selection_abs h Sel).

(** [ValPi]: a function value [abs g : tpi b f] is related to [M : A] when [A]
    head-reduces to a Π-type [tpi A0 B0] and [M] satisfies both value-graph
    edges [PiAppVal] (each argument maps to a related result) and [PiAppEq]
    (the action is congruent in the argument). *)
Definition ValPi {n} (Γ : Ctx n)
  (M : Tm n) (A : Tm n) g b f (h : wt (abs g) (tpi b f)):=
  exists A0, exists B0, HeadRed A (Core.tpi A0 B0)
  /\ PiAppVal Γ M A0 B0 h
  /\ PiAppEq Γ M A0 B0 h.

(** Binary companion of [ValPi]: [M] and [N] act equally on related arguments. *)

Definition EqValPi {n} (Γ : Ctx n)
  (M : Tm n) (N: Tm n) (A : Tm n) g b f 
  (h : wt (abs g) (tpi b f)) :=
  exists A0, exists B0, HeadRed A (Core.tpi A0 B0)
  /\ PiAppEqVal Γ M N A0 B0 h.


(** [ValTy Γ M u h]: the type-level relation, i.e. [Val] specialized to
    [a = tuniv].  When the type code [u] is a Π-code [tpi b g], [M] must
    head-reduce to a syntactic Π-type [tpi A B] that is well-typed, with its
    domain in the relation and the codomain satisfying the type edges
    [PiEdgeVal]/[PiEdgeEq]; the base type codes are trivially related. *)
Definition ValTy {n} (Γ : Ctx n)
  (M : Tm n) u (h : wt u tuniv) : Prop  :=
  (match u return wt _ tuniv ->  Prop with
  | tpi b g =>
      fun (h : wt (tpi b g) tuniv) =>
        (* ValTyPi M tuniv *)
        (* M reduces to a pi type *)
        exists A B, HeadRed M (Core.tpi A B)

               (* the syntactic pi-type is well-typed *)              
               /\ typing Γ A Core.tuniv
               /\ typing (Γ ++ A) B Core.tuniv

               (* the semantic pi-type is valid *)
               /\ valid (tpi b g)

               (* domain (b) is in the relation *)
               /\ Val Γ A Core.tuniv (wt_tpi_dom h)

               (* the codomain edge: related arguments give related results *)
               /\ PiEdgeVal Γ A B h
               /\ PiEdgeEq Γ A B h

  | tnat => fun h1 => True
  | tuniv => fun h1  => True
  | _ => fun h1  => True
  end) h.


Definition PiEdgeEqTy {n} (Γ : Ctx n)
  (A : Tm n) (B B' : Tm (S n)) b f (h : wt (tpi b f) tuniv) :=
    forall u v (Sel : Selection f u v) (WTu : wt u b)
      (P : Tm n),
          typing Γ P A ->
          (* take a related argument *)
          Val  Γ P A WTu ->
          (* to (equal) related results *)
          EqVal Γ B[P..] B'[P..] Core.tuniv (wt_Selection_codU h Sel).

(** [EqValTy Γ M N a h]: the binary type relation (two convertible types
    related to the same type code [a]); the Π case additionally requires the
    cross codomain edge [PiEdgeEqTy]. *)
Definition EqValTy {n}
  (Γ : Ctx n) M N (a : elt) (h : wt a tuniv) :  Prop :=
  (match a return wt _ tuniv ->  Prop with
  | tpi b f =>
      fun (h : wt (tpi b f) tuniv)  =>
        ValTy Γ M h  /\ ValTy Γ N h /\
        (* EqValTyPi Val EqVal EqValTy M N h *)
             (* both reduce to pi types *)
             exists A B, HeadRed M (Core.tpi A B)
             /\ exists A' B', HeadRed N (Core.tpi A' B')
             (* ... that are convertible *)
             /\ conv Γ A A' Core.tuniv 
             /\ conv (Γ ++ A) B B' Core.tuniv 
             /\ valid (tpi b f)
             (* ... and the domain is in the relation *)
             /\ EqVal  Γ A A' Core.tuniv  (wt_tpi_dom h)
             (* ... and the codomain edge: related args give equal results *)
             /\ PiEdgeEqTy Γ A B B' h
  | _ => fun h => True
  end) h.

End Helpers.
End Rec.


(* ------------------------------------------------------------------
   The unary [Val] and binary [EqVal] logical relations.

   Under a Pi type these relations recurse on the codomain type
   [app f u] (see [PiEdgeEq] / [PiAppVal]), which is *not* a structural
   subterm of the typing derivation [h] — only its rank is smaller
   ([rk (app f u) <= rk_fun f < rk (tpi b f)]).  We therefore define
   them by well-founded recursion on the rank measure [rk u + rk a].

   The measure is [max (rk u) (rk a)] (the larger of the element's and
   the type's rank).  Every recursive occurrence is at strictly smaller
   [max]-rank:
     - the codomain occurrence [EqVal (app f u) tuniv] has
       [rk (app f u) <= rk_fun f < rk (tpi b f)];
     - the domain occurrence [EqVal Γ N1 N2 A WT], [WT : wt u b], is
       made small by the bound [rk u < rk (tpi b f)] added to
       [PiEdgeEq]: with [rk b < rk (tpi b f)] this gives
       [max (rk u) (rk b) < rk (tpi b f)].
   Bounding the argument is what tames Pi-over-universe [tpi tuniv f]
   (which is otherwise not rank-well-founded under type-in-type).

   We realise the recursion with an explicit fuel [k] that decreases
   structurally; the canonical relations instantiate the fuel with
   [S (max (rk u) (rk a))].  The unfolding lemmas [Val_eq]/[EqVal_eq]
   recover the intended one-step behaviour with every recursive
   occurrence at the canonical fuel.
   ------------------------------------------------------------------ *)

(** [Val k Γ M A u a h]: the unary logical relation, by recursion on fuel [k]
    and case analysis on the type [a] (then, for Π types, on the value [u]).
    [a = bot] / [u = bot] / fuel [0] are trivially [True] (everything related);
    [a = tuniv] defers to the type relation [ValTy]; [a = tpi b f] requires both
    that [A] is a valid type and that [M] satisfies the Π-edge condition
    [ValPi]; [a = tnat] matches the numeral structure through head reduction.
    Defined mutually with [EqVal]. *)
Fixpoint Val (k : nat) {n} (Γ : Ctx n)
  (M : Tm n) (A : Tm n) (u : elt) (a : elt) (h : wt u a)
  {struct k} : Prop :=
  match k with
  | 0 => True
  | S k =>
      (match a return wt u _ -> Prop with

      | bot => fun h => True

      | tuniv => fun (h : wt u tuniv) =>
          Rec.ValTy (@Val k) (@EqVal k) Γ M h

      | tpi b f => fun h  =>
           (match u return wt _ (tpi b f) ->  Prop with

            | abs g => fun (h : wt (abs g) (tpi b f)) =>
                        Rec.ValTy (@Val k) (@EqVal k) Γ A (wt_abs_ty h)
                      /\ Rec.ValPi (@Val k) (@EqVal k) Γ M A h

            | _ => fun h  => True
            end) h

      | tnat => fun h =>
          (match u return wt _ tnat -> Prop with
               | zero => fun h  =>
                 HeadRed M (Core.zero)
               | succ v => fun (h : wt (succ v) tnat)  =>
                 exists M1, HeadRed M (Core.succ M1)
                 /\ Val k Γ M1 Core.tnat (wt_succ_inv h)
               | _ =>  fun h => True
               end) h
      | _ => fun h  => True
       end) h
  end
(** [EqVal k Γ M N A u a h]: the binary (PER) companion of [Val], relating two
    convertible terms [M], [N] to the member [u : a].  It has the same case
    structure as [Val], additionally requiring each side to be in [Val] and the
    pair to satisfy the symmetric edge conditions. *)
(* Binary logical relation *)
with EqVal (k : nat) {n} (Γ : Ctx n)
  (M : Tm n) (N : Tm n) (A : Tm n) (u : elt) (a : elt) (h : wt u a)
  {struct k} : Prop :=
  match k with
  | 0 => True
  | S k =>
     (match a return wt u _ -> Prop with

      | bot => fun h => True

      | tuniv => fun (h : wt u tuniv) =>

            Rec.ValTy (@Val k) (@EqVal k) Γ M h
          /\ Rec.ValTy (@Val k) (@EqVal k) Γ N h
          /\ Rec.EqValTy (@Val k) (@EqVal k) Γ M N h

      | tpi b f => fun h =>
           (match u return wt _ (tpi b f) -> Prop with
           | bot => fun h => True
           | abs g => fun (h : wt (abs g) (tpi b f)) =>
               Rec.ValTy (@Val k) (@EqVal k) Γ A (wt_abs_ty h)
             /\ Rec.ValPi (@Val k) (@EqVal k) Γ M A h
             /\ Rec.ValPi (@Val k) (@EqVal k) Γ N A h
             /\ Rec.EqValPi (@Val k) (@EqVal k) Γ M N A h

           | _ => fun h => True
            end) h

      | tnat => fun h =>
          (match u return wt _ tnat -> Prop with
               | zero => fun h =>
                 HeadRed M Core.zero
                 /\ HeadRed N Core.zero
               | succ v => fun (h : wt (succ v) tnat) =>
                 exists M1, HeadRed M (Core.succ M1)
                 /\ exists N1, HeadRed N (Core.succ N1)
                 /\ EqVal k Γ M1 N1 Core.tnat (wt_succ_inv h)
               | _ =>  fun h => True
               end) h
      | _ => fun h => True
    end) h
  end.

Arguments Val : clear implicits.
Arguments EqVal : clear implicits.

(* Parameterised abbreviations for the [Rec.*] helpers *)
Notation ValTy k      := (Rec.ValTy (@Val k) (@EqVal k)).
Notation EqValTy k    := (Rec.EqValTy (@Val k) (@EqVal k)).
Notation ValPi k      := (Rec.ValPi (@Val k) (@EqVal k)).
Notation EqValPi k    := (Rec.EqValPi (@Val k) (@EqVal k)).
Notation PiEdgeEq k   := (Rec.PiEdgeEq (@EqVal k)).
Notation PiEdgeVal k  := (Rec.PiEdgeVal (@Val k)).
Notation PiAppVal k   := (Rec.PiAppVal (@Val k)).
Notation PiAppEq k    := (Rec.PiAppEq (@EqVal k)).
Notation PiAppEqVal k := (Rec.PiAppEqVal (@Val k) (@EqVal k)).
Notation PiEdgeEqTy k := (Rec.PiEdgeEqTy (@Val k) (@EqVal k)).

Arguments Val _ {n} Γ M A {u} {a} h.
Arguments EqVal _ {n} Γ M N A {u} {a} h.

(* Per-constructor unfolding lemmas (the form actually used downstream).
   [Val]/[EqVal] at fuel [S RB] expose the helpers/recursive occurrences
   at fuel [RB] -- definitional, hence [reflexivity]. *)

Lemma Val_tuniv {n} (Γ : Ctx n) M A u (h : wt u tuniv) k :
  Val (S k) Γ M A h = ValTy k Γ M h.
Proof. reflexivity. Qed.

Lemma Val_abs {n} (Γ : Ctx n) M A g b f (h : wt (abs g) (tpi b f)) k :
  Val (S k) Γ M A h = (ValTy k Γ A (wt_abs_ty h) /\ ValPi k Γ M A h).
Proof. reflexivity. Qed.

Lemma Val_zero {n} (Γ : Ctx n) M A (h : wt zero tnat) k :
  Val (S k) Γ M A h = HeadRed M Core.zero.
Proof. reflexivity. Qed.

Lemma Val_succ {n} (Γ : Ctx n) M A v (h : wt (succ v) tnat) k :
  Val (S k) Γ M A h = (exists M1, HeadRed M (Core.succ M1) /\ Val k Γ M1 Core.tnat (wt_succ_inv h)).
Proof. reflexivity. Qed.

Lemma EqVal_tuniv {n} (Γ : Ctx n) M N A u (h : wt u tuniv) k :
  EqVal (S k) Γ M N A h = (ValTy k Γ M h /\ ValTy k Γ N h /\ EqValTy k Γ M N h).
Proof. reflexivity. Qed.

Lemma EqVal_abs {n} (Γ : Ctx n) M N A g b f (h : wt (abs g) (tpi b f)) k :
  EqVal (S k) Γ M N A h =
  (ValTy k Γ A (wt_abs_ty h) /\ ValPi k Γ M A h /\ ValPi k Γ N A h /\ EqValPi k Γ M N A h).
Proof. reflexivity. Qed.

Lemma EqVal_zero {n} (Γ : Ctx n) M N A (h : wt zero tnat) k :
  EqVal (S k) Γ M N A h = (HeadRed M Core.zero /\ HeadRed N Core.zero).
Proof. reflexivity. Qed.

Lemma EqVal_succ {n} (Γ : Ctx n) M N A v (h : wt (succ v) tnat) k :
  EqVal (S k) Γ M N A h =
  (exists M1, HeadRed M (Core.succ M1) /\ exists N1, HeadRed N (Core.succ N1)
            /\ EqVal k Γ M1 N1 Core.tnat (wt_succ_inv h)).
Proof. reflexivity. Qed.

(* ============================================================
   Val2-Bot, EqVal2-Bot: at u = bot, both relations are total.
   ============================================================ *)

(** The least element [bot] is related to every term: the relation is
    inhabited at the bottom of every type. *)
Lemma Val_Bot {n} (Γ : Ctx n) (M A : Tm n) a (h : wt bot a) k : Val k Γ M A h.
Proof.
  unfold Val. destruct k as [|k']; first exact I.
  revert h. destruct a; intro h; exact I.
Qed.

Lemma EqVal_Bot {n} (Γ : Ctx n) (M N A : Tm n) a (h : wt bot a) k :
  EqVal k Γ M N A h.
Proof.
  unfold EqVal. destruct k as [|k']; first exact I.
  revert h. destruct a; intro h; repeat split; try exact I;
    dependent destruction h; exact I.
Qed.

(* ============================================================
   wt judgement irrelevance
   ============================================================ *)

(* [Val]/[EqVal] depend on the typing derivation only up to proof
   irrelevance, so any two derivations of the same [wt u a] give the
   same relation.  Used to discharge the cases of [up_down_restrict]
   where the two element/type pairs coincide. *)
Lemma Val_irr {n} (Γ : Ctx n) (M T : Tm n) u a (h h' : wt u a) k :
  Val k Γ M T h -> Val k Γ M T h'.
Proof. now rewrite (proof_irrelevance _ h h'). Qed.

Lemma EqVal_irr {n} (Γ : Ctx n) (M N T : Tm n) u a (h h' : wt u a) k :
  EqVal k Γ M N T h -> EqVal k Γ M N T h'.
Proof. now rewrite (proof_irrelevance _ h h'). Qed.

Lemma ValTy_irr {n} (Γ : Ctx n) (M : Tm n) u (h h' : wt u tuniv) k :
  ValTy k Γ M h -> ValTy k Γ M h'.
Proof. now rewrite (proof_irrelevance _ h h'). Qed.

(* Proof-irrelevance for [wt]: needed to identify [Val]/[EqVal] proof
   indices when the type/element are forced to coincide. *)
Lemma wt_unique {u a} (h1 h2 : wt u a) : h1 = h2.
Proof. apply proof_irrelevance. Qed.

(* ============================================================
   Relations are trivial for bottom elements
   ============================================================ *)

Lemma is_bot_eq (a : elt) : is_bot a -> a = bot.
Proof. by destruct a. Qed.

(* At a [bot] (semantic) type the relations are trivially total. *)
Lemma Val_isbot {n} (Γ : Ctx n) (M A : Tm n) u a (h : wt u a) k :
  is_bot a -> Val k Γ M A h.
Proof.
  move=> /is_bot_eq E. subst a.
  unfold Val. destruct k as [|k']; first exact I.
  revert h. destruct u; intro h; exact I.
Qed.

Lemma EqVal_isbot {n} (Γ : Ctx n) (M N A : Tm n) u a (h : wt u a) k :
  is_bot a -> EqVal k Γ M N A h.
Proof.
  move=> /is_bot_eq E. subst a.
  unfold EqVal. destruct k as [|k']; first exact I.
  revert h. destruct u; intro h; exact I.
Qed.


(* ============================================================
   Val <-> ValTy  and  EqVal <-> EqValTy
   ============================================================ *)

Lemma EqValTy_EqVal {n} (Γ : Ctx n) (A B : Tm n) a (h : wt a tuniv) k :
  EqValTy k Γ A B h ->
  EqVal (S k) Γ A B Core.tuniv h.
Proof.
  rewrite (EqVal_tuniv Γ A B Core.tuniv h k).
  dependent destruction h; cbn [Rec.EqValTy] in * |- *; try done.
  move=> [hA [hB h1]]. eauto.
Qed.

Lemma EqVal_EqValTy {n} (Γ : Ctx n) (A B C : Tm n) a (h : wt a tuniv) k :
  EqVal (S k) Γ A B C h ->
  EqValTy k Γ A B h.
Proof.
  rewrite (EqVal_tuniv Γ A B C h k). by move=> [_ [_ ?]].
Qed.

Lemma ValTy_Val {n} (Γ : Ctx n) (A : Tm n) a (h : wt a tuniv) k :
  ValTy k Γ A h ->
  Val (S k) Γ A Core.tuniv h.
Proof.
  rewrite (Val_tuniv Γ A Core.tuniv h k). auto.
Qed.

Lemma Val_ValTy {n} (Γ : Ctx n) (A : Tm n) a (h : wt a tuniv) k :
  Val (S k) Γ A Core.tuniv h ->
  ValTy k Γ A h.
Proof.
  rewrite (Val_tuniv Γ A Core.tuniv h k). auto.
Qed.
                                 
(* ============================================================
   Diagonal embedding
   Val <-> EqVal  and  ValTy → EqValTy
   ============================================================ *)


(** Reflexivity / diagonal embedding [Val -> EqVal]: a related term is related
    to itself.  (Agda: [Val2-to-EqVal2].) *)
Lemma Val_EqVal k : forall {n} (Γ : Ctx n) (M A : Tm n) u a (h : wt u a),
  Val k Γ M A h -> EqVal k Γ M M A h.
Proof.
  induction k as [|k IH].
  all: intros n Γ M A u a h.
  - unfold EqVal. done.
  - dependent destruction h.
    all: try solve [cbn; try destruct a; done].
    + (* succ *)
      cbn. move=> [M1 [R1 V1]]. exists M1. split. auto.
      apply IH in V1; eauto.
    + (* tpi *)
      cbn.
      move=> [A0 [B0 [R0 [TA0 [TB0 [Vtpi [VA0 [PEV PEE]]]]]]]].
      repeat split.
      all: try solve [eexists; eexists; repeat split; eauto].
      exists A0. exists B0. repeat split; eauto.
      exists A0. exists B0. repeat split; eauto.
      eapply c_refl; eauto.
      eapply c_refl; eauto.
      unfold PiEdgeEqTy.
      move=> u v Sel WTu P TP VP.
      unfold PiEdgeEq in PEE.
      specialize (PEE u v Sel WTu P P (c_refl _ _ _ _ TP)).
      eapply PEE. eapply IH. auto.
    + (* tabs *)
      cbn.
      move=> [[A0 [B0 [R0 [TA0 [TB0 [Vtabs [VA0 [PEV PEE]]]]]]]] VAbs].
      repeat split; eauto.
      exists A0. exists B0.
      repeat split; eauto.
      unfold ValPi in VAbs.
      destruct VAbs as [A1 [B1 [R1 [PAV PAE]]]].
      move: (HeadRed_tpi_det R0 R1) => [EQA EQB]. subst A1. subst B1.
      exists A0. exists B0; split; auto.
      unfold PiAppEqVal.
      intros u v Sel WTu P TP VP.
      specialize (PAV u v Sel WTu P TP VP).
      eapply IH. eauto.
Qed.


(* ValTy2-to-EqValTy2 *)
Lemma ValTy_EqValTy {n} (Γ : Ctx n) (M : Tm n) u (h : wt u tuniv) k :
  ValTy k Γ M h -> EqValTy k Γ M M h.
Proof.
  intros VT.
  eapply EqVal_EqValTy.
  eapply Val_EqVal.
  eapply ValTy_Val. exact VT.
Qed.


(* ============================================================
   projecting first and second parts of EqVal
   EqVal_Val1, EqVal_Val2
   ============================================================ *)


Fixpoint EqVal_Val1 {n} (Γ : Ctx n) (M N A : Tm n) u a (h : wt u a) k
  {struct h} :
  EqVal k Γ M N A h -> Val k Γ M A h.
Proof.
  destruct k as [|k].
  { move=> _. unfold Val. exact I. }
  dependent destruction h.
  - move=> _. apply Val_Bot.
  - rewrite EqVal_tuniv Val_tuniv. by move=> [? _].
  - rewrite EqVal_tuniv Val_tuniv. by move=> [? _].
  - rewrite EqVal_zero Val_zero. by move=> [? _].
  - rewrite EqVal_succ Val_succ.
    move=> [M1 [h1 [N1 [h2 V1]]]]. exists M1. split; auto.
    eapply EqVal_Val1; exact V1.
  - rewrite EqVal_tuniv Val_tuniv. by move=> [? _].
  - rewrite EqVal_abs Val_abs. move=> [hA [hM _]]. by split.
Qed.


Fixpoint EqVal_Val2 {n} (Γ : Ctx n) (M N A : Tm n) u a (h : wt u a) k
  {struct h} :
  EqVal k Γ M N A h -> Val k Γ N A h.
Proof.
  destruct k as [|k].
  { move=> _. unfold Val. exact I. }
  dependent destruction h.
  - move=> _. apply Val_Bot.
  - rewrite EqVal_tuniv Val_tuniv. by move=> [_ [? _]].
  - rewrite EqVal_tuniv Val_tuniv. by move=> [_ [? _]].
  - rewrite EqVal_zero Val_zero. by move=> [_ ?].
  - rewrite EqVal_succ Val_succ.
    move=> [M1 [h1 [N1 [h2 V1]]]]. exists N1. split; auto.
    eapply EqVal_Val2; exact V1.
  - rewrite EqVal_tuniv Val_tuniv. by move=> [_ [? _]].
  - rewrite EqVal_abs Val_abs. move=> [hA [_ [hN _]]]. by split.
Qed.

(* ============================================================
   ValTy is closed under head expansion and reduction
   ============================================================ *)

Lemma ValTy_HeadRed1_expand {n} (Γ : Ctx n) (M M' : Tm n) u (h : wt u tuniv) k :
  HeadRed1 M' M -> ValTy k Γ M h -> ValTy k Γ M' h.
Proof. 
  move=> R.
  dependent destruction h; cbn [Rec.ValTy].
  1,2,3: tauto.
  move=> [A0 [B0 [R0 [TA0 [TB0 [Vpi [VA [PEV PEE]]]]]]]].
  exists A0, B0.
  split. { eapply HeadRed1_tpi_expand; eauto. }
  split. exact TA0.
  split. exact TB0.
  split. exact Vpi.
  split. exact VA.
  split. exact PEV.
  exact PEE.
Qed.

(** Closure under head expansion for types: if [M'] head-reduces to a related
    type [M], then [M'] is related too.  (Agda: [ValTy2-headred-expand].) *)
Lemma ValTy_HeadRed_expand {n} (Γ : Ctx n) (M M' : Tm n) u (h : wt u tuniv) k :
  HeadRed M' M -> ValTy k Γ M h -> ValTy k Γ M' h.
Proof.
  move=> R. induction R.
  - done.
  - move=> h1. specialize (IHR h1).
    eapply ValTy_HeadRed1_expand in H; eauto.
Qed.

Lemma ValTy_HeadRed1_contract {n} (Γ : Ctx n) (M M' : Tm n) u (h : wt u tuniv) k :
  HeadRed1 M M' -> ValTy k Γ M h -> ValTy k Γ M' h.
Proof. 
  move=> R.
  dependent destruction h; cbn [Rec.ValTy].
  1,2,3: tauto.
  move=> [A0 [B0 [R0 [TA0 [TB0 [Vpi [VA [PEV PEE]]]]]]]].
  exists A0, B0.
  split. { eapply HeadRed1_tpi_contract; eauto. }
  split. exact TA0.
  split. exact TB0.
  split. exact Vpi.
  split. exact VA.
  split. exact PEV.
  exact PEE.
Qed.

(* ValTy2-headred-contract *)
Lemma ValTy_headred_contract {n} (Γ : Ctx n) (M M' : Tm n) u (h : wt u tuniv) k :
  HeadRed M M' -> ValTy k Γ M h -> ValTy k Γ M' h.
Proof.
  move=> R. induction R.
  - done.
  - move=> h1. apply IHR. eapply ValTy_HeadRed1_contract; eauto.
Qed.

(* ============================================================
   EqValTy is closed under head expansion and reduction
   ============================================================ *)

(* EqValTy2-headred-expand *)
Lemma EqValTy_headred_expand {n} (Γ : Ctx n) (M1 M2 M1' M2' : Tm n) u 
  (h : wt u tuniv) RB :
  HeadRed M1' M1 -> HeadRed M2' M2 ->
  EqValTy RB Γ M1 M2 h -> EqValTy RB Γ M1' M2' h.
Proof.
  move=> R1 R2.
  dependent destruction h; cbn [Rec.EqValTy].
  1,2,3: tauto.
  move=> [VM1 [VM2 [A0 [B0 [HM1 [A0' [B0' [HM2 REST]]]]]]]].
  split; [ eapply ValTy_HeadRed_expand; [ exact R1 | exact VM1 ] | ].
  split; [ eapply ValTy_HeadRed_expand; [ exact R2 | exact VM2 ] | ].
  exists A0, B0. split; [ eapply relations.ms_app; [ exact R1 | exact HM1 ] | ].
  exists A0', B0'. split; [ eapply relations.ms_app; [ exact R2 | exact HM2 ] | exact REST ].
Qed.

(* EqValTy2-headred-contract *)
Lemma EqValTy_headred_contract {n} (Γ : Ctx n) (M1 M2 M1' M2' : Tm n) u
  (h : wt u tuniv) RB :
  HeadRed M1 M1' -> HeadRed M2 M2' ->
  EqValTy RB Γ M1 M2 h -> EqValTy RB Γ M1' M2' h.
Proof.
  move=> R1 R2.
  dependent destruction h; cbn [Rec.EqValTy].
  1,2,3: tauto.
  move=> [VM1 [VM2 [A0 [B0 [HM1 [A0' [B0' [HM2 REST]]]]]]]].
  split; [ eapply ValTy_headred_contract; [ exact R1 | exact VM1 ] | ].
  split; [ eapply ValTy_headred_contract; [ exact R2 | exact VM2 ] | ].
  exists A0, B0. split; [ eapply HeadRed_tpi_contract; [ exact R1 | exact HM1 ] | ].
  exists A0', B0'. split; [ eapply HeadRed_tpi_contract; [ exact R2 | exact HM2 ] | exact REST ].
Qed.

(* ============================================================
   Val/EqVal closed under head expansion/contraction
   ============================================================ *)

(* ---------------------------------------------------------------------
   TERMINATION METRIC: the fuel [k].  The reduced term
   occurs in [Val k]/[EqVal k] only through (i) the [HeadRed _ <normal>]
   clauses (closed by [ms_trans]/[HeadRed_expand] for expand and
   [HeadRed_contract] for contract) and (ii) the [app M P] occurrences in
   the [ValPi]/[EqValPi] edges of the [a=tpi,u=abs] case, which are at the
   inner [@Val k']/[@EqVal k'] (one fuel less) and are discharged by the
   fuel-[k] [IH] after an [ms_app] step.  So the four facts are bundled and
   proven by [induction k]. 
   --------------------------------------------------------------------- *)

Definition HeadRedVE (k : nat) : Prop :=
  (forall n (Γ : Ctx n) (M M0 T : Tm n) u a (h : wt u a),
      HeadRed M0 M -> Val k Γ M T h -> Val k Γ M0 T h)
  /\ (forall n (Γ : Ctx n) (M M0 N N0 T : Tm n) u a (h : wt u a),
      HeadRed M0 M -> HeadRed N0 N -> EqVal k Γ M N T h -> EqVal k Γ M0 N0 T h)
  /\ (forall n (Γ : Ctx n) (M M0 T : Tm n) u a (h : wt u a),
      HeadRed M M0 -> Val k Γ M T h -> Val k Γ M0 T h)
  /\ (forall n (Γ : Ctx n) (M M0 N N0 T : Tm n) u a (h : wt u a),
      HeadRed M M0 -> HeadRed N N0 -> EqVal k Γ M N T h -> EqVal k Γ M0 N0 T h).

Lemma headred_VE_all : forall k, HeadRedVE k.
Proof.
  induction k as [|k IH].
  - (* fuel 0: [Val 0]/[EqVal 0] are [True] *)
    unfold HeadRedVE. repeat split; intros; exact I.
  - move: IH => [IHVe [IHEe [IHVc IHEc]]].
    (* [ValPi]/[EqValPi] transport at fuel [k], used in the [wt_abs] cases.
       The reduced function head appears only in [app M P], moved by the
       app-congruence [ms_app] and the fuel-[k] IH. *)
    have ValPiExp : forall m (Δ : Ctx m) (P P0 S : Tm m) gg bb ff
        (hh : wt (abs gg) (tpi bb ff)),
        HeadRed P0 P -> ValPi k Δ P S hh -> ValPi k Δ P0 S hh.
    { move=> m Δ P P0 S gg bb ff hh HR [A0 [B0 [HRT [PAV PAE]]]].
      exists A0, B0. split; [ exact HRT | ]. split.
      - move=> uu vv Sel WT Q TQ VQ.
        eapply IHVe; [ apply HeadRed_app; exact HR | exact (PAV uu vv Sel WT Q TQ VQ) ].
      - move=> uu vv Sel WT N1 N2 CN EV.
        eapply IHEe; [ apply HeadRed_app; exact HR | apply HeadRed_app; exact HR
                     | exact (PAE uu vv Sel WT N1 N2 CN EV) ]. }
    have ValPiCon : forall m (Δ : Ctx m) (P P0 S : Tm m) gg bb ff
        (hh : wt (abs gg) (tpi bb ff)),
        HeadRed P P0 -> ValPi k Δ P S hh -> ValPi k Δ P0 S hh.
    { move=> m Δ P P0 S gg bb ff hh HR [A0 [B0 [HRT [PAV PAE]]]].
      exists A0, B0. split; [ exact HRT | ]. split.
      - move=> uu vv Sel WT Q TQ VQ.
        eapply IHVc; [ apply HeadRed_app; exact HR | exact (PAV uu vv Sel WT Q TQ VQ) ].
      - move=> uu vv Sel WT N1 N2 CN EV.
        eapply IHEc; [ apply HeadRed_app; exact HR | apply HeadRed_app; exact HR
                     | exact (PAE uu vv Sel WT N1 N2 CN EV) ]. }
    have EqValPiExp : forall m (Δ : Ctx m) (P P0 Q Q0 S : Tm m) gg bb ff
        (hh : wt (abs gg) (tpi bb ff)),
        HeadRed P0 P -> HeadRed Q0 Q ->
        EqValPi k Δ P Q S hh -> EqValPi k Δ P0 Q0 S hh.
    { move=> m Δ P P0 Q Q0 S gg bb ff hh HRP HRQ [A0 [B0 [HRT PAEV]]].
      exists A0, B0. split; [ exact HRT | ].
      move=> uu vv Sel WT R0 TR VR.
      eapply IHEe; [ apply HeadRed_app; exact HRP | apply HeadRed_app; exact HRQ
                   | exact (PAEV uu vv Sel WT R0 TR VR) ]. }
    have EqValPiCon : forall m (Δ : Ctx m) (P P0 Q Q0 S : Tm m) gg bb ff
        (hh : wt (abs gg) (tpi bb ff)),
        HeadRed P P0 -> HeadRed Q Q0 ->
        EqValPi k Δ P Q S hh -> EqValPi k Δ P0 Q0 S hh.
    { move=> m Δ P P0 Q Q0 S gg bb ff hh HRP HRQ [A0 [B0 [HRT PAEV]]].
      exists A0, B0. split; [ exact HRT | ].
      move=> uu vv Sel WT R0 TR VR.
      eapply IHEc; [ apply HeadRed_app; exact HRP | apply HeadRed_app; exact HRQ
                   | exact (PAEV uu vv Sel WT R0 TR VR) ]. }
    unfold HeadRedVE. repeat split.
    + (* Val expand *)
      intros n Γ M M0 T u a h R. dependent destruction h.
      * move=> _; apply Val_Bot.
      * rewrite !Val_tuniv. move=> _. cbn [Rec.ValTy]. exact I.
      * rewrite !Val_tuniv. move=> _. cbn [Rec.ValTy]. exact I.
      * rewrite !Val_zero. move=> HR0. eapply relations.ms_app; [ exact R | exact HR0 ].
      * rewrite !Val_succ. move=> [M1 [HR0 HV]].
        exists M1. split; [ eapply relations.ms_app; [ exact R | exact HR0 ] | exact HV ].
      * rewrite !Val_tuniv. eapply ValTy_HeadRed_expand; exact R.
      * rewrite !Val_abs. move=> [VTd VPi].
        split; [ exact VTd | eapply ValPiExp; [ exact R | exact VPi ] ].
    + (* EqVal expand *)
      intros n Γ M M0 N N0 T u a h RM RN. dependent destruction h.
      * move=> _; apply EqVal_Bot.
      * rewrite !EqVal_tuniv. move=> _. cbn [Rec.ValTy Rec.EqValTy]. tauto.
      * rewrite !EqVal_tuniv. move=> _. cbn [Rec.ValTy Rec.EqValTy]. tauto.
      * rewrite !EqVal_zero. move=> [HM HN].
        split; [ eapply relations.ms_app; [ exact RM | exact HM ]
               | eapply relations.ms_app; [ exact RN | exact HN ] ].
      * rewrite !EqVal_succ. move=> [M1 [HM [N1 [HN HE]]]].
        exists M1. split; [ eapply relations.ms_app; [ exact RM | exact HM ] | ].
        exists N1. split; [ eapply relations.ms_app; [ exact RN | exact HN ] | exact HE ].
      * rewrite !EqVal_tuniv. move=> [VTM [VTN ET]].
        split; [ eapply ValTy_HeadRed_expand; [ exact RM | exact VTM ] | ].
        split; [ eapply ValTy_HeadRed_expand; [ exact RN | exact VTN ] | ].
        eapply EqValTy_headred_expand; [ exact RM | exact RN | exact ET ].
      * rewrite !EqVal_abs. move=> [VTd [VPiM [VPiN EPi]]].
        split; [ exact VTd | ].
        split; [ eapply ValPiExp; [ exact RM | exact VPiM ] | ].
        split; [ eapply ValPiExp; [ exact RN | exact VPiN ] | ].
        eapply EqValPiExp; [ exact RM | exact RN | exact EPi ].
    + (* Val contract *)
      intros n Γ M M0 T u a h R. dependent destruction h.
      * move=> _; apply Val_Bot.
      * rewrite !Val_tuniv. move=> _. cbn [Rec.ValTy]. exact I.
      * rewrite !Val_tuniv. move=> _. cbn [Rec.ValTy]. exact I.
      * rewrite !Val_zero. move=> HR0.
        eapply HeadRed_contract_to_multi; [ apply nf_zero | exact R | exact HR0 ].
      * rewrite !Val_succ. move=> [M1 [HR0 HV]].
        exists M1. split; [ eapply HeadRed_contract_to_multi; [ apply nf_succ | exact R | exact HR0 ] | exact HV ].
      * rewrite !Val_tuniv. eapply ValTy_headred_contract; exact R.
      * rewrite !Val_abs. move=> [VTd VPi].
        split; [ exact VTd | eapply ValPiCon; [ exact R | exact VPi ] ].
    + (* EqVal contract *)
      intros n Γ M M0 N N0 T u a h RM RN. dependent destruction h.
      * move=> _; apply EqVal_Bot.
      * rewrite !EqVal_tuniv. move=> _. cbn [Rec.ValTy Rec.EqValTy]. tauto.
      * rewrite !EqVal_tuniv. move=> _. cbn [Rec.ValTy Rec.EqValTy]. tauto.
      * rewrite !EqVal_zero. move=> [HM HN].
        split; [ eapply HeadRed_contract_to_multi; [ apply nf_zero | exact RM | exact HM ]
               | eapply HeadRed_contract_to_multi; [ apply nf_zero | exact RN | exact HN ] ].
      * rewrite !EqVal_succ. move=> [M1 [HM [N1 [HN HE]]]].
        exists M1. split; [ eapply HeadRed_contract_to_multi; [ apply nf_succ | exact RM | exact HM ] | ].
        exists N1. split; [ eapply HeadRed_contract_to_multi; [ apply nf_succ | exact RN | exact HN ] | exact HE ].
      * rewrite !EqVal_tuniv. move=> [VTM [VTN ET]].
        split; [ eapply ValTy_headred_contract; [ exact RM | exact VTM ] | ].
        split; [ eapply ValTy_headred_contract; [ exact RN | exact VTN ] | ].
        eapply EqValTy_headred_contract; [ exact RM | exact RN | exact ET ].
      * rewrite !EqVal_abs. move=> [VTd [VPiM [VPiN EPi]]].
        split; [ exact VTd | ].
        split; [ eapply ValPiCon; [ exact RM | exact VPiM ] | ].
        split; [ eapply ValPiCon; [ exact RN | exact VPiN ] | ].
        eapply EqValPiCon; [ exact RM | exact RN | exact EPi ].
Qed.

(** Closure under head expansion for values (Agda: [Val2-beta-expand]): a term
    head-reducing to a related term is itself related.  These four lemmas are
    projections of the bundled [headred_VE_all]. *)
Lemma Val_beta_expand k : forall {n} (Γ : Ctx n) (M M0 T : Tm n) u a (h : wt u a),
  HeadRed M0 M -> Val k Γ M T h -> Val k Γ M0 T h.
Proof. exact (proj1 (headred_VE_all k)). Qed.

(** Binary head expansion (Agda: [EqVal2-headred-expand]). *)
Lemma EqVal_headred_expand {n} (Γ : Ctx n) (M M0 N N0 T : Tm n) u a (h : wt u a) k :
  HeadRed M0 M -> HeadRed N0 N ->
  EqVal k Γ M N T h -> EqVal k Γ M0 N0 T h.
Proof. exact (proj1 (proj2 (headred_VE_all k)) n Γ M M0 N N0 T u a h). Qed.


(** Closure under head contraction for values (Agda: [Val2-headred-contract]). *)
Lemma Val_headred_contract {n} (Γ : Ctx n) (M M0 T : Tm n) u a (h : wt u a) k :
  HeadRed M M0 -> Val k Γ M T h -> Val k Γ M0 T h.
Proof. exact (proj1 (proj2 (proj2 (headred_VE_all k))) n Γ M M0 T u a h). Qed.

(* EqVal2-headred-contract *)
Lemma EqVal_headred_contract {n} (Γ : Ctx n) (M M0 N N0 T : Tm n) u a (h : wt u a) k :
  HeadRed M M0 -> HeadRed N N0 ->
  EqVal k Γ M N T h -> EqVal k Γ M0 N0 T h.
Proof. exact (proj2 (proj2 (proj2 (headred_VE_all k))) n Γ M M0 N N0 T u a h). Qed.


(* ValPi2-headred-expand *)
Lemma ValPi_headred_expand {n} (Γ : Ctx n) (M M' T : Tm n) b f g
  (h : wt (abs g) (tpi b f)) k :
  HeadRed M' M -> ValPi k Γ M T h -> ValPi k Γ M' T h.
Proof.
  move=> HR [A0 [B0 [HRT [PAV PAE]]]].
  exists A0, B0. split; [ exact HRT | ]. split.
  - move=> uu vv Sel WT Q TQ VQ.
    eapply Val_beta_expand; [ apply HeadRed_app; exact HR | exact (PAV uu vv Sel WT Q TQ VQ) ].
  - move=> uu vv Sel WT N1 N2 CN EV.
    eapply EqVal_headred_expand; [ apply HeadRed_app; exact HR | apply HeadRed_app; exact HR
                                 | exact (PAE uu vv Sel WT N1 N2 CN EV) ].
Qed.

(* EqValPi2-headred-expand *)
Lemma EqValPi_headred_expand {n} (Γ : Ctx n) (M1 M2 M1' M2' T : Tm n) b f g
  (h : wt (abs g) (tpi b f)) k :
  HeadRed M1' M1 -> HeadRed M2' M2 ->
  EqValPi k Γ M1 M2 T h -> EqValPi k Γ M1' M2' T h.
Proof.
  move=> HR1 HR2 [A0 [B0 [HRT PAEV]]].
  exists A0, B0. split; [ exact HRT | ].
  move=> uu vv Sel WT Q TQ VQ.
  eapply EqVal_headred_expand; [ apply HeadRed_app; exact HR1 | apply HeadRed_app; exact HR2
                               | exact (PAEV uu vv Sel WT Q TQ VQ) ].
Qed.

(* ValPi2-headred-contract *)
Lemma ValPi_headred_contract {n} (Γ : Ctx n) (M M' T : Tm n) b f g
  (h : wt (abs g) (tpi b f)) k :
  HeadRed M M' -> ValPi k Γ M T h -> ValPi k Γ M' T h.
Proof.
  move=> HR [A0 [B0 [HRT [PAV PAE]]]].
  exists A0, B0. split; [ exact HRT | ]. split.
  - move=> uu vv Sel WT Q TQ VQ.
    eapply Val_headred_contract; [ apply HeadRed_app; exact HR | exact (PAV uu vv Sel WT Q TQ VQ) ].
  - move=> uu vv Sel WT N1 N2 CN EV.
    eapply EqVal_headred_contract; [ apply HeadRed_app; exact HR | apply HeadRed_app; exact HR
                                   | exact (PAE uu vv Sel WT N1 N2 CN EV) ].
Qed.

(* EqValPi2-headred-contract *)
Lemma EqValPi_headred_contract {n} (Γ : Ctx n) (M1 M2 M1' M2' T : Tm n) b f g
  (h : wt (abs g) (tpi b f)) k :
  HeadRed M1 M1' -> HeadRed M2 M2' ->
  EqValPi k Γ M1 M2 T h -> EqValPi k Γ M1' M2' T h.
Proof.
  move=> HR1 HR2 [A0 [B0 [HRT PAEV]]].
  exists A0, B0. split; [ exact HRT | ].
  move=> uu vv Sel WT Q TQ VQ.
  eapply EqVal_headred_contract; [ apply HeadRed_app; exact HR1 | apply HeadRed_app; exact HR2
                                 | exact (PAEV uu vv Sel WT Q TQ VQ) ].
Qed.





(* ============================================================
   downVal/upVal/downEqVal/upEqVal/restrictVal/restrictEqVal
   ============================================================ *)

(* ------------------------------------------------------------------
   Monotonicity of [Val]/[EqVal] in the type and the element
   (up/down/restrict).  These mutually recurse through the Pi codomain
   ([app g u], whose rank is smaller), so we prove them together by
   well-founded recursion on the rank measure, bundled into one
   strong-induction statement [up_down_restrict].  The named lemmas
   [upVal] … [restrictEqVal] are derived as corollaries.
   ------------------------------------------------------------------ *)

(* The six monotonicity statements, bundled, at induction level [k] and
   relation bound [k].  [Val]/[EqVal] are taken at [k]; the rank
   premise ([... <= k]) drives the strong induction, the [... < k]
   premise keeps the relation's fuel above all the ranks in play. *)
Definition UDR (k : nat) : Prop :=
  (forall n (Γ : Ctx n) (M T : Tm n) u a0 a1
      (h0 : wt u a0) (h1 : wt u a1) (hUa0 : wt a0 tuniv) (hUa1 : wt a1 tuniv),
      le a0 a1 -> Val k Γ M T h0 -> Val k Γ T Core.tuniv hUa1 -> Val k Γ M T h1)
  /\ (forall n (Γ : Ctx n) (M N T : Tm n) u a0 a1
      (h0 : wt u a0) (h1 : wt u a1) (hUa0 : wt a0 tuniv) (hUa1 : wt a1 tuniv),
      le a0 a1 -> EqVal k Γ M N T h0 -> Val k Γ T Core.tuniv hUa1 -> EqVal k Γ M N T h1)
  /\ (forall n (Γ : Ctx n) (M T : Tm n) u a0 a1
      (h0 : wt u a0) (h1 : wt u a1),
      le a0 a1 -> Val k Γ M T h1 -> Val k Γ M T h0)
  /\ (forall n (Γ : Ctx n) (M N T : Tm n) u a0 a1
      (h0 : wt u a0) (h1 : wt u a1),
      le a0 a1 -> EqVal k Γ M N T h1 -> EqVal k Γ M N T h0)
  /\ (forall n (Γ : Ctx n) (M T : Tm n) u u' a
      (h0 : wt u' a) (h1 : wt u a),
      le u' u -> Val k Γ M T h1 -> Val k Γ M T h0)
  /\ (forall n (Γ : Ctx n) (M N T : Tm n) u u' a
      (h0 : wt u' a) (h1 : wt u a),
      le u' u -> EqVal k Γ M N T h1 -> EqVal k Γ M N T h0).

Lemma upValPi (k : nat) (IH : UDR k)
  {n} (Γ : Ctx n) (M T : Tm n) f a g a' g'
  (h0 : wt (abs f) (tpi a' g')) (h1 : wt (abs f) (tpi a g))
  (hUa1 : wt (tpi a g) tuniv)
  (LEa : le a' a) (LEg : le_fun g' g) :
  Val (S k) Γ M T h0 -> Val (S k) Γ T Core.tuniv hUa1 -> Val (S k) Γ M T h1.
Proof.
  move=> V VT.
  have h0ty : wt (tpi a' g') tuniv := wt_abs_ty h0.
  rewrite Val_abs.
  rewrite Val_abs in V.
  rewrite Val_tuniv in VT.
  destruct V as [_ VPi0].
  split. { eapply ValTy_irr; exact VT. }
  cbn [Rec.ValPi] in VPi0. destruct VPi0 as [A0 [B0 [HR0 [PAV0 PAE0]]]].
  cbn [Rec.ValTy] in VT. destruct VT as [AT [BT [HRt [TyA0 [TyB0 [vld [VDomT [PEV PEE]]]]]]]].
  have [E1 E2] := HeadRed_tpi_det HR0 HRt. subst AT BT.
  have Vg  : valid_fun g  by eauto with valid.
  have Vg' : valid_fun g' by eauto with valid.
  have UP    := proj1 IH.
  have UPe   := proj1 (proj2 IH).
  have DOWN  := proj1 (proj2 (proj2 IH)).
  have DOWNe := proj1 (proj2 (proj2 (proj2 IH))).
  cbn [Rec.ValPi]. exists A0, B0. split; [ exact HR0 | split ].
  - cbn [Rec.PiAppVal]. move=> u v Sel WT P TyP VP.
    destruct (is_bot (app g u)) eqn:Hb. { apply Val_isbot; exact Hb. }
    have Vf : valid_fun f by eauto with valid.
    have Vu : valid u := wt_valid_tm WT.
    have WT' : wt u a' := wt_Selection (wt_tpi_dom h0ty) Vf (wt_abs_inv1 h0) Sel.
    have NBp : ~ is_bot (app g u) by rewrite Hb.
    have hT0 : wt (app g' u) tuniv := wt_tpi_inv2 h0ty Vu erefl.
    have hT1 : wt (app g u) tuniv := wt_tpi_inv2 hUa1 Vu erefl.
    have leC : le (app g' u) (app g u) by (apply le_fun_mono; eauto with valid).
    have VP0 := DOWN n Γ P A0 u a' a WT' WT LEa VP.
    have Vcod0 := PAV0 u v Sel WT' P TyP VP0.
    have RES := proj1 (proj2 (proj2 (proj2 (proj2 IH)))).
    have [u_g [v_g [Sel_g [Le_g Eq_g]]]] := selectionBelow Vg Vu.
    have WT_g : wt u_g a := wt_Selection (wt_tpi_dom hUa1) Vg (wt_tpi_keys hUa1) Sel_g.
    have VP_g : Val k Γ P A0 WT_g := RES n Γ P A0 u u_g a WT_g WT Le_g VP.
    have Vty := PEV u_g v_g Sel_g WT_g P TyP VP_g.
    subst v_g.
    have Vfin := UP n Γ (Core.app M P) B0[P..] v (app g' u) (app g u)
                   (wt_Selection_abs h0 Sel) (wt_Selection_abs h1 Sel) hT0 hT1
                   leC Vcod0 ltac:(eapply Val_irr; exact Vty).
    exact Vfin.
  - cbn [Rec.PiAppEq]. move=> u v Sel WT N1 N2 Cv EV.
    destruct (is_bot (app g u)) eqn:Hb. { apply EqVal_isbot; exact Hb. }
    have Vf : valid_fun f by eauto with valid.
    have Vu : valid u := wt_valid_tm WT.
    have WT' : wt u a' := wt_Selection (wt_tpi_dom h0ty) Vf (wt_abs_inv1 h0) Sel.
    have NBp : ~ is_bot (app g u) by rewrite Hb.
    have hT0 : wt (app g' u) tuniv := wt_tpi_inv2 h0ty Vu erefl.
    have hT1 : wt (app g u) tuniv := wt_tpi_inv2 hUa1 Vu erefl.
    have leC : le (app g' u) (app g u) by (apply le_fun_mono; eauto with valid).
    have EV0 := DOWNe n Γ N1 N2 A0 u a' a WT' WT LEa EV.
    have Ecod0 := PAE0 u v Sel WT' N1 N2 Cv EV0.
    have RESe := proj2 (proj2 (proj2 (proj2 (proj2 IH)))).
    have [u_g [v_g [Sel_g [Le_g Eq_g]]]] := selectionBelow Vg Vu.
    have WT_g : wt u_g a := wt_Selection (wt_tpi_dom hUa1) Vg (wt_tpi_keys hUa1) Sel_g.
    have EV_g : EqVal k Γ N1 N2 A0 WT_g := RESe n Γ N1 N2 A0 u u_g a WT_g WT Le_g EV.
    have Ety := PEE u_g v_g Sel_g WT_g N1 N2 Cv EV_g.
    subst v_g.
    have Vty : Val k Γ B0[N1..] Core.tuniv hT1 by (eapply Val_irr; eapply EqVal_Val1; exact Ety).
    have Efin := UPe n Γ (Core.app M N1) (Core.app M N2) B0[N1..] v (app g' u) (app g u)
                   (wt_Selection_abs h0 Sel) (wt_Selection_abs h1 Sel) hT0 hT1
                   leC Ecod0 ltac:(eapply Val_irr; exact Vty).
    exact Efin.
Qed.

Lemma upEqValPi (k : nat) (IH : UDR k)
  {n} (Γ : Ctx n) (M N T : Tm n) f a g a' g'
  (h0 : wt (abs f) (tpi a' g')) (h1 : wt (abs f) (tpi a g))
  (hUa1 : wt (tpi a g) tuniv)
  (LEa : le a' a) (LEg : le_fun g' g) :
  EqVal (S k) Γ M N T h0 -> Val (S k) Γ T Core.tuniv hUa1 -> EqVal (S k) Γ M N T h1.
Proof.
  move=> EV VT.
  have VM0 : Val (S k) Γ M T h0 by (eapply EqVal_Val1; exact EV).
  have VN0 : Val (S k) Γ N T h0 by (eapply EqVal_Val2; exact EV).
  have VM1 : Val (S k) Γ M T h1.
  { eapply (upValPi IH); [ exact LEa | exact LEg | exact VM0 | exact VT ]. }
  have VN1 : Val (S k) Γ N T h1.
  { eapply (upValPi IH); [ exact LEa | exact LEg | exact VN0 | exact VT ]. }
  rewrite Val_abs in VM1. destruct VM1 as [_ VPiM1].
  rewrite Val_abs in VN1. destruct VN1 as [_ VPiN1].
  rewrite EqVal_abs in EV. destruct EV as [_ [_ [_ EPi0]]].
  rewrite EqVal_abs.
  split; [ | split; [ exact VPiM1 | split; [ exact VPiN1 | ] ] ].
  { rewrite Val_tuniv in VT. eapply ValTy_irr; exact VT. }
  cbn [Rec.EqValPi] in EPi0. destruct EPi0 as [A0 [B0 [HR0 PAEV0]]].
  rewrite Val_tuniv in VT. cbn [Rec.ValTy] in VT.
  destruct VT as [AT [BT [HRt [TyA0 [TyB0 [vld [VDomT [PEV PEE]]]]]]]].
  have [E1 E2] := HeadRed_tpi_det HR0 HRt. subst AT BT.
  have Vg  : valid_fun g  by eauto with valid.
  have Vg' : valid_fun g' by eauto with valid.
  have UPe  := proj1 (proj2 IH).
  have DOWN := proj1 (proj2 (proj2 IH)).
  cbn [Rec.EqValPi]. exists A0, B0. split; [ exact HR0 | ].
  cbn [Rec.PiAppEqVal]. move=> u v Sel WT P TyP VP.
  destruct (is_bot (app g u)) eqn:Hb. { apply EqVal_isbot; exact Hb. }
  have Vf : valid_fun f by eauto with valid.
  have Vu : valid u := wt_valid_tm WT.
  have WT' : wt u a' := wt_Selection (wt_tpi_dom (wt_abs_ty h0)) Vf (wt_abs_inv1 h0) Sel.
  have NBp : ~ is_bot (app g u) by rewrite Hb.
  have hT0 : wt (app g' u) tuniv := wt_tpi_inv2 (wt_abs_ty h0) Vu erefl.
  have hT1 : wt (app g u) tuniv := wt_tpi_inv2 hUa1 Vu erefl.
  have leC : le (app g' u) (app g u) by (apply le_fun_mono; eauto with valid).
  have VP0 := DOWN n Γ P A0 u a' a WT' WT LEa VP.
  have Ecod0 := PAEV0 u v Sel WT' P TyP VP0.
  have RES := proj1 (proj2 (proj2 (proj2 (proj2 IH)))).
  have [u_g [v_g [Sel_g [Le_g Eq_g]]]] := selectionBelow Vg Vu.
  have WT_g : wt u_g a := wt_Selection (wt_tpi_dom hUa1) Vg (wt_tpi_keys hUa1) Sel_g.
  have VP_g : Val k Γ P A0 WT_g := RES n Γ P A0 u u_g a WT_g WT Le_g VP.
  have Vty := PEV u_g v_g Sel_g WT_g P TyP VP_g.
  subst v_g.
  have Efin := UPe n Γ (Core.app M P) (Core.app N P) B0[P..] v (app g' u) (app g u)
                 (wt_Selection_abs h0 Sel) (wt_Selection_abs h1 Sel) hT0 hT1
                 leC Ecod0 ltac:(eapply Val_irr; exact Vty).
  exact Efin.
Qed.

Lemma downValPi (k : nat) (IH : UDR k)
  {n} (Γ : Ctx n) (M T : Tm n) f a g a' g'
  (h1 : wt (abs f) (tpi a g)) (h0 : wt (abs f) (tpi a' g'))
  (LEa : le a' a) (LEg : le_fun g' g) :
  Val (S k) Γ M T h1 -> Val (S k) Γ T Core.tuniv (wt_abs_ty h0) -> Val (S k) Γ M T h0.
Proof.
  move=> V VTS.
  rewrite Val_abs.
  rewrite Val_abs in V. destruct V as [VTyB VPiB].
  rewrite Val_tuniv in VTS.
  split. { eapply ValTy_irr; exact VTS. }
  cbn [Rec.ValTy] in VTyB. destruct VTyB as [AT [BT [HRt [TyA0 [TyB0 [vld [VDomB [PEV_B PEE_B]]]]]]]].
  cbn [Rec.ValPi] in VPiB. destruct VPiB as [A0 [B0 [HR0 [PAV_B PAE_B]]]].
  have [E1 E2] := HeadRed_tpi_det HR0 HRt. subst AT BT.
  have Vg  : valid_fun g  by eauto with valid.
  have Vg' : valid_fun g' by eauto with valid.
  have UP    := proj1 IH.
  have UPe   := proj1 (proj2 IH).
  have DOWN  := proj1 (proj2 (proj2 IH)).
  have DOWNe := proj1 (proj2 (proj2 (proj2 IH))).
  have hUab : wt a tuniv := wt_tpi_dom (wt_abs_ty h1).
  have hUab' : wt a' tuniv := wt_tpi_dom (wt_abs_ty h0).
  cbn [Rec.ValPi]. exists A0, B0. split; [ exact HR0 | split ].
  - cbn [Rec.PiAppVal]. move=> u v Sel WT P TyP VP.
    have Vu : valid u := wt_valid_tm WT.
    have Vf : valid_fun f by eauto with valid.
    have WT1 : wt u a := wt_le WT LEa hUab' hUab.
    have leC : le (app g' u) (app g u) by (apply le_fun_mono; eauto with valid).
    have VPb := UP n Γ P A0 u a' a WT WT1 hUab' hUab LEa VP ltac:(eapply Val_irr; exact VDomB).
    have Vcodb := PAV_B u v Sel WT1 P TyP VPb.
    have Vfin := DOWN n Γ (Core.app M P) B0[P..] v (app g' u) (app g u)
                   (wt_Selection_abs h0 Sel) (wt_Selection_abs h1 Sel) leC Vcodb.
    exact Vfin.
  - cbn [Rec.PiAppEq]. move=> u v Sel WT N1 N2 Cv EV.
    have Vu : valid u := wt_valid_tm WT.
    have Vf : valid_fun f by eauto with valid.
    have WT1 : wt u a := wt_le WT LEa hUab' hUab.
    have leC : le (app g' u) (app g u) by (apply le_fun_mono; eauto with valid).
    have EVb := UPe n Γ N1 N2 A0 u a' a WT WT1 hUab' hUab LEa EV ltac:(eapply Val_irr; exact VDomB).
    have Ecodb := PAE_B u v Sel WT1 N1 N2 Cv EVb.
    have Efin := DOWNe n Γ (Core.app M N1) (Core.app M N2) B0[N1..] v (app g' u) (app g u)
                   (wt_Selection_abs h0 Sel) (wt_Selection_abs h1 Sel) leC Ecodb.
    exact Efin.
Qed.

Lemma downEqValPi (k : nat) (IH : UDR k)
  {n} (Γ : Ctx n) (M N T : Tm n) f a g a' g'
  (h1 : wt (abs f) (tpi a g)) (h0 : wt (abs f) (tpi a' g'))
  (LEa : le a' a) (LEg : le_fun g' g) :
  EqVal (S k) Γ M N T h1 -> Val (S k) Γ T Core.tuniv (wt_abs_ty h0) -> EqVal (S k) Γ M N T h0.
Proof.
  move=> EV VTS.
  have VM1 : Val (S k) Γ M T h1 by (eapply EqVal_Val1; exact EV).
  have VN1 : Val (S k) Γ N T h1 by (eapply EqVal_Val2; exact EV).
  have VMS : Val (S k) Γ M T h0.
  { eapply (downValPi IH); [ exact LEa | exact LEg | exact VM1 | exact VTS ]. }
  have VNS : Val (S k) Γ N T h0.
  { eapply (downValPi IH); [ exact LEa | exact LEg | exact VN1 | exact VTS ]. }
  rewrite Val_abs in VMS. destruct VMS as [_ VPiMS].
  rewrite Val_abs in VNS. destruct VNS as [_ VPiNS].
  rewrite EqVal_abs.
  split; [ | split; [ exact VPiMS | split; [ exact VPiNS | ] ] ].
  { rewrite Val_tuniv in VTS. eapply ValTy_irr; exact VTS. }
  rewrite Val_abs in VM1. destruct VM1 as [VTyB _].
  rewrite EqVal_abs in EV. destruct EV as [_ [_ [_ EPiB]]].
  cbn [Rec.ValTy] in VTyB. destruct VTyB as [AT [BT [HRt [TyA0 [TyB0 [vld [VDomB [PEV_B PEE_B]]]]]]]].
  cbn [Rec.EqValPi] in EPiB. destruct EPiB as [A0 [B0 [HR0 PAEV_B]]].
  have [E1 E2] := HeadRed_tpi_det HR0 HRt. subst AT BT.
  have Vg  : valid_fun g  by eauto with valid.
  have Vg' : valid_fun g' by eauto with valid.
  have UP    := proj1 IH.
  have DOWNe := proj1 (proj2 (proj2 (proj2 IH))).
  have hUab : wt a tuniv := wt_tpi_dom (wt_abs_ty h1).
  have hUab' : wt a' tuniv := wt_tpi_dom (wt_abs_ty h0).
  cbn [Rec.EqValPi]. exists A0, B0. split; [ exact HR0 | ].
  cbn [Rec.PiAppEqVal]. move=> u v Sel WT P TyP VP.
  have Vu : valid u := wt_valid_tm WT.
  have Vf : valid_fun f by eauto with valid.
  have WT1 : wt u a := wt_le WT LEa hUab' hUab.
  have leC : le (app g' u) (app g u) by (apply le_fun_mono; eauto with valid).
  have VPb := UP n Γ P A0 u a' a WT WT1 hUab' hUab LEa VP ltac:(eapply Val_irr; exact VDomB).
  have Ecodb := PAEV_B u v Sel WT1 P TyP VPb.
  have Efin := DOWNe n Γ (Core.app M P) (Core.app N P) B0[P..] v (app g' u) (app g u)
                 (wt_Selection_abs h0 Sel) (wt_Selection_abs h1 Sel) leC Ecodb.
  exact Efin.
Qed.


(* restrictVal: shrink the *element* witness [u' <= u] at a fixed type
   [a].  The semantic content of [Val] is selected by [a]; the element
   [u] only matters in the [tuniv] (type-code), [tnat] (numeral) and
   [tpi] (function-value) branches.  Every recursive use lands at level
   [k] (= [IH]): [succ] uses [restrictVal] on the predecessor; the
   type-code [tpi] case uses [restrictVal] (domain) + [upVal] (args);
   the function-value [abs] case transfers by the universal PiApp edge.
   Mirrors the four Pi lemmas. *)
Lemma restrictVal_step (k : nat) (IH : UDR k) :
  forall n (Γ : Ctx n) (M T : Tm n) u u' a
    (h0 : wt u' a) (h1 : wt u a),
    le u' u -> Val (S k) Γ M T h1 -> Val (S k) Γ M T h0.
Proof.
  have UP    := proj1 IH.
  have UPe   := proj1 (proj2 IH).
  have RES   := proj1 (proj2 (proj2 (proj2 (proj2 IH)))).
  have RESe  := proj2 (proj2 (proj2 (proj2 (proj2 IH)))).
  move=> n Γ M T u u' a h0 h1 LE V.
  dependent destruction h1.
  - (* wt_bot: u = bot, so u' = bot *)
    have E := le_bot_inv _ LE. subst u'. apply Val_Bot.
  - (* wt_tuniv: u = tuniv, a = tuniv *)
    rewrite Val_tuniv. dependent destruction h0; cbn [Rec.ValTy];
      first [ exact I | by autorewrite with le in LE ].
  - (* wt_tnat: u = tnat, a = tuniv *)
    rewrite Val_tuniv. dependent destruction h0; cbn [Rec.ValTy];
      first [ exact I | by autorewrite with le in LE ].
  - (* wt_zero: u = zero, a = tnat *)
    dependent destruction h0.
    + apply Val_Bot.
    + rewrite Val_zero. rewrite Val_zero in V. exact V.
    + by autorewrite with le in LE.
  - (* wt_succ: u = succ w, a = tnat *)
    rewrite Val_succ in V. destruct V as [M1 [HR V1]].
    dependent destruction h0.
    + apply Val_Bot.
    + by autorewrite with le in LE.
    + rewrite le_succ in LE.
      rewrite Val_succ. exists M1. split; [ exact HR | ].
      eapply Val_irr.
      eapply (RES _ Γ M1 Core.tnat _ _ tnat); [ exact LE | exact V1 ].
    Unshelve. exact h0.
  - (* wt_tpi: u = tpi b g (type-code), a = tuniv -- edge reconstruction *)
    rewrite Val_tuniv in V. cbn [Rec.ValTy] in V.
    destruct V as [A [B [HRM [TyA [TyB [vld [VDom [PEV PEE]]]]]]]].
    dependent destruction h0.
    + apply Val_Bot.
    + by autorewrite with le in LE.
    + by autorewrite with le in LE.
    + rewrite le_pi in LE. case/andP: LE => LEb LEg.
      rewrite Val_tuniv. cbn [Rec.ValTy].
      have Vg  : valid_fun g  by eauto with valid.
      have Vg0 : valid_fun g0 by eauto with valid.
      exists A, B.
      split; [ exact HRM | ]. split; [ exact TyA | ]. split; [ exact TyB | ].
      split; [ exact i | ].
      split. { eapply Val_irr. eapply (RES _ Γ A Core.tuniv a0 a tuniv); [ exact LEb | exact VDom ]. Unshelve. exact h0. }
      have HTbig : wt (tpi a0 g0) tuniv by (eapply wt_tpi; eauto).
      have HTsmall : wt (tpi a g) tuniv by (eapply wt_tpi; eauto).
      split.
      * (* PiEdgeVal at (a, g), over a Selection of the smaller graph g *)
        cbn [Rec.PiEdgeVal]. move=> u0 v0 Sel0 WT0 N0 TyN0 VN0.
        have Vu0 : valid u0 := wt_valid_tm WT0.
        (* lift the target selection to the bigger graph g0 at the same key *)
        have [u1 [v1 [Sel1 [Le1 Eq1]]]] := selectionBelow Vg0 Vu0.
        have WTu1 : wt u1 a0 := wt_Selection (wt_tpi_dom HTbig) Vg0 (wt_tpi_keys HTbig) Sel1.
        have WTu0b : wt u0 a0 := wt_le WT0 LEb h0 h1.
        have VN0b : Val k Γ N0 A WTu0b
          by (eapply (UP _ Γ N0 A u0 a a0 WT0 WTu0b h0 h1);
                [ exact LEb | exact VN0 | eapply Val_irr; exact VDom ]).
        have VN1 : Val k Γ N0 A WTu1
          by (eapply (RES _ Γ N0 A u0 u1 a0 WTu1 WTu0b); [ exact Le1 | exact VN0b ]).
        have Res := PEV u1 v1 Sel1 WTu1 N0 TyN0 VN1.
        subst v1.
        have leV : le v0 (app g0 u0) := Selection_le_app Vg Vg0 LEg Vu0 Sel0.
        eapply Val_irr.
        eapply (RES _ Γ B[N0..] Core.tuniv (app g0 u0) v0 tuniv); [ exact leV | exact Res ].
        Unshelve.
        all: first [ exact (wt_Selection_codU HTsmall Sel0) | exact (wt_Selection_codU HTbig Sel1) ].
      * (* PiEdgeEq at (a, g), over a Selection of the smaller graph g *)
        cbn [Rec.PiEdgeEq]. move=> u0 v0 Sel0 WT0 N1 N2 Cv EV0.
        have Vu0 : valid u0 := wt_valid_tm WT0.
        have [u1 [v1 [Sel1 [Le1 Eq1]]]] := selectionBelow Vg0 Vu0.
        have WTu1 : wt u1 a0 := wt_Selection (wt_tpi_dom HTbig) Vg0 (wt_tpi_keys HTbig) Sel1.
        have WTu0b : wt u0 a0 := wt_le WT0 LEb h0 h1.
        have EVb : EqVal k Γ N1 N2 A WTu0b
          by (eapply (UPe _ Γ N1 N2 A u0 a a0 WT0 WTu0b h0 h1);
                [ exact LEb | exact EV0 | eapply Val_irr; exact VDom ]).
        have EV1 : EqVal k Γ N1 N2 A WTu1
          by (eapply (RESe _ Γ N1 N2 A u0 u1 a0 WTu1 WTu0b); [ exact Le1 | exact EVb ]).
        have Res := PEE u1 v1 Sel1 WTu1 N1 N2 Cv EV1.
        subst v1.
        have leV : le v0 (app g0 u0) := Selection_le_app Vg Vg0 LEg Vu0 Sel0.
        eapply EqVal_irr.
        eapply (RESe _ Γ B[N1..] B[N2..] Core.tuniv (app g0 u0) v0 tuniv);
          [ exact leV | exact Res ].
        Unshelve.
        all: first [ exact (wt_Selection_codU HTsmall Sel0) | exact (wt_Selection_codU HTbig Sel1) ].
        
  - (* wt_abs: source value graph [f0] (h1), shrink to target [f] (h0),
       [le_fun f f0], same type [tpi a g].  Mirrors restrictPiAppVal2-sel:
       for a target selection (u,v) we [selectionBelow] the source graph
       [f0] at [u] (giving an [f0]-join [u0 <= u]), restrict the argument
       to [u0], apply the source edge, then transport the result up
       ([u0 -> u] on the codomain type) and shrink the element
       ([v0 -> v], via [Selection_le_app]). *)
    rewrite Val_abs in V. destruct V as [VTyT VPi1].
    dependent destruction h0.
    + apply Val_Bot.
    + rewrite le_abs in LE.
      rewrite Val_abs.
      split. { eapply ValTy_irr; exact VTyT. }
      cbn [Rec.ValPi] in VPi1. destruct VPi1 as [A0 [B0 [HR0 [PAV1 PAE1]]]].
      have VTyTc := VTyT. cbn [Rec.ValTy] in VTyTc.
      destruct VTyTc as [AT [BT [HRt [TyA0 [TyB0 [vldT [VDomT [PEV_T PEE_T]]]]]]]].
      have [E1 E2] := HeadRed_tpi_det HR0 HRt. subst AT BT.
      have VFs : valid_fun f0 by eauto with valid.
      have VFt : valid_fun f by eauto with valid.
      cbn [Rec.ValPi]. exists A0, B0. split; [ exact HR0 | split ].
      * (* PiAppVal at the target value graph [f] *)
        cbn [Rec.PiAppVal]. move=> u v Sel WT P TyP VP.
        have Vu : valid u := wt_valid_tm WT.
        have [u0 [v0 [Sel0 [Le0 Eq0]]]] := selectionBelow VFs Vu.
        have WTu0 : wt u0 a := wt_Selection (wt_tpi_dom h1) VFs (wt_abs_inv1 (wt_abs w1 w2 i0 h1)) Sel0.
        have VPu0 : Val k Γ P A0 WTu0
          by (eapply (RES _ Γ P A0 u u0 a WTu0 WT); [ exact Le0 | exact VP ]).
        have Res := PAV1 u0 v0 Sel0 WTu0 P TyP VPu0.
        destruct (is_bot (app g u)) eqn:Hb. { apply Val_isbot; exact Hb. }
        have NBg : ~ is_bot (app g u) by rewrite Hb.
        have Tu  : wt (app g u) tuniv := wt_tpi_inv2 h1 Vu erefl.
        have Tu0 : wt (app g u0) tuniv := wt_tpi_inv2 h1 (wt_valid_tm WTu0) erefl.
        have leTy : le (app g u0) (app g u) by (apply le_fun_mono_arg; eauto with valid).
        have HTg : wt (tpi a g) tuniv := h1.
        have Vgt : valid_fun g by eauto with valid.
        have [ug [vg [Selg [Leg Eqg]]]] := selectionBelow Vgt Vu.
        have WTug : wt ug a := wt_Selection (wt_tpi_dom HTg) Vgt (wt_tpi_keys HTg) Selg.
        have VPug : Val k Γ P A0 WTug
          by (eapply (RES _ Γ P A0 u ug a WTug WT); [ exact Leg | exact VP ]).
        have Vty := PEV_T ug vg Selg WTug P TyP VPug.
        subst vg.
        have hVgU : wt v0 (app g u) :=
          wt_le (wt_Selection_abs (wt_abs w1 w2 i0 h1) Sel0) leTy Tu0 Tu.
        have ResUp := UP n Γ (Core.app M P) B0[P..] v0 (app g u0) (app g u)
                         (wt_Selection_abs (wt_abs w1 w2 i0 h1) Sel0) hVgU Tu0 Tu
                         leTy Res ltac:(eapply Val_irr; exact Vty).
        have levg : le v v0.
        { have H := Selection_le_app VFt VFs LE Vu Sel. rewrite Eq0 in H. exact H. }
        eapply (RES _ Γ (Core.app M P) B0[P..] v0 v (app g u)
                   (wt_Selection_abs (wt_abs w w0 i h0) Sel) hVgU);
          [ exact levg | exact ResUp ].
      * (* PiAppEq at the target value graph [f] *)
        cbn [Rec.PiAppEq]. move=> u v Sel WT N1 N2 Cv EV.
        have Vu : valid u := wt_valid_tm WT.
        have [u0 [v0 [Sel0 [Le0 Eq0]]]] := selectionBelow VFs Vu.
        have WTu0 : wt u0 a := wt_Selection (wt_tpi_dom h1) VFs (wt_abs_inv1 (wt_abs w1 w2 i0 h1)) Sel0.
        have EVu0 : EqVal k Γ N1 N2 A0 WTu0
          by (eapply (RESe _ Γ N1 N2 A0 u u0 a WTu0 WT); [ exact Le0 | exact EV ]).
        have Res := PAE1 u0 v0 Sel0 WTu0 N1 N2 Cv EVu0.
        destruct (is_bot (app g u)) eqn:Hb. { apply EqVal_isbot; exact Hb. }
        have NBg : ~ is_bot (app g u) by rewrite Hb.
        have Tu  : wt (app g u) tuniv := wt_tpi_inv2 h1 Vu erefl.
        have Tu0 : wt (app g u0) tuniv := wt_tpi_inv2 h1 (wt_valid_tm WTu0) erefl.
        have leTy : le (app g u0) (app g u) by (apply le_fun_mono_arg; eauto with valid).
        have HTg : wt (tpi a g) tuniv := h1.
        have Vgt : valid_fun g by eauto with valid.
        have [ug [vg [Selg [Leg Eqg]]]] := selectionBelow Vgt Vu.
        have WTug : wt ug a := wt_Selection (wt_tpi_dom HTg) Vgt (wt_tpi_keys HTg) Selg.
        have EVug : EqVal k Γ N1 N2 A0 WTug
          by (eapply (RESe _ Γ N1 N2 A0 u ug a WTug WT); [ exact Leg | exact EV ]).
        have Ety := PEE_T ug vg Selg WTug N1 N2 Cv EVug.
        subst vg.
        have Vty : Val k Γ B0[N1..] Core.tuniv Tu by (eapply Val_irr; eapply EqVal_Val1; exact Ety).
        have hVgU : wt v0 (app g u) :=
          wt_le (wt_Selection_abs (wt_abs w1 w2 i0 h1) Sel0) leTy Tu0 Tu.
        have ResUp := UPe n Γ (Core.app M N1) (Core.app M N2) B0[N1..] v0 (app g u0) (app g u)
                         (wt_Selection_abs (wt_abs w1 w2 i0 h1) Sel0) hVgU Tu0 Tu
                         leTy Res ltac:(eapply Val_irr; exact Vty).
        have levg : le v v0.
        { have H := Selection_le_app VFt VFs LE Vu Sel. rewrite Eq0 in H. exact H. }
        eapply (RESe _ Γ (Core.app M N1) (Core.app M N2) B0[N1..] v0 v (app g u)
                   (wt_Selection_abs (wt_abs w w0 i h0) Sel) hVgU);
          [ exact levg | exact ResUp ].
Qed.

(* restrictEqVal: the binary analog of [restrictVal_step]. *)
Lemma restrictEqVal_step (k : nat) (IH : UDR k) :
  forall n (Γ : Ctx n) (M N T : Tm n) u u' a
    (h0 : wt u' a) (h1 : wt u a),
    le u' u -> EqVal (S k) Γ M N T h1 -> EqVal (S k) Γ M N T h0.
Proof.
  have UP    := proj1 IH.
  have UPe   := proj1 (proj2 IH).
  have RES   := proj1 (proj2 (proj2 (proj2 (proj2 IH)))).
  have RESe  := proj2 (proj2 (proj2 (proj2 (proj2 IH)))).
  move=> n Γ M N T u u' a h0 h1 LE V.
  dependent destruction h1.
  - (* wt_bot *)
    have E := le_bot_inv _ LE. subst u'. apply EqVal_Bot.
  - (* wt_tuniv *)
    rewrite EqVal_tuniv. dependent destruction h0; cbn [Rec.ValTy Rec.EqValTy];
      first [ (repeat split; exact I) | by autorewrite with le in LE ].
  - (* wt_tnat *)
    rewrite EqVal_tuniv. dependent destruction h0; cbn [Rec.ValTy Rec.EqValTy];
      first [ (repeat split; exact I) | by autorewrite with le in LE ].
  - (* wt_zero *)
    rewrite EqVal_zero in V. destruct V as [HRM HRN].
    dependent destruction h0.
    + apply EqVal_Bot.
    + rewrite EqVal_zero. split; [ exact HRM | exact HRN ].
    + by autorewrite with le in LE.
  - (* wt_succ *)
    rewrite EqVal_succ in V. destruct V as [M1 [HRM [N1 [HRN EV1]]]].
    dependent destruction h0.
    + apply EqVal_Bot.
    + by autorewrite with le in LE.
    + rewrite le_succ in LE.
      rewrite EqVal_succ. exists M1. split; [ exact HRM | ].
      exists N1. split; [ exact HRN | ].
      eapply EqVal_irr.
      eapply (RESe _ Γ M1 N1 Core.tnat _ _ tnat); [ exact LE | exact EV1 ].
  - (* wt_tpi: type-code -- EqValTy edge reconstruction (PiEdgeEqTy) *)
    rewrite EqVal_tuniv in V. destruct V as [VTyM1 [VTyN1 EQT1]].
    dependent destruction h0.
    + apply EqVal_Bot.
    + by autorewrite with le in LE.
    + by autorewrite with le in LE.
    + rewrite le_pi in LE. case/andP: LE => LEb LEg.
      have Vg  : valid_fun g  by eauto with valid.
      have Vg0 : valid_fun g0 by eauto with valid.
      (* shrink a unary [ValTy] from the [u]-typecode to the [u']-typecode *)
      have RVTy : forall (X : Tm n),
          ValTy k Γ X (wt_tpi h1 w1 w2 i0) -> ValTy k Γ X (wt_tpi h0 w w0 i).
      { move=> X HX. apply Val_ValTy. eapply (restrictVal_step IH).
        2: { apply ValTy_Val; exact HX. }
        rewrite le_pi. apply/andP. split; [ exact LEb | exact LEg ]. }
      cbn [Rec.EqValTy] in EQT1.
      destruct EQT1 as [_ [_ [A [B [HRM [A' [B' [HRN [CvA [CvB [vldT [EDom EPEqT]]]]]]]]]]]].
      rewrite EqVal_tuniv.
      split; [ exact (RVTy M VTyM1) | ]. split; [ exact (RVTy N VTyN1) | ].
      cbn [Rec.EqValTy].
      split; [ exact (RVTy M VTyM1) | ]. split; [ exact (RVTy N VTyN1) | ].
      exists A, B. split; [ exact HRM | ]. exists A', B'. split; [ exact HRN | ].
      split; [ exact CvA | ]. split; [ exact CvB | ].
      split; [ exact i | ].
      split.
      { eapply EqVal_irr.
        eapply (RESe _ Γ A A' Core.tuniv a0 a tuniv); [ exact LEb | exact EDom ]. }
      (* PiEdgeEqTy at (a, g), over a Selection of the smaller graph g *)
      have HTbig : wt (tpi a0 g0) tuniv := wt_tpi h1 w1 w2 i0.
      have HTsmall : wt (tpi a g) tuniv := wt_tpi h0 w w0 i.
      cbn [Rec.PiEdgeEqTy]. move=> u0 v0 Sel0 WT0 P TyP VP.
      have Vu0 : valid u0 := wt_valid_tm WT0.
      have [u1 [v1 [Sel1 [Le1 Eq1]]]] := selectionBelow Vg0 Vu0.
      have WTu1 : wt u1 a0 := wt_Selection (wt_tpi_dom HTbig) Vg0 (wt_tpi_keys HTbig) Sel1.
      have VDomA : Val k Γ A Core.tuniv (wt_tpi_dom (wt_tpi h1 w1 w2 i0))
        by (eapply EqVal_Val1; exact EDom).
      have WTu0b : wt u0 a0 := wt_le WT0 LEb (wt_tpi_dom HTsmall) (wt_tpi_dom HTbig).
      have VPb : Val k Γ P A WTu0b
        by (eapply (UP _ Γ P A u0 a a0 WT0 WTu0b (wt_tpi_dom HTsmall) (wt_tpi_dom HTbig));
              [ exact LEb | exact VP | eapply Val_irr; exact VDomA ]).
      have VP1 : Val k Γ P A WTu1
        by (eapply (RES _ Γ P A u0 u1 a0 WTu1 WTu0b); [ exact Le1 | exact VPb ]).
      have Res := EPEqT u1 v1 Sel1 WTu1 P TyP VP1.
      subst v1.
      have leV : le v0 (app g0 u0) := Selection_le_app Vg Vg0 LEg Vu0 Sel0.
      eapply EqVal_irr.
      exact (RESe _ Γ B[P..] B'[P..] Core.tuniv (app g0 u0) v0 tuniv
                  (wt_Selection_codU HTsmall Sel0) _ leV Res).
  - (* wt_abs: source value graph [f0] (h1), shrink to target [f] (h0).
       The [ValPi] parts come from [restrictVal_step]; the [EqValPi]
       (binary [PiAppEqVal]) edge is reconstructed as in restrictVal_step's
       abs case, via [selectionBelow] on the source graph. *)
    rewrite EqVal_abs in V. destruct V as [VTyT [VPiM1 [VPiN1 EPi1]]].
    dependent destruction h0.
    + apply EqVal_Bot.
    + have LEabs : le (abs f) (abs f0) := LE.
      rewrite le_abs in LE.
      have VM1 : Val (S k) Γ M T (wt_abs w1 w2 i0 h1)
        by (rewrite Val_abs; split; [ exact VTyT | exact VPiM1 ]).
      have VN1 : Val (S k) Γ N T (wt_abs w1 w2 i0 h1)
        by (rewrite Val_abs; split; [ exact VTyT | exact VPiN1 ]).
      have VMS : Val (S k) Γ M T (wt_abs w w0 i h0)
        by (eapply (restrictVal_step IH); [ exact LEabs | exact VM1 ]).
      have VNS : Val (S k) Γ N T (wt_abs w w0 i h0)
        by (eapply (restrictVal_step IH); [ exact LEabs | exact VN1 ]).
      rewrite Val_abs in VMS. destruct VMS as [_ VPiMS].
      rewrite Val_abs in VNS. destruct VNS as [_ VPiNS].
      rewrite EqVal_abs.
      split. { eapply ValTy_irr; exact VTyT. }
      split. { exact VPiMS. }
      split. { exact VPiNS. }
      cbn [Rec.EqValPi] in EPi1. destruct EPi1 as [A0 [B0 [HR0 PAEV1]]].
      have VTyTc := VTyT. cbn [Rec.ValTy] in VTyTc.
      destruct VTyTc as [AT [BT [HRt [TyA0 [TyB0 [vldT [VDomT [PEV_T PEE_T]]]]]]]].
      have [E1 E2] := HeadRed_tpi_det HR0 HRt. subst AT BT.
      have VFs : valid_fun f0 by eauto with valid.
      have VFt : valid_fun f  by eauto with valid.
      cbn [Rec.EqValPi]. exists A0, B0. split; [ exact HR0 | ].
      cbn [Rec.PiAppEqVal]. move=> u v Sel WT P TyP VP.
      have Vu : valid u := wt_valid_tm WT.
      have [u0 [v0 [Sel0 [Le0 Eq0]]]] := selectionBelow VFs Vu.
      have WTu0 : wt u0 a := wt_Selection (wt_tpi_dom h1) VFs (wt_abs_inv1 (wt_abs w1 w2 i0 h1)) Sel0.
      have VPu0 : Val k Γ P A0 WTu0
        by (eapply (RES _ Γ P A0 u u0 a WTu0 WT); [ exact Le0 | exact VP ]).
      have Res := PAEV1 u0 v0 Sel0 WTu0 P TyP VPu0.
      destruct (is_bot (app g u)) eqn:Hb. { apply EqVal_isbot; exact Hb. }
      have NBg : ~ is_bot (app g u) by rewrite Hb.
      have Tu  : wt (app g u) tuniv := wt_tpi_inv2 h1 Vu erefl.
      have Tu0 : wt (app g u0) tuniv := wt_tpi_inv2 h1 (wt_valid_tm WTu0) erefl.
      have leTy : le (app g u0) (app g u) by (apply le_fun_mono_arg; eauto with valid).
      have HTg : wt (tpi a g) tuniv := h1.
      have Vgt : valid_fun g by eauto with valid.
      have [ug [vg [Selg [Leg Eqg]]]] := selectionBelow Vgt Vu.
      have WTug : wt ug a := wt_Selection (wt_tpi_dom HTg) Vgt (wt_tpi_keys HTg) Selg.
      have VPug : Val k Γ P A0 WTug
        by (eapply (RES _ Γ P A0 u ug a WTug WT); [ exact Leg | exact VP ]).
      have Vty := PEV_T ug vg Selg WTug P TyP VPug.
      subst vg.
      have hVgU : wt v0 (app g u) :=
        wt_le (wt_Selection_abs (wt_abs w1 w2 i0 h1) Sel0) leTy Tu0 Tu.
      have ResUp := UPe n Γ (Core.app M P) (Core.app N P) B0[P..] v0 (app g u0) (app g u)
                       (wt_Selection_abs (wt_abs w1 w2 i0 h1) Sel0) hVgU Tu0 Tu
                       leTy Res ltac:(eapply Val_irr; exact Vty).
      have levg : le v v0.
      { have H := Selection_le_app VFt VFs LE Vu Sel. rewrite Eq0 in H. exact H. }
      eapply (RESe _ Γ (Core.app M P) (Core.app N P) B0[P..] v0 v (app g u)
                 (wt_Selection_abs (wt_abs w w0 i h0) Sel) hVgU);
        [ exact levg | exact ResUp ].
  Unshelve.
  all: try eassumption.
  all: eapply (wt_tpi_inv2 (wt_tpi h0 w w0 i) (u := u0)); eauto with valid.
Qed.

(** All six up/down/restrict monotonicity facts, bundled in [UDR k] and proven
    together by induction on the fuel [k]; the named projections appear just
    below. *)
Lemma up_down_restrict : forall k, UDR k.
Proof.
  induction k as [|k IH].
  - unfold UDR. repeat split; intros; exact I.
  - unfold UDR. repeat split.
    + intros n Γ M T u a0 a1 h0 h1 hUa0 hUa1 LE V VT.
      dependent destruction h1.
      * apply Val_Bot.
      * dependent destruction h0; eapply Val_irr; eassumption.
      * dependent destruction h0; eapply Val_irr; eassumption.
      * dependent destruction h0; eapply Val_irr; eassumption.
      * dependent destruction h0; eapply Val_irr; eassumption.
      * dependent destruction h0; eapply Val_irr; eassumption.
      * dependent destruction h0. rewrite le_pi in LE. case/andP: LE => LEa LEg.
        eapply (upValPi IH); [ exact LEa | exact LEg | exact V | exact VT ].
    + intros n Γ M N T u a0 a1 h0 h1 hUa0 hUa1 LE V VT.
      dependent destruction h1.
      * apply EqVal_Bot.
      * dependent destruction h0; eapply EqVal_irr; eassumption.
      * dependent destruction h0; eapply EqVal_irr; eassumption.
      * dependent destruction h0; eapply EqVal_irr; eassumption.
      * dependent destruction h0; eapply EqVal_irr; eassumption.
      * dependent destruction h0; eapply EqVal_irr; eassumption.
      * dependent destruction h0. rewrite le_pi in LE. case/andP: LE => LEa LEg.
        eapply (upEqValPi IH); [ exact LEa | exact LEg | exact V | exact VT ].
    + intros n Γ M T u a0 a1 h0 h1 LE V.
      dependent destruction h1.
      * apply Val_Bot.
      * dependent destruction h0; eapply Val_irr; eassumption.
      * dependent destruction h0; eapply Val_irr; eassumption.
      * dependent destruction h0; eapply Val_irr; eassumption.
      * dependent destruction h0; eapply Val_irr; eassumption.
      * dependent destruction h0; eapply Val_irr; eassumption.
      * dependent destruction h0. rewrite le_pi in LE. case/andP: LE => LEa LEg.
        eapply (downValPi IH); [ exact LEa | exact LEg | exact V | ].
        rewrite Val_abs in V. destruct V as [VTyB _].
        eapply (restrictVal_step IH).
        2: { eapply ValTy_Val. exact VTyB. }
        rewrite le_pi. apply/andP. split; [ exact LEa | exact LEg ].
    + intros n Γ M N T u a0 a1 h0 h1 LE V.
      dependent destruction h1.
      * apply EqVal_Bot.
      * dependent destruction h0; eapply EqVal_irr; eassumption.
      * dependent destruction h0; eapply EqVal_irr; eassumption.
      * dependent destruction h0; eapply EqVal_irr; eassumption.
      * dependent destruction h0; eapply EqVal_irr; eassumption.
      * dependent destruction h0; eapply EqVal_irr; eassumption.
      * dependent destruction h0. rewrite le_pi in LE. case/andP: LE => LEa LEg.
        eapply (downEqValPi IH); [ exact LEa | exact LEg | exact V | ].
        rewrite EqVal_abs in V. destruct V as [VTyB _].
        eapply (restrictVal_step IH).
        2: { eapply ValTy_Val. exact VTyB. }
        rewrite le_pi. apply/andP. split; [ exact LEa | exact LEg ].
    + exact (restrictVal_step IH).
    + exact (restrictEqVal_step IH).
  (* A few proof-irrelevant [wt _ tuniv] witnesses are left shelved by the
     [eapply]s above; any inhabitant works (they only index [Val]/[EqVal],
     which are proof-irrelevant -- see [Val_irr]/[EqVal_irr]). *)
  Unshelve. all: eauto using wt_tuniv, wt_tnat, wt_tpi, wt_bot.
Qed.

(** Monotonicity of the relation in the *type* and *value* code, exported as
    six lemmas (Agda: [upVal2-pub]/[downVal2-pub]/[restrictVal2-pub] and their
    [EqVal] versions).  [upVal]/[upEqVal] enlarge the type along [le a0 a1];
    [downVal]/[downEqVal] shrink it; [restrictVal]/[restrictEqVal] shrink the
    value along [le u' u].  All are projections of [up_down_restrict]. *)
Lemma upVal k {n} (Γ : Ctx n) (M T : Tm n) u a0 a1
  (h0 : wt u a0) (h1 : wt u a1) (hUa0 : wt a0 tuniv) (hUa1 : wt a1 tuniv) :
  le a0 a1 -> Val k Γ M T h0 -> Val k Γ T Core.tuniv hUa1 -> Val k Γ M T h1.
Proof. exact (proj1 (up_down_restrict k) n Γ M T u a0 a1 h0 h1 hUa0 hUa1). Qed.

Lemma upEqVal k {n} (Γ : Ctx n) (M N T : Tm n) u a0 a1
  (h0 : wt u a0) (h1 : wt u a1) (hUa0 : wt a0 tuniv) (hUa1 : wt a1 tuniv) :
  le a0 a1 -> EqVal k Γ M N T h0 -> Val k Γ T Core.tuniv hUa1 -> EqVal k Γ M N T h1.
Proof. exact (proj1 (proj2 (up_down_restrict k)) n Γ M N T u a0 a1 h0 h1 hUa0 hUa1). Qed.

Lemma downVal k {n} (Γ : Ctx n) (M T : Tm n) u a0 a1
  (h0 : wt u a0) (h1 : wt u a1) :
  le a0 a1 -> Val k Γ M T h1 -> Val k Γ M T h0.
Proof. exact (proj1 (proj2 (proj2 (up_down_restrict k))) n Γ M T u a0 a1 h0 h1). Qed.

Lemma downEqVal k {n} (Γ : Ctx n) (M N T : Tm n) u a0 a1
  (h0 : wt u a0) (h1 : wt u a1) :
  le a0 a1 -> EqVal k Γ M N T h1 -> EqVal k Γ M N T h0.
Proof. exact (proj1 (proj2 (proj2 (proj2 (up_down_restrict k)))) n Γ M N T u a0 a1 h0 h1). Qed.

Lemma restrictVal k {n} (Γ : Ctx n) (M T : Tm n) u u' a
  (h0 : wt u' a) (h1 : wt u a) :
  le u' u -> Val k Γ M T h1 -> Val k Γ M T h0.
Proof. exact (proj1 (proj2 (proj2 (proj2 (proj2 (up_down_restrict k))))) n Γ M T u u' a h0 h1). Qed.

Lemma restrictEqVal k {n} (Γ : Ctx n) (M N T : Tm n) u u' a
  (h0 : wt u' a) (h1 : wt u a) :
  le u' u -> EqVal k Γ M N T h1 -> EqVal k Γ M N T h0.
Proof. exact (proj2 (proj2 (proj2 (proj2 (proj2 (up_down_restrict k))))) n Γ M N T u u' a h0 h1). Qed.


(* ============================================================ *)
(* ============================================================ *)
(** * Fuel stability (above-rank) *)
(* ============================================================ *)
(* Analogue of Agda's [Validity/Stability.agda] 
   vlU/vlD/vtyU/vtyD/evlU/evlD/evtyU/evtyD.

   Above the ranks of the codes, the fuel-indexed [Val]/[EqVal] are
   independent of the fuel: increasing the fuel does not change the
   relation, because every recursive occurrence in one unfolding step
   lands on a code of strictly smaller rank, which is already saturated
   at the available fuel.  

   The bound is [rk u <= k] / [rk a <= k] (= Agda's [Le (suc (RANK)) (S k)]).
   ============================================================ *)

(* ---- statement shapes for the eight bundled fuel-stability facts ----

   The four top-level facts (FU/FD/FEU/FED) and the four per-edge helper
   facts (HVT/HET/HVP/HEP), each at a fixed fuel [k].  [FuelStable k]
   bundles them so they can be proven by a single induction on [k].
   [HVP]/[HEP] bound BOTH the value rank [rk (abs g)] and the 
   type rank [rk (tpi b f)] — a lambda's value  graph can outrank 
   its type (e.g. [succ zero : tnat]), so the type bound alone is insufficient. *)
Definition FU (k : nat) : Prop :=
  forall n (Γ : Ctx n) (M T : Tm n) u a (h : wt u a),
    rk u < k -> rk a < k -> Val k Γ M T h -> Val (S k) Γ M T h.
Definition FD (k : nat) : Prop :=
  forall n (Γ : Ctx n) (M T : Tm n) u a (h : wt u a),
    rk u < k -> rk a < k -> Val (S k) Γ M T h -> Val k Γ M T h.
Definition FEU (k : nat) : Prop :=
  forall n (Γ : Ctx n) (M N T : Tm n) u a (h : wt u a),
    rk u < k -> rk a < k -> EqVal k Γ M N T h -> EqVal (S k) Γ M N T h.
Definition FED (k : nat) : Prop :=
  forall n (Γ : Ctx n) (M N T : Tm n) u a (h : wt u a),
    rk u < k -> rk a < k -> EqVal (S k) Γ M N T h -> EqVal k Γ M N T h.
Definition HVT (k : nat) : Prop :=
  forall n (Γ : Ctx n) (M : Tm n) u (h : wt u tuniv),
    rk u <= k ->
    (ValTy k Γ M h -> ValTy (S k) Γ M h) /\ (ValTy (S k) Γ M h -> ValTy k Γ M h).
Definition HET (k : nat) : Prop :=
  forall n (Γ : Ctx n) (M N : Tm n) u (h : wt u tuniv),
    rk u <= k ->
    (EqValTy k Γ M N h -> EqValTy (S k) Γ M N h)
    /\ (EqValTy (S k) Γ M N h -> EqValTy k Γ M N h).
Definition HVP (k : nat) : Prop :=
  forall n (Γ : Ctx n) (M A : Tm n) g b f (h : wt (abs g) (tpi b f)),
    rk (abs g) <= k -> rk (tpi b f) <= k ->
    (ValPi k Γ M A h -> ValPi (S k) Γ M A h) /\ (ValPi (S k) Γ M A h -> ValPi k Γ M A h).
Definition HEP (k : nat) : Prop :=
  forall n (Γ : Ctx n) (M N A : Tm n) g b f (h : wt (abs g) (tpi b f)),
    rk (abs g) <= k -> rk (tpi b f) <= k ->
    (EqValPi k Γ M N A h -> EqValPi (S k) Γ M N A h)
    /\ (EqValPi (S k) Γ M N A h -> EqValPi k Γ M N A h).
Definition FuelStable (k : nat) : Prop :=
  FU k /\ FD k /\ FEU k /\ FED k /\ HVT k /\ HET k /\ HVP k /\ HEP k.

(* ---- promotion of a [Val]/[EqVal] at the constant type [tuniv].
   The type rank [rk tuniv = 1] forces a [bot] case-split: when the
   element is [bot] the relation is trivially total ([Val_Bot]); when it
   is not, [rk e >= 1], so the element rank witnesses [rk tuniv < S k]
   needed by the top-level fact. *)
Lemma Val_tuniv_up (k : nat) (VU : FU (S k)) {n} (Γ : Ctx n) (M : Tm n) e
  (h : wt e tuniv) : rk e <= k -> Val (S k) Γ M Core.tuniv h -> Val (S (S k)) Γ M Core.tuniv h.
Proof.
  move=> He V. destruct (is_bot e) eqn:Hb.
  - have E : e = bot by (apply is_bot_eq; rewrite Hb). subst e. apply Val_Bot.
  - have Hge := rk_pos Hb. apply (VU n Γ M Core.tuniv e tuniv h); [ lia | cbn; lia | exact V ].
Qed.

Lemma Val_tuniv_down (k : nat) (VD : FD (S k)) {n} (Γ : Ctx n) (M : Tm n) e
  (h : wt e tuniv) : rk e <= k -> Val (S (S k)) Γ M Core.tuniv h -> Val (S k) Γ M Core.tuniv h.
Proof.
  move=> He V. destruct (is_bot e) eqn:Hb.
  - have E : e = bot by (apply is_bot_eq; rewrite Hb). subst e. apply Val_Bot.
  - have Hge := rk_pos Hb. apply (VD n Γ M Core.tuniv e tuniv h); [ lia | cbn; lia | exact V ].
Qed.

Lemma EqVal_tuniv_up (k : nat) (EU : FEU (S k)) {n} (Γ : Ctx n) (M N : Tm n) e
  (h : wt e tuniv) : rk e <= k -> EqVal (S k) Γ M N Core.tuniv h -> EqVal (S (S k)) Γ M N Core.tuniv h.
Proof.
  move=> He V. destruct (is_bot e) eqn:Hb.
  - have E : e = bot by (apply is_bot_eq; rewrite Hb). subst e. apply EqVal_Bot.
  - have Hge := rk_pos Hb. apply (EU n Γ M N Core.tuniv e tuniv h); [ lia | cbn; lia | exact V ].
Qed.

Lemma EqVal_tuniv_down (k : nat) (ED : FED (S k)) {n} (Γ : Ctx n) (M N : Tm n) e
  (h : wt e tuniv) : rk e <= k -> EqVal (S (S k)) Γ M N Core.tuniv h -> EqVal (S k) Γ M N Core.tuniv h.
Proof.
  move=> He V. destruct (is_bot e) eqn:Hb.
  - have E : e = bot by (apply is_bot_eq; rewrite Hb). subst e. apply EqVal_Bot.
  - have Hge := rk_pos Hb. apply (ED n Γ M N Core.tuniv e tuniv h); [ lia | cbn; lia | exact V ].
Qed.

(* [tnat] fuel-monotonicity (the [zero]/[succ] structural recursion).  Easy
   (no Pi edges), but recursive on the successor chain; ADMITTED here to keep
   the top-level lemmas free of nested induction. *)
Lemma fuel_Val_tnat : forall (k : nat) {n} (Γ : Ctx n) (M T : Tm n) u (h : wt u tnat),
  rk u < k ->
  (Val k Γ M T h -> Val (S k) Γ M T h) /\ (Val (S k) Γ M T h -> Val k Γ M T h).
Proof.
  induction k as [|k IHk]; first (intros n Γ M T u h Hu; exfalso; lia).
  intros n Γ M T u h Hu. dependent destruction h.
  - (* bot *) split; intros _; apply Val_Bot.
  - (* zero *) rewrite !Val_zero; tauto.
  - (* succ u *)
    have Hrk : rk u < k by (cbn in Hu; lia).
    rewrite !Val_succ.
    split; intros [M1 [HR V1]]; exists M1; (split; [exact HR|]).
    + exact (proj1 (IHk n Γ M1 Core.tnat u (wt_succ_inv (wt_succ h)) Hrk) V1).
    + exact (proj2 (IHk n Γ M1 Core.tnat u (wt_succ_inv (wt_succ h)) Hrk) V1).
Qed.

Lemma fuel_EqVal_tnat : forall (k : nat) {n} (Γ : Ctx n) (M N T : Tm n) u (h : wt u tnat),
  rk u < k ->
  (EqVal k Γ M N T h -> EqVal (S k) Γ M N T h)
  /\ (EqVal (S k) Γ M N T h -> EqVal k Γ M N T h).
Proof.
  induction k as [|k IHk]; first (intros n Γ M N T u h Hu; exfalso; lia).
  intros n Γ M N T u h Hu. dependent destruction h.
  - (* bot *) split; intros _; apply EqVal_Bot.
  - (* zero *) rewrite !EqVal_zero; tauto.
  - (* succ u *)
    have Hrk : rk u < k by (cbn in Hu; lia).
    rewrite !EqVal_succ.
    split; intros [M1 [HRM [N1 [HRN EV1]]]]; exists M1; (split; [exact HRM|]);
      exists N1; (split; [exact HRN|]).
    + exact (proj1 (IHk n Γ M1 N1 Core.tnat u (wt_succ_inv (wt_succ h)) Hrk) EV1).
    + exact (proj2 (IHk n Γ M1 N1 Core.tnat u (wt_succ_inv (wt_succ h)) Hrk) EV1).
Qed.

(* ============================================================
   The eight fuel-stability facts, proven together by one induction
   on the fuel [k].

   Dependency within a level: each per-edge helper at [S k] uses only
   the top-level facts at [S k]; each top-level fact at [S k] uses only
   the per-edge helpers at [k] (its predecessor).  So the induction
   step first establishes the four top-level facts at [S k] (from the
   IH's helpers at [k]) and then the four helpers at [S k] (from the
   just-proven top-level facts).
   ============================================================ *)

(* ---- the four per-edge helpers at level [S k] ----
   Codomain occurrences are at the constant type [tuniv] (type edges)
   or at a genuine codomain element [app f u] (value edges).  The former
   route through the [bot]-split [Val_tuniv_*]/[EqVal_tuniv_*] (the type
   rank [rk tuniv = 1] is not bounded by the element rank); the latter
   go straight through the top-level facts.  Edge arguments are
   re-aligned by the opposite-direction top-level fact at the same
   level. *)

Lemma fuel_ValTy_S (k : nat) (VU : FU (S k)) (VD : FD (S k)) (EU : FEU (S k)) (ED : FED (S k))
  : HVT (S k).
Proof.
  unfold HVT. intros n Γ M u h Hu. dependent destruction h;
    try (split; intro V; cbn [Rec.ValTy] in V |- *; exact V).
  cbn in Hu. split.
  - (* up: ValTy (S k) -> ValTy (S (S k)) *)
    intro V; cbn [Rec.ValTy] in V |- *.
    move: V => [A [B [HR [TA [TB [vld2 [VDom [PEV PEE]]]]]]]].
    exists A, B; do 4 (split; [eassumption|]); split; [|split].
    + apply (Val_tuniv_up VU); [ lia | exact VDom ].
    + cbn [Rec.PiEdgeVal] in PEV |- *. intros u0 v0 Sel WT N0 TN VN.
      move: (rk_Selection_key Sel) (rk_Selection_val Sel) => HK HV.
      have VN' : Val (S k) Γ N0 A WT by (apply (VD n Γ N0 A u0 _ WT); [ lia | lia | exact VN ]).
      apply (Val_tuniv_up VU); [ lia | exact (PEV u0 v0 Sel WT N0 TN VN') ].
    + cbn [Rec.PiEdgeEq] in PEE |- *. intros u0 v0 Sel WT N1 N2 Cv EV.
      move: (rk_Selection_key Sel) (rk_Selection_val Sel) => HK HV.
      have EV' : EqVal (S k) Γ N1 N2 A WT by (apply (ED n Γ N1 N2 A u0 _ WT); [ lia | lia | exact EV ]).
      apply (EqVal_tuniv_up EU); [ lia | exact (PEE u0 v0 Sel WT N1 N2 Cv EV') ].
  - (* down: ValTy (S (S k)) -> ValTy (S k) *)
    intro V; cbn [Rec.ValTy] in V |- *.
    move: V => [A [B [HR [TA [TB [vld2 [VDom [PEV PEE]]]]]]]].
    exists A, B; do 4 (split; [eassumption|]); split; [|split].
    + apply (Val_tuniv_down VD); [ lia | exact VDom ].
    + cbn [Rec.PiEdgeVal] in PEV |- *. intros u0 v0 Sel WT N0 TN VN.
      move: (rk_Selection_key Sel) (rk_Selection_val Sel) => HK HV.
      have VN' : Val (S (S k)) Γ N0 A WT by (apply (VU n Γ N0 A u0 _ WT); [ lia | lia | exact VN ]).
      apply (Val_tuniv_down VD); [ lia | exact (PEV u0 v0 Sel WT N0 TN VN') ].
    + cbn [Rec.PiEdgeEq] in PEE |- *. intros u0 v0 Sel WT N1 N2 Cv EV.
      move: (rk_Selection_key Sel) (rk_Selection_val Sel) => HK HV.
      have EV' : EqVal (S (S k)) Γ N1 N2 A WT by (apply (EU n Γ N1 N2 A u0 _ WT); [ lia | lia | exact EV ]).
      apply (EqVal_tuniv_down ED); [ lia | exact (PEE u0 v0 Sel WT N1 N2 Cv EV') ].
Qed.

Lemma fuel_EqValTy_S (k : nat) (VU : FU (S k)) (VD : FD (S k)) (EU : FEU (S k)) (ED : FED (S k))
  (FVT : HVT (S k)) : HET (S k).
Proof.
  unfold HET. intros n Γ M N u h Hu. dependent destruction h;
    try (split; intro V; cbn [Rec.EqValTy] in V |- *; exact V).
  have Hu' := Hu. cbn in Hu. split.
  - (* up *)
    intro V; cbn [Rec.EqValTy] in V |- *.
    move: V => [VTyM [VTyN [A [B [HRM [A' [B' [HRN [CvA [CvB [vld2 [EDom EPT]]]]]]]]]]]].
    split; [ exact (proj1 (FVT n Γ M _ _ Hu') VTyM) | ].
    split; [ exact (proj1 (FVT n Γ N _ _ Hu') VTyN) | ].
    exists A, B; split; [exact HRM|]; exists A', B'; split; [exact HRN|].
    split; [exact CvA|]; split; [exact CvB|]; split; [exact vld2|]; split.
    + apply (EqVal_tuniv_up EU); [ lia | exact EDom ].
    + cbn [Rec.PiEdgeEqTy] in EPT |- *. intros u0 v0 Sel WTu P TP VP.
      move: (rk_Selection_key Sel) (rk_Selection_val Sel) => HK HV.
      have VP' : Val (S k) Γ P A WTu by (apply (VD n Γ P A u0 _ WTu); [ lia | lia | exact VP ]).
      apply (EqVal_tuniv_up EU); [ lia | exact (EPT u0 v0 Sel WTu P TP VP') ].
  - (* down *)
    intro V; cbn [Rec.EqValTy] in V |- *.
    move: V => [VTyM [VTyN [A [B [HRM [A' [B' [HRN [CvA [CvB [vld2 [EDom EPT]]]]]]]]]]]].
    split; [ exact (proj2 (FVT n Γ M _ _ Hu') VTyM) | ].
    split; [ exact (proj2 (FVT n Γ N _ _ Hu') VTyN) | ].
    exists A, B; split; [exact HRM|]; exists A', B'; split; [exact HRN|].
    split; [exact CvA|]; split; [exact CvB|]; split; [exact vld2|]; split.
    + apply (EqVal_tuniv_down ED); [ lia | exact EDom ].
    + cbn [Rec.PiEdgeEqTy] in EPT |- *. intros u0 v0 Sel WTu P TP VP.
      move: (rk_Selection_key Sel) (rk_Selection_val Sel) => HK HV.
      have VP' : Val (S (S k)) Γ P A WTu by (apply (VU n Γ P A u0 _ WTu); [ lia | lia | exact VP ]).
      apply (EqVal_tuniv_down ED); [ lia | exact (EPT u0 v0 Sel WTu P TP VP') ].
Qed.

Lemma fuel_ValPi_S (k : nat) (VU : FU (S k)) (VD : FD (S k)) (EU : FEU (S k)) (ED : FED (S k))
  : HVP (S k).
Proof.
  unfold HVP. intros n Γ M A g b f h Hu1 Hu2. dependent destruction h.
  cbn in Hu1, Hu2. split.
  - (* up *)
    intro V; cbn [Rec.ValPi] in V |- *.
    move: V => [A0 [B0 [HR [PAV PAE]]]].
    exists A0, B0; split; [exact HR|]; split.
    + cbn [Rec.PiAppVal] in PAV |- *. intros u0 v0 Sel WT P TP VP.
      move: (rk_Selection_key Sel) (rk_Selection_val Sel) (rk_app f u0) => HK HV HA.
      have VP' : Val (S k) Γ P A0 WT by (apply (VD n Γ P A0 u0 _ WT); [ lia | lia | exact VP ]).
      apply (VU n Γ (Core.app M P) B0[P..] v0 (app f u0)); [ lia | lia | exact (PAV u0 v0 Sel WT P TP VP') ].
    + cbn [Rec.PiAppEq] in PAE |- *. intros u0 v0 Sel WT N1 N2 Cv EV.
      move: (rk_Selection_key Sel) (rk_Selection_val Sel) (rk_app f u0) => HK HV HA.
      have EV' : EqVal (S k) Γ N1 N2 A0 WT by (apply (ED n Γ N1 N2 A0 u0 _ WT); [ lia | lia | exact EV ]).
      apply (EU n Γ (Core.app M N1) (Core.app M N2) B0[N1..] v0 (app f u0)); [ lia | lia | exact (PAE u0 v0 Sel WT N1 N2 Cv EV') ].
  - (* down *)
    intro V; cbn [Rec.ValPi] in V |- *.
    move: V => [A0 [B0 [HR [PAV PAE]]]].
    exists A0, B0; split; [exact HR|]; split.
    + cbn [Rec.PiAppVal] in PAV |- *. intros u0 v0 Sel WT P TP VP.
      move: (rk_Selection_key Sel) (rk_Selection_val Sel) (rk_app f u0) => HK HV HA.
      have VP' : Val (S (S k)) Γ P A0 WT by (apply (VU n Γ P A0 u0 _ WT); [ lia | lia | exact VP ]).
      apply (VD n Γ (Core.app M P) B0[P..] v0 (app f u0)); [ lia | lia | exact (PAV u0 v0 Sel WT P TP VP') ].
    + cbn [Rec.PiAppEq] in PAE |- *. intros u0 v0 Sel WT N1 N2 Cv EV.
      move: (rk_Selection_key Sel) (rk_Selection_val Sel) (rk_app f u0) => HK HV HA.
      have EV' : EqVal (S (S k)) Γ N1 N2 A0 WT by (apply (EU n Γ N1 N2 A0 u0 _ WT); [ lia | lia | exact EV ]).
      apply (ED n Γ (Core.app M N1) (Core.app M N2) B0[N1..] v0 (app f u0)); [ lia | lia | exact (PAE u0 v0 Sel WT N1 N2 Cv EV') ].
Qed.

Lemma fuel_EqValPi_S (k : nat) (VU : FU (S k)) (VD : FD (S k)) (EU : FEU (S k)) (ED : FED (S k))
  : HEP (S k).
Proof.
  unfold HEP. intros n Γ M N A g b f h Hu1 Hu2. dependent destruction h.
  cbn in Hu1, Hu2. split.
  - (* up *)
    intro V; cbn [Rec.EqValPi] in V |- *.
    move: V => [A0 [B0 [HR PAEV]]].
    exists A0, B0; split; [exact HR|].
    cbn [Rec.PiAppEqVal] in PAEV |- *. intros u0 v0 Sel WT P TP VP.
    move: (rk_Selection_key Sel) (rk_Selection_val Sel) (rk_app f u0) => HK HV HA.
    have VP' : Val (S k) Γ P A0 WT by (apply (VD n Γ P A0 u0 _ WT); [ lia | lia | exact VP ]).
    apply (EU n Γ (Core.app M P) (Core.app N P) B0[P..] v0 (app f u0)); [ lia | lia | exact (PAEV u0 v0 Sel WT P TP VP') ].
  - (* down *)
    intro V; cbn [Rec.EqValPi] in V |- *.
    move: V => [A0 [B0 [HR PAEV]]].
    exists A0, B0; split; [exact HR|].
    cbn [Rec.PiAppEqVal] in PAEV |- *. intros u0 v0 Sel WT P TP VP.
    move: (rk_Selection_key Sel) (rk_Selection_val Sel) (rk_app f u0) => HK HV HA.
    have VP' : Val (S (S k)) Γ P A0 WT by (apply (VU n Γ P A0 u0 _ WT); [ lia | lia | exact VP ]).
    apply (ED n Γ (Core.app M P) (Core.app N P) B0[P..] v0 (app f u0)); [ lia | lia | exact (PAEV u0 v0 Sel WT P TP VP') ].
Qed.

(* ---- the four top-level facts at level [S k] (from the helpers at [k]) ---- *)

Lemma Val_fuel_up_S (k : nat) (FVT : HVT k) (FVP : HVP k) : FU (S k).
Proof.
  unfold FU. intros n Γ M T u a h Hu Ha V. dependent destruction h.
  - apply Val_Bot.
  - rewrite Val_tuniv. cbn [Rec.ValTy]. exact I.
  - rewrite Val_tuniv. cbn [Rec.ValTy]. exact I.
  - eapply (proj1 (@fuel_Val_tnat (S k) n Γ M T _ _ Hu)); exact V.
  - eapply (proj1 (@fuel_Val_tnat (S k) n Γ M T _ _ Hu)); exact V.
  - rewrite Val_tuniv in V |- *.
    refine (proj1 (FVT n Γ M _ _ _) V). cbn in Hu |- *; lia.
  - rewrite Val_abs in V |- *. destruct V as [VTy VPi]. split.
    + refine (proj1 (FVT n Γ T _ _ _) VTy). cbn in Ha |- *; lia.
    + refine (proj1 (FVP n Γ M T _ _ _ _ _ _) VPi); cbn in Hu, Ha |- *; lia.
Qed.

Lemma Val_fuel_down_S (k : nat) (FVT : HVT k) (FVP : HVP k) : FD (S k).
Proof.
  unfold FD. intros n Γ M T u a h Hu Ha V. dependent destruction h.
  - apply Val_Bot.
  - rewrite Val_tuniv. cbn [Rec.ValTy]. exact I.
  - rewrite Val_tuniv. cbn [Rec.ValTy]. exact I.
  - eapply (proj2 (@fuel_Val_tnat (S k) n Γ M T _ _ Hu)); exact V.
  - eapply (proj2 (@fuel_Val_tnat (S k) n Γ M T _ _ Hu)); exact V.
  - rewrite Val_tuniv in V |- *.
    refine (proj2 (FVT n Γ M _ _ _) V). cbn in Hu |- *; lia.
  - rewrite Val_abs in V |- *. destruct V as [VTy VPi]. split.
    + refine (proj2 (FVT n Γ T _ _ _) VTy). cbn in Ha |- *; lia.
    + refine (proj2 (FVP n Γ M T _ _ _ _ _ _) VPi); cbn in Hu, Ha |- *; lia.
Qed.

Lemma EqVal_fuel_up_S (k : nat) (FVT : HVT k) (FET : HET k) (FVP : HVP k) (FEP : HEP k) : FEU (S k).
Proof.
  unfold FEU. intros n Γ M N T u a h Hu Ha V. dependent destruction h.
  - apply EqVal_Bot.
  - rewrite EqVal_tuniv. cbn [Rec.ValTy Rec.EqValTy]. tauto.
  - rewrite EqVal_tuniv. cbn [Rec.ValTy Rec.EqValTy]. tauto.
  - eapply (proj1 (@fuel_EqVal_tnat (S k) n Γ M N T _ _ Hu)); exact V.
  - eapply (proj1 (@fuel_EqVal_tnat (S k) n Γ M N T _ _ Hu)); exact V.
  - rewrite EqVal_tuniv in V |- *. destruct V as [VTyM [VTyN VEqTy]].
    split; [ | split ].
    + refine (proj1 (FVT n Γ M _ _ _) VTyM). cbn in Hu |- *; lia.
    + refine (proj1 (FVT n Γ N _ _ _) VTyN). cbn in Hu |- *; lia.
    + refine (proj1 (FET n Γ M N _ _ _) VEqTy). cbn in Hu |- *; lia.
  - rewrite EqVal_abs in V |- *. destruct V as [VTy [VPiM [VPiN VEqPi]]].
    split; [ | split; [ | split ] ].
    + refine (proj1 (FVT n Γ T _ _ _) VTy). cbn in Ha |- *; lia.
    + refine (proj1 (FVP n Γ M T _ _ _ _ _ _) VPiM); cbn in Hu, Ha |- *; lia.
    + refine (proj1 (FVP n Γ N T _ _ _ _ _ _) VPiN); cbn in Hu, Ha |- *; lia.
    + refine (proj1 (FEP n Γ M N T _ _ _ _ _ _) VEqPi); cbn in Hu, Ha |- *; lia.
Qed.

Lemma EqVal_fuel_down_S (k : nat) (FVT : HVT k) (FET : HET k) (FVP : HVP k) (FEP : HEP k) : FED (S k).
Proof.
  unfold FED. intros n Γ M N T u a h Hu Ha V. dependent destruction h.
  - apply EqVal_Bot.
  - rewrite EqVal_tuniv. cbn [Rec.ValTy Rec.EqValTy]. tauto.
  - rewrite EqVal_tuniv. cbn [Rec.ValTy Rec.EqValTy]. tauto.
  - eapply (proj2 (@fuel_EqVal_tnat (S k) n Γ M N T _ _ Hu)); exact V.
  - eapply (proj2 (@fuel_EqVal_tnat (S k) n Γ M N T _ _ Hu)); exact V.
  - rewrite EqVal_tuniv in V |- *. destruct V as [VTyM [VTyN VEqTy]].
    split; [ | split ].
    + refine (proj2 (FVT n Γ M _ _ _) VTyM). cbn in Hu |- *; lia.
    + refine (proj2 (FVT n Γ N _ _ _) VTyN). cbn in Hu |- *; lia.
    + refine (proj2 (FET n Γ M N _ _ _) VEqTy). cbn in Hu |- *; lia.
  - rewrite EqVal_abs in V |- *. destruct V as [VTy [VPiM [VPiN VEqPi]]].
    split; [ | split; [ | split ] ].
    + refine (proj2 (FVT n Γ T _ _ _) VTy). cbn in Ha |- *; lia.
    + refine (proj2 (FVP n Γ M T _ _ _ _ _ _) VPiM); cbn in Hu, Ha |- *; lia.
    + refine (proj2 (FVP n Γ N T _ _ _ _ _ _) VPiN); cbn in Hu, Ha |- *; lia.
    + refine (proj2 (FEP n Γ M N T _ _ _ _ _ _) VEqPi); cbn in Hu, Ha |- *; lia.
Qed.

(** Fuel stability (the bundle [FuelStable k], proven by induction on [k]):
    above the ranks of the value/type codes, [Val]/[EqVal] do not depend on the
    fuel.  This is what licenses passing extra fuel freely and recovers the
    rank-relative behaviour of the Agda [Stage].  The eight directed projections
    ([Val_fuel_up]/[Val_fuel_down]/… below) are taken from it. *)
(* ---- the bundle, by induction on [k] ---- *)
Lemma fuel_stable : forall k, FuelStable k.
Proof.
  induction k as [|k IH].
  - unfold FuelStable.
    split; [ unfold FU; intros n Γ M T u a h H1 H2 V; exfalso; exact (Nat.nlt_0_r _ H1) | ].
    split; [ unfold FD; intros; exact I | ].
    split; [ unfold FEU; intros n Γ M N T u a h H1 H2 V; exfalso; exact (Nat.nlt_0_r _ H1) | ].
    split; [ unfold FED; intros; exact I | ].
    split; [ unfold HVT; intros n Γ M u h Hu;
             have E : u = bot := rk_bot_inv u Hu; subst u;
             split; intro V; cbn [Rec.ValTy] in V |- *; exact V | ].
    split; [ unfold HET; intros n Γ M N u h Hu;
             have E : u = bot := rk_bot_inv u Hu; subst u;
             split; intro V; cbn [Rec.EqValTy] in V |- *; exact V | ].
    split; [ unfold HVP; intros n Γ M A g b f h Hu1 Hu2; exfalso; cbn in Hu1; exact (Nat.nle_succ_0 _ Hu1) | ].
    unfold HEP; intros n Γ M N A g b f h Hu1 Hu2; exfalso; cbn in Hu1; exact (Nat.nle_succ_0 _ Hu1).
  - have [VU0 [VD0 [EU0 [ED0 [HVT0 [HET0 [HVP0 HEP0]]]]]]] := IH.
    have VU : FU (S k) := Val_fuel_up_S HVT0 HVP0.
    have VD : FD (S k) := Val_fuel_down_S HVT0 HVP0.
    have EU : FEU (S k) := EqVal_fuel_up_S HVT0 HET0 HVP0 HEP0.
    have ED : FED (S k) := EqVal_fuel_down_S HVT0 HET0 HVP0 HEP0.
    have FVT : HVT (S k) := fuel_ValTy_S VU VD EU ED.
    have FET : HET (S k) := fuel_EqValTy_S VU VD EU ED FVT.
    have FVP : HVP (S k) := fuel_ValPi_S VU VD EU ED.
    have FEP : HEP (S k) := fuel_EqValPi_S VU VD EU ED.
    exact (conj VU (conj VD (conj EU (conj ED (conj FVT (conj FET (conj FVP FEP))))))).
Qed.

(* ---- the canonical fuel lemmas (corollaries of the bundle) ---- *)
Definition Val_fuel_up    k : FU  k := proj1 (fuel_stable k).
Definition Val_fuel_down  k : FD  k := proj1 (proj2 (fuel_stable k)).
Definition EqVal_fuel_up  k : FEU k := proj1 (proj2 (proj2 (fuel_stable k))).
Definition EqVal_fuel_down k : FED k := proj1 (proj2 (proj2 (proj2 (fuel_stable k)))).
Definition fuel_ValTy   k : HVT k := proj1 (proj2 (proj2 (proj2 (proj2 (fuel_stable k))))).
Definition fuel_EqValTy k : HET k := proj1 (proj2 (proj2 (proj2 (proj2 (proj2 (fuel_stable k)))))).
Definition fuel_ValPi   k : HVP k := proj1 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (fuel_stable k))))))).
Definition fuel_EqValPi k : HEP k := proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (fuel_stable k))))))).


(* ============================================================ *)
(** * PER kernel *)
(* symmetry and transitivity for EqVal and EqValTy
   type conversion for Val and EqVal
   ============================================================ *)


(* The conversion-adequacy / PER kernel, bundled for one induction on [k].
   Mirrors Agda [FwdPack] ([Validity/Props.agda]): [EqValTy_sym] / [fwd] / [efwd]
   are mutually needed at each stage but the cycle is broken because each abs/tpi
   case at [S k] uses the *predecessor* facts at [k] (the domain has lower rank,
   so its edge data drops a fuel level).  Coq's global fuel reintroduces a
   rank-boundary off-by-one that Agda's rank-relative [Stage] avoids; we sidestep
   it by *sequencing* the step like [fuel_stable]: establish [fwd]/[EqValTy_sym]
   at [S k] first, then let the [EqVal]-PER [tpi] cases (whose content sits at
   the lower fuel [k]) bounce through the just-built [S k] facts via
   [fuel_EqValTy] up/down. *)
Definition FwdPER (k : nat) : Prop :=
  (forall n (Γ : Ctx n) (M A B : Tm n) u a (h : wt u a) (h' : wt a tuniv),
      rk u < k -> rk a < k ->
      Val k Γ M A h -> EqValTy k Γ A B h' -> Val k Γ M B h)
  /\ (forall n (Γ : Ctx n) (M N A B : Tm n) u a (h : wt u a) (h' : wt a tuniv),
      rk u < k -> rk a < k ->
      EqVal k Γ M N A h -> EqValTy k Γ A B h' -> EqVal k Γ M N B h)
  /\ (forall n (Γ : Ctx n) (M1 M2 A : Tm n) u a (h : wt u a),
      rk u < k ->
      EqVal k Γ M1 M2 A h -> EqVal k Γ M2 M1 A h)
  /\ (forall n (Γ : Ctx n) (M1 M2 M3 A : Tm n) u a (h : wt u a),
      rk u < k ->
      EqVal k Γ M1 M2 A h -> EqVal k Γ M2 M3 A h -> EqVal k Γ M1 M3 A h)
  /\ (forall n (Γ : Ctx n) (M N : Tm n) u (h : wt u tuniv),
      rk u < k ->
      EqValTy k Γ M N h -> EqValTy k Γ N M h)
  /\ (forall n (Γ : Ctx n) (A B C : Tm n) u (h : wt u tuniv),
      rk u < k ->
      EqValTy k Γ A B h -> EqValTy k Γ B C h -> EqValTy k Γ A C h).

(** The forward/PER kernel [FwdPER k], proven by one induction on [k].  It
    bundles, and so simultaneously establishes: type transport of [Val]/[EqVal]
    along [EqValTy] (forward), and symmetry and transitivity of [EqVal] and
    [EqValTy].  The exported PER lemmas ([EqVal_sym], [EqVal_trans],
    [EqValTy_sym], [EqValTy_trans], and the transport lemmas) are projections. *)
Lemma fwd_per_all : forall k, FwdPER k.
Proof.
  induction k as [|k IH].
  - (* fuel 0: every conjunct's [rk _ < 0] guard is absurd *)
    unfold FwdPER. repeat split; intros; lia.
  - move: IH => [IHfwd [IHEfwd [IHsym [IHtrans [IHTsym IHTtrans]]]]].
    (* ---- fwd (Val), established first: uses only the [k] IH ---- *)
    have FWD : forall n (Γ : Ctx n) (M A B : Tm n) u a (h : wt u a) (h' : wt a tuniv),
        rk u < S k -> rk a < S k ->
        Val (S k) Γ M A h -> EqValTy (S k) Γ A B h' -> Val (S k) Γ M B h.
    { intros n Γ M A B u a h. dependent destruction h; move=> h' Hu Ha HV HE.
      - apply Val_Bot.
      - exact HV.
      - exact HV.
      - exact HV.
      - exact HV.
      - exact HV.
      - (* abs: conversion-adequacy kernel (Agda [Vfwd FunEl PiCode]).
           Domain transport (IHfwd + [EtAe]), source value edge [PAV]/[PAE],
           then codomain [Bd->Be] retype at code [app g u']: [selectionBelow] the
           TYPE graph [g] at the value-key [u'] gives a [g]-selection whose
           value-join *is* [app g u'] ([selectionBelow]'s [app g x = v] clause),
           so the type edge [PEEty] (restricted argument) lands exactly there. *)
        rewrite Val_abs in HV. rewrite Val_abs.
        move: HV => [_ VPiMA].
        cbn [Rec.EqValTy] in HE.
        move: HE => [VTyAS [VTyBS [Ad [Bd [HRA [Ae [Be [Hk [cvA [cvB [vld [Edom PEEty]]]]]]]]]]]].
        move: VPiMA => [Ada [Bda [HRAa [PAV PAE]]]].
        have [eqAd eqBd] := HeadRed_tpi_det HRAa HRA. subst Ada Bda.
        have rkle2 := proj1 (Nat.lt_succ_r _ _) Ha.
        have EtAe : EqValTy k Γ Ae Ad (wt_tpi_dom h').
        { eapply IHTsym; [ cbn in Ha; lia | exact (EqVal_EqValTy Edom) ]. }
        have VFg : valid_fun g by eauto with valid.
        split.
        + eapply ValTy_irr. exact (proj2 (@fuel_ValTy k _ Γ B _ h' rkle2) VTyBS).
        + cbn [Rec.ValPi]. exists Ae, Be. split; [ exact Hk | split ].
          * cbn [Rec.PiAppVal]. move=> u' v' Sel WTu' P TyP VP.
            move: (rk_Selection_key Sel) (rk_Selection_val Sel) => Hk' Hkv.
            have Vu' : valid u' := wt_valid_tm WTu'.
            have VP0 : Val k Γ P Ad WTu'.
            { eapply IHfwd; [ cbn in Hu; lia | cbn in Ha; lia | exact VP | exact EtAe ]. }
            have TyP0 : typing Γ P Ad by (eapply t_conv; [ exact TyP | eapply c_sym; exact cvA ]).
            have Vres := PAV u' v' Sel WTu' P TyP0 VP0.
            have [uf [vf [Selg [Leuf Eqvf]]]] := selectionBelow VFg Vu'.
            have WTuf := wt_Selection (wt_tpi_dom h') VFg (wt_tpi_keys h') Selg.
            have VPuf : Val k Γ P Ad WTuf := restrictVal WTuf Leuf VP0.
            have VPufS : Val (S k) Γ P Ad WTuf.
            { apply Val_fuel_up;
                [ move: (rk_Selection_key Selg) => Hkf; cbn in Ha; lia
                | cbn in Ha; lia | exact VPuf ]. }
            subst vf.
            have Eedge := PEEty uf (app g u') Selg WTuf P TyP0 VPufS.
            eapply IHfwd;
              [ cbn in Hu; lia
              | move: (rk_app g u') => Hca; cbn in Ha; lia
              | exact Vres | exact (EqVal_EqValTy Eedge) ].
          * cbn [Rec.PiAppEq]. move=> u' v' Sel WTu' N1 N2 Cv EV.
            move: (rk_Selection_key Sel) (rk_Selection_val Sel) => Hk' Hkv.
            have Vu' : valid u' := wt_valid_tm WTu'.
            have EV0 : EqVal k Γ N1 N2 Ad WTu'.
            { eapply IHEfwd; [ cbn in Hu; lia | cbn in Ha; lia | exact EV | exact EtAe ]. }
            have Cv0 : conv Γ N1 N2 Ad by (eapply c_conv; [ exact Cv | eapply c_sym; exact cvA ]).
            have TyN1 : typing Γ N1 Ad := proj1 (conv_typing Cv0).
            have Eres := PAE u' v' Sel WTu' N1 N2 Cv0 EV0.
            have [uf [vf [Selg [Leuf Eqvf]]]] := selectionBelow VFg Vu'.
            have WTuf := wt_Selection (wt_tpi_dom h') VFg (wt_tpi_keys h') Selg.
            have Vn1uf : Val k Γ N1 Ad WTuf := restrictVal WTuf Leuf (EqVal_Val1 EV0).
            have Vn1ufS : Val (S k) Γ N1 Ad WTuf.
            { apply Val_fuel_up;
                [ move: (rk_Selection_key Selg) => Hkf; cbn in Ha; lia
                | cbn in Ha; lia | exact Vn1uf ]. }
            subst vf.
            have Eedge := PEEty uf (app g u') Selg WTuf N1 TyN1 Vn1ufS.
            eapply IHEfwd;
              [ cbn in Hu; lia
              | move: (rk_app g u') => Hca; cbn in Ha; lia
              | exact Eres | exact (EqVal_EqValTy Eedge) ]. }
    (* ---- efwd (EqVal), same shape ---- *)
    have EFWD : forall n (Γ : Ctx n) (M N A B : Tm n) u a (h : wt u a) (h' : wt a tuniv),
        rk u < S k -> rk a < S k ->
        EqVal (S k) Γ M N A h -> EqValTy (S k) Γ A B h' -> EqVal (S k) Γ M N B h.
    { intros n Γ M N A B u a h. dependent destruction h; move=> h' Hu Ha HV HE.
      - apply EqVal_Bot.
      - exact HV.
      - exact HV.
      - exact HV.
      - exact HV.
      - exact HV.
      - (* abs: reuse FWD for the two ValPi components; transport the
           PiAppEqVal edge (same [selectionBelow] codomain dance as FWD) *)
        rewrite EqVal_abs in HV. rewrite EqVal_abs.
        move: HV => [VTyA [VPiM [VPiN EqPiMN]]].
        have VMA : Val (S k) Γ M A (wt_abs w w0 i h) := conj VTyA VPiM.
        have VNA : Val (S k) Γ N A (wt_abs w w0 i h) := conj VTyA VPiN.
        have VMB := FWD _ Γ M A B _ _ (wt_abs w w0 i h) h' Hu Ha VMA HE.
        have VNB := FWD _ Γ N A B _ _ (wt_abs w w0 i h) h' Hu Ha VNA HE.
        move: VMB => [VTyB VPiMB]. move: VNB => [_ VPiNB].
        split; [ exact VTyB | split; [ exact VPiMB | split; [ exact VPiNB | ] ] ].
        cbn [Rec.EqValPi] in EqPiMN |- *.
        move: EqPiMN => [Ad [Bd [HRA PAEV]]].
        cbn [Rec.EqValTy] in HE.
        move: HE => [VTyAS [VTyBS [Ad2 [Bd2 [HRA2 [Ae [Be [Hk [cvA [cvB [vld [Edom PEEty]]]]]]]]]]]].
        have [eqAd eqBd] := HeadRed_tpi_det HRA HRA2. subst Ad2 Bd2.
        have EtAe : EqValTy k Γ Ae Ad (wt_tpi_dom h').
        { eapply IHTsym; [ cbn in Ha; lia | exact (EqVal_EqValTy Edom) ]. }
        have VFg : valid_fun g by eauto with valid.
        exists Ae, Be. split; [ exact Hk | ].
        cbn [Rec.PiAppEqVal]. move=> u' v' Sel WTu' P TyP VP.
        move: (rk_Selection_key Sel) (rk_Selection_val Sel) => Hk' Hkv.
        have Vu' : valid u' := wt_valid_tm WTu'.
        have VP0 : Val k Γ P Ad WTu'.
        { eapply IHfwd; [ cbn in Hu; lia | cbn in Ha; lia | exact VP | exact EtAe ]. }
        have TyP0 : typing Γ P Ad by (eapply t_conv; [ exact TyP | eapply c_sym; exact cvA ]).
        have Eres := PAEV u' v' Sel WTu' P TyP0 VP0.
        have [uf [vf [Selg [Leuf Eqvf]]]] := selectionBelow VFg Vu'.
        have WTuf := wt_Selection (wt_tpi_dom h') VFg (wt_tpi_keys h') Selg.
        have VPuf : Val k Γ P Ad WTuf := restrictVal WTuf Leuf VP0.
        have VPufS : Val (S k) Γ P Ad WTuf.
        { apply Val_fuel_up;
            [ move: (rk_Selection_key Selg) => Hkf; cbn in Ha; lia
            | cbn in Ha; lia | exact VPuf ]. }
        subst vf.
        have Eedge := PEEty uf (app g u') Selg WTuf P TyP0 VPufS.
        eapply IHEfwd;
          [ cbn in Hu; lia | move: (rk_app g u') => Hca; cbn in Ha; lia
          | exact Eres | exact (EqVal_EqValTy Eedge) ]. }
    (* ---- EqValTy_sym at [S k]: tpi case uses FWD (just built) + the [k] IH ---- *)
    have ETSYM : forall n (Γ : Ctx n) (M N : Tm n) u (h : wt u tuniv),
        rk u < S k -> EqValTy (S k) Γ M N h -> EqValTy (S k) Γ N M h.
    { intros n Γ M N u h. dependent destruction h; move=> Hu HE;
        try (cbn [Rec.EqValTy] in HE |- *; exact HE).
      (* tpi: conv-sym + ctx-conv + domain-flip + PiEdgeEqTy-sym (mirrors Agda
         [Esym PiCode], [Validity/Props.agda]) *)
      have flipU : forall (X Y : Tm n) v (hv : wt v tuniv),
          rk v < k -> EqVal (S k) Γ X Y Core.tuniv hv -> EqVal (S k) Γ Y X Core.tuniv hv.
      { move=> X Y v hv Hv E. rewrite EqVal_tuniv in E. rewrite EqVal_tuniv.
        move: E => [VX [VY Et]]. split; [ exact VY | split; [ exact VX | ] ].
        apply IHTsym; [ exact Hv | exact Et ]. }
      cbn [Rec.EqValTy] in HE |- *.
      move: HE => [VM [VN [A0 [B0 [HRM [A0' [B0' [HRN [cvA [cvB [vld [Edom PEEty]]]]]]]]]]]].
      cbn in Hu.
      have Hark : rk a < k by lia.
      have Edom' := flipU A0 A0' _ _ Hark Edom.
      have EtA'0 := EqVal_EqValTy Edom'.
      split; [ exact VN | split; [ exact VM | ] ].
      exists A0', B0'. split; [ exact HRN | ].
      exists A0, B0. split; [ exact HRM | ].
      split; [ eapply c_sym; exact cvA | ].
      split; [ eapply ctx_conv_conv; [ exact cvA | eapply c_sym; exact cvB ] | ].
      split; [ exact vld | ].
      split; [ exact Edom' | ].
      cbn [Rec.PiEdgeEqTy].
      move=> u' v' Sel WTu' P TyP VP.
      have Hu'rk : rk u' < k by (move: (rk_Selection_key Sel) => Hk; lia).
      have TyP0 : typing Γ P A0 by (eapply t_conv; [ exact TyP | eapply c_sym; exact cvA ]).
      have VP0 : Val (S k) Γ P A0 WTu'.
      { apply Val_fuel_up; [ exact Hu'rk | exact Hark | ].
        eapply IHfwd;
          [ exact Hu'rk | exact Hark
          | apply Val_fuel_down; [ exact Hu'rk | exact Hark | exact VP ]
          | exact EtA'0 ]. }
      have Eres := PEEty u' v' Sel WTu' P TyP0 VP0.
      eapply flipU; [ move: (rk_Selection_val Sel) => Hr; lia | exact Eres ]. }
    (* ---- EqValTy_trans at [S k] ---- *)
    have ETTRANS : forall n (Γ : Ctx n) (A B C : Tm n) u (h : wt u tuniv),
        rk u < S k -> EqValTy (S k) Γ A B h -> EqValTy (S k) Γ B C h -> EqValTy (S k) Γ A C h.
    { intros n Γ A B C u h. dependent destruction h; move=> Hu HAB HBC;
        try (cbn [Rec.EqValTy] in HAB, HBC |- *; exact HAB).
      (* tpi: conv-trans + ctx-conv + domain/codomain EqVal-trans (all edges over
         the type graph, so no value/type-graph mismatch) *)
      have transU : forall (X Y Z : Tm n) v (hv : wt v tuniv),
          rk v < k -> EqVal (S k) Γ X Y Core.tuniv hv -> EqVal (S k) Γ Y Z Core.tuniv hv ->
          EqVal (S k) Γ X Z Core.tuniv hv.
      { move=> X Y Z v hv Hv E1 E2. rewrite EqVal_tuniv in E1, E2. rewrite EqVal_tuniv.
        move: E1 => [VX [VY Et1]]. move: E2 => [_ [VZ Et2]].
        split; [ exact VX | split; [ exact VZ | ] ].
        eapply IHTtrans; [ exact Hv | exact Et1 | exact Et2 ]. }
      cbn [Rec.EqValTy] in HAB, HBC |- *.
      move: HAB => [VTyA [VTyB [A0 [B0 [HRA [A0m [B0m [Hk [cvAB [cvBB [vldAB [EdomAB PEEtyAB]]]]]]]]]]]].
      move: HBC => [_ [VTyC [A0n [B0n [Hkn [A0c [B0c [HRC [cvBC [cvCC [vldBC [EdomBC PEEtyBC]]]]]]]]]]]].
      have [eqA0m eqB0m] := HeadRed_tpi_det Hkn Hk. subst A0n B0n.
      cbn in Hu. have Hark : rk a < k by lia.
      have EtAm : EqValTy k Γ A0 A0m h := EqVal_EqValTy EdomAB.
      split; [ exact VTyA | split; [ exact VTyC | ] ].
      exists A0, B0. split; [ exact HRA | ].
      exists A0c, B0c. split; [ exact HRC | ].
      split; [ eapply c_trans; [ exact cvAB | exact cvBC ] | ].
      split; [ eapply c_trans; [ exact cvBB | eapply ctx_conv_conv; [ eapply c_sym; exact cvAB | exact cvCC ] ] | ].
      split; [ exact vldAB | ].
      split; [ eapply transU; [ exact Hark | exact EdomAB | exact EdomBC ] | ].
      cbn [Rec.PiEdgeEqTy].
      move=> u' v' Sel WTu' P TyP VP.
      have Hu'rk : rk u' < k by (move: (rk_Selection_key Sel) => Hk'; lia).
      have Vrk : rk v' < k by (move: (rk_Selection_val Sel) => Hk'; lia).
      have VPm : Val k Γ P A0m WTu'.
      { eapply IHfwd;
          [ exact Hu'rk | exact Hark
          | apply Val_fuel_down; [ exact Hu'rk | exact Hark | exact VP ]
          | exact EtAm ]. }
      have VPmS : Val (S k) Γ P A0m WTu' by (apply Val_fuel_up; [ exact Hu'rk | exact Hark | exact VPm ]).
      have TyPm : typing Γ P A0m by (eapply t_conv; [ exact TyP | exact cvAB ]).
      have EresAB := PEEtyAB u' v' Sel WTu' P TyP VP.
      have EresBC := PEEtyBC u' v' Sel WTu' P TyPm VPmS.
      eapply transU; [ exact Vrk | exact EresAB | exact EresBC ]. }
    (* ---- EqVal_sym (PER): tpi bounces its [k] content through ETSYM (S k) ---- *)
    have SYM : forall n (Γ : Ctx n) (M1 M2 A : Tm n) u a (h : wt u a),
        rk u < S k -> EqVal (S k) Γ M1 M2 A h -> EqVal (S k) Γ M2 M1 A h.
    { intros n Γ M1 M2 A u a h. dependent destruction h; move=> Hu HV.
      - apply EqVal_Bot.
      - rewrite EqVal_tuniv. move: HV => _. cbn [Rec.ValTy Rec.EqValTy]. tauto.
      - rewrite EqVal_tuniv. move: HV => _. cbn [Rec.ValTy Rec.EqValTy]. tauto.
      - rewrite EqVal_zero in HV. move: HV => [H1 H2]. rewrite EqVal_zero. by split.
      - rewrite EqVal_succ in HV. move: HV => [a1 [Ha1 [a2 [Ha2 HE]]]].
        rewrite EqVal_succ. exists a2. split; [ exact Ha2 | ].
        exists a1. split; [ exact Ha1 | eapply IHsym; [ cbn in Hu; lia | exact HE ] ].
      - (* tpi: bounce EqValTy [k] content up through ETSYM (S k) and back *)
        rewrite EqVal_tuniv in HV. rewrite EqVal_tuniv.
        move: HV => [VM1 [VM2 ET]].
        split; [ exact VM2 | split; [ exact VM1 | ] ].
        have rkle := proj1 (Nat.lt_succ_r _ _) Hu.
        apply (proj2 (@fuel_EqValTy k _ Γ M2 M1 _ (wt_tpi h w w0 i) rkle)).
        apply ETSYM; [ exact Hu | ].
        exact (proj1 (@fuel_EqValTy k _ Γ M1 M2 _ (wt_tpi h w w0 i) rkle) ET).
      - rewrite EqVal_abs in HV. rewrite EqVal_abs.
        move: HV => [VTd [VPiM1 [VPiM2 [A0 [B0 [HRT PAEV]]]]]].
        split; [ exact VTd | ]. split; [ exact VPiM2 | ]. split; [ exact VPiM1 | ].
        exists A0, B0. split; [ exact HRT | ].
        move=> uu vv Sel WT P TP VP.
        eapply IHsym;
          [ move: (rk_Selection_val Sel) => Hv; cbn in Hu; lia
          | exact (PAEV uu vv Sel WT P TP VP) ]. }
    (* ---- EqVal_trans (PER): tpi bounces through ETTRANS (S k) ---- *)
    have TRANS : forall n (Γ : Ctx n) (M1 M2 M3 A : Tm n) u a (h : wt u a),
        rk u < S k -> EqVal (S k) Γ M1 M2 A h -> EqVal (S k) Γ M2 M3 A h -> EqVal (S k) Γ M1 M3 A h.
    { intros n Γ M1 M2 M3 A u a h. dependent destruction h; move=> Hu HV HW.
      - apply EqVal_Bot.
      - rewrite EqVal_tuniv. move: HV HW => _ _. cbn [Rec.ValTy Rec.EqValTy]. tauto.
      - rewrite EqVal_tuniv. move: HV HW => _ _. cbn [Rec.ValTy Rec.EqValTy]. tauto.
      - rewrite EqVal_zero in HV HW. move: HV => [H1 _]. move: HW => [_ H3].
        rewrite EqVal_zero. by split.
      - rewrite EqVal_succ in HV HW. rewrite EqVal_succ.
        move: HV => [a1 [Ha1 [a2 [Ha2 HE12]]]].
        move: HW => [a2' [Ha2' [a3 [Ha3 HE23]]]].
        have E := HeadRed_succ_det Ha2 Ha2'. subst a2'.
        exists a1. split; [ exact Ha1 | ]. exists a3. split; [ exact Ha3 | ].
        eapply IHtrans; [ cbn in Hu; lia | exact HE12 | exact HE23 ].
      - (* tpi: bounce both EqValTy [k] components up through ETTRANS (S k) *)
        rewrite EqVal_tuniv in HV HW. rewrite EqVal_tuniv.
        move: HV => [VM1 [VM2 ET12]]. move: HW => [_ [VM3 ET23]].
        split; [ exact VM1 | split; [ exact VM3 | ] ].
        have rkle := proj1 (Nat.lt_succ_r _ _) Hu.
        apply (proj2 (@fuel_EqValTy k _ Γ M1 M3 _ (wt_tpi h w w0 i) rkle)).
        eapply ETTRANS;
          [ exact Hu
          | exact (proj1 (@fuel_EqValTy k _ Γ M1 M2 _ (wt_tpi h w w0 i) rkle) ET12)
          | exact (proj1 (@fuel_EqValTy k _ Γ M2 M3 _ (wt_tpi h w w0 i) rkle) ET23) ].
      - rewrite EqVal_abs in HV HW. rewrite EqVal_abs.
        move: HV => [VTd [VPiM1 [_ [A0 [B0 [HRT12 PAEV12]]]]]].
        move: HW => [_ [_ [VPiM3 [A0' [B0' [HRT23 PAEV23]]]]]].
        have [EA EB] := HeadRed_tpi_det HRT12 HRT23. subst A0' B0'.
        split; [ exact VTd | ]. split; [ exact VPiM1 | ]. split; [ exact VPiM3 | ].
        exists A0, B0. split; [ exact HRT12 | ].
        move=> uu vv Sel WT P TP VP.
        eapply IHtrans;
          [ move: (rk_Selection_val Sel) => Hv; cbn in Hu; lia
          | exact (PAEV12 uu vv Sel WT P TP VP) | exact (PAEV23 uu vv Sel WT P TP VP) ]. }
    unfold FwdPER. repeat split;
      [ exact FWD | exact EFWD | exact SYM | exact TRANS | exact ETSYM | exact ETTRANS ].
Qed.

(** ** Downstream-facing projections of [fwd_per_all]. *)

(** Type transport for [Val] (Agda: [Val2-EqValTy2-fwd]): a related term keeps
    its relation across a related (convertible) type. *)
Lemma Val_EqVal_fwd {n} (Γ : Ctx n) (M A : Tm n) u a
  (h : wt u a) (B : Tm n) (h' : wt a tuniv) k :
  rk u < k -> rk a < k ->
  Val k Γ M A h -> EqValTy k Γ A B h' -> Val k Γ M B h.
Proof. exact (proj1 (fwd_per_all k) n Γ M A B u a h h'). Qed.

(** Type transport for [EqVal] (Agda: [EqVal2-EqValTy2-fwd]). *)
Lemma EqVal_EqVal_fwd {n} (Γ : Ctx n) (M N A : Tm n) u a
  (h : wt u a) (B : Tm n) (h' : wt a tuniv) k :
  rk u < k -> rk a < k ->
  EqVal k Γ M N A h -> EqValTy k Γ A B h' -> EqVal k Γ M N B h.
Proof. exact (proj1 (proj2 (fwd_per_all k)) n Γ M N A B u a h h'). Qed.

(** Symmetry of [EqVal] (the PER's symmetry; Agda: [EqVal2-sym]). *)
Lemma EqVal_sym {n} (Γ : Ctx n) (M1 M2 A : Tm n) u a (h : wt u a) k :
  rk u < k ->
  EqVal k Γ M1 M2 A h -> EqVal k Γ M2 M1 A h.
Proof. exact (proj1 (proj2 (proj2 (fwd_per_all k))) n Γ M1 M2 A u a h). Qed.

(** Transitivity of [EqVal] (Agda: [EqVal2-trans]). *)
Lemma EqVal_trans {n} (Γ : Ctx n) (M1 M2 M3 A : Tm n) u a (h : wt u a) k :
  rk u < k ->
  EqVal k Γ M1 M2 A h -> EqVal k Γ M2 M3 A h -> EqVal k Γ M1 M3 A h.
Proof. exact (proj1 (proj2 (proj2 (proj2 (fwd_per_all k)))) n Γ M1 M2 M3 A u a h). Qed.

(** Symmetry of the type PER (Agda: [EqValTy2-sym]). *)
Lemma EqValTy_sym {n} (Γ : Ctx n) (M N : Tm n) u (h : wt u tuniv) k :
  rk u < k ->
  EqValTy k Γ M N h -> EqValTy k Γ N M h.
Proof. exact (proj1 (proj2 (proj2 (proj2 (proj2 (fwd_per_all k))))) n Γ M N u h). Qed.

(** Transitivity of the type PER (Agda: [EqValTy2-trans]). *)
Lemma EqValTy_trans {n} (Γ : Ctx n) (A B C : Tm n) u (h : wt u tuniv) k :
  rk u < k ->
  EqValTy k Γ A B h -> EqValTy k Γ B C h -> EqValTy k Γ A C h.
Proof. exact (proj2 (proj2 (proj2 (proj2 (proj2 (fwd_per_all k))))) n Γ A B C u h). Qed.


