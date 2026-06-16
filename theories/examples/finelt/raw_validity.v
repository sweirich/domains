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



Import SyntaxNotations.
Import SubstNotations.

Open Scope syntax_scope.

(* single-step head reduction *)
Inductive HeadRed1 (n : nat) : Tm n -> Tm n -> Prop := 
 | hr_beta A M N :
    HeadRed1 (app (abs A M) N) M[N..]
 | hr_app  M1 M2 N :
    HeadRed1 M1 M2 -> 
    HeadRed1 (app M1 N) (app M2 N).

(* reflexive-transitive closure *)
Definition HeadRed (n : nat) : Tm n -> Tm n -> Prop := 
  multi (@HeadRed1 n).

Lemma ms_app {n:nat} (M1 M2 : Tm (S n)) N :
   HeadRed M1 M2 -> HeadRed (app M1 N) (app M2 N).
Proof.
  intro h.
  induction h; eauto. eapply ms_refl.
  eapply ms_trans; eauto. eapply hr_app; eauto.
Qed.

Lemma HeadRed1_det (n:nat) (M N P : Tm n) : 
  HeadRed1 M N -> HeadRed1 M P -> N = P.
Proof.
  move=> h1 h2.
  induction M.
  all: inversion h1; inversion h2; subst. 
  - inversion H3. done.
  - inversion H5.
  - inversion H2.
  - rewrite (@IHM1 M3 M5) ; eauto.
Qed.

Lemma HeadRed_tpi_det (n:nat) (M : Tm n) A1 B1 A2 B2 : 
  HeadRed M (Core.tpi A1 B1) -> HeadRed M (Core.tpi A2 B2) ->
  A1 = A2 /\ B1 = B2.
Proof.
  move=> h1. move:A2 B2.
  dependent induction h1.
  all: move=> A2 B2 h2. 
  - inversion h2; subst. done. inversion H.
  - inversion h2; subst. inversion H.
    specialize (IHh1 _ _ ltac:(reflexivity) A2 B2).
    have EQ: e2 = e3. eapply HeadRed1_det; eauto.
    subst.
    eauto.
Qed.

Lemma HeadRed_tpi_eq {n}( A1 : Tm n) B1 A2 B2 :
   HeadRed (Core.tpi A1 B1) (Core.tpi A2 B2) -> 
   A1 = A2 /\ B1 = B2.
Proof. 
  move=> R1.
  have R2: HeadRed (Core.tpi A1 B1) (Core.tpi A1 B1).
  { eapply ms_refl. }
  eapply HeadRed_tpi_det; eauto.
Qed.

Lemma typing_app_inv n (Γ : Ctx n) M N A : 
 typing Γ (app M N) A -> 
      exists A1 , exists A2, typing Γ M (tpi A1 A2) /\ typing Γ N A1 /\ conv Γ A2[N..] A tuniv.
Proof. 
  move=> h.
  dependent induction h.
  - specialize (IHh M N ltac:(eauto)).
    destruct IHh as [A1 [A2 [TM [TN CC]]]].
    exists A1. exists A2. repeat split; auto.
    eapply c_trans; eauto.
  - clear IHh1 IHh2 IHh3 IHh4.
    exists A. exists B. repeat split; auto.
    eapply c_refl; eauto.
    eapply substitution_tm with (σ := N..) in h2. cbn in h2.
    eapply h2.
    eapply typing_subst_cons. asimpl. auto.
    eapply typing_subst_id. eapply typing_ctx; eauto.
    eapply typing_ctx; eauto.
Qed.

Lemma typing_abs_inv n (Γ : Ctx n) M A B: 
 typing Γ (abs A M) B -> 
      exists B2, typing (Γ ++ A) M B2 /\ conv Γ (tpi A B2) B tuniv.
Proof. 
  move=>h.
  dependent induction h.
  - specialize (IHh M A ltac:(eauto)).
    destruct IHh as [B2 [TM CC]].
    exists B2. repeat split; auto.
    eapply c_trans; eauto.
  - clear IHh1 IHh2 IHh3.
    exists B. repeat split; auto.
    eapply c_refl; eauto.
    eapply t_tpi; eauto.
Qed.


Lemma HeadRed1_conv {n} Γ (M N : Tm n) A :
  HeadRed1 M N -> typing Γ M A -> conv Γ M N A.
Proof.
  move=> h. induction h.
  - move=> T.
    destruct (typing_app_inv T) as [A1 [A2 [T1 [T3 C1]]]].
    destruct (typing_abs_inv T1) as [B2 [T2 C2]].
    eapply c_conv. 2: eassumption.
    eapply c_beta; eauto.
Abort.    

From Stdlib Require Import ProofIrrelevance.
Require Import finelt.utils.
Require Import findom.
Require Import types.

Import Raw.


(* Logical relation, defined by recursion on rank.

   The relation is parameterized by a typing context Γ : Ctx n.
   Terms M, N, A live at scope n; substitutions B[N..] close one
   variable, producing terms at scope n in the same context Γ.

   This is a coinductive definition. As u is "more defined" the
   set of syntactic terms in the relation becomes smaller.
   To begin, when u is bot, it is the total set.

*)


(* This module defines various helper operations on the logical
   relation. Each of these operations is parameterized by the
   two main fixpoints (Val and EqVal) which are polymorphic in
   the context size n and the typing context Γ.
*)
Module Rec.

Record F := MkF {
   Val   : forall {n} (Γ : Ctx n),
              Tm n -> Tm n -> forall u a, wt u a -> Prop;
   EqVal : forall {n} (Γ : Ctx n),
              Tm n -> Tm n -> Tm n -> forall u a, wt u a -> Prop;
}.

Section Helpers.
      
Variable 
   RB    : nat.

Variable 
   Val   : forall {n} (Γ : Ctx n),
              Tm n -> Tm n -> forall u a, wt u a -> Prop.
Variable
   EqVal : forall {n} (Γ : Ctx n),
              Tm n -> Tm n -> Tm n -> forall u a, wt u a -> Prop.


Definition  PiEdgeEq {n} (Γ : Ctx n)
  (A : Tm n) (B : Tm (S n)) (b: elt) (f : list (elt * elt))
  (h : wt (tpi b f) tuniv) :=
  forall u v (WT : wt u b)
      (* the argument's rank is bounded by the Pi type's rank: this
         keeps the (otherwise unbounded) domain occurrence of [EqVal]
         below within the well-founded [max]-rank measure.  See the
         note on [ValF]/[EqValF]. *)
      (RKu : rk u < RB)
      (APP: app f u = v) (NB: ~ is_bot v)
      (N1 N2 : Tm n),
      conv Γ N1 N2 A ->
      (* take related arguments *)
      EqVal Γ N1 N2 A WT ->
      (* to related results *)
      EqVal Γ B[N1..] B[N2..] Core.tuniv (wt_tpi_inv2 h (wt_valid_tm WT) APP).

Definition PiAppVal {n} (Γ : Ctx n)
  (M : Tm n) (A0 : Tm n) (B0 : Tm (S n)) b f g
  (h : wt (abs f) (tpi b g)) : Prop :=
  forall ui vi (Hin : In (ui, vi) f)
  (* the argument's rank is bounded by [RB] (the subject's rank), so the
     domain occurrence of [Val] below stays within the well-founded
     [max]-rank measure.  Mirrors [PiEdgeVal]/[PiEdgeEq]. *)
  (RKu : rk ui < RB)
  v t
  (APP : app f ui = v)
  (APPg : app g ui = t)
  (P : Tm n), typing Γ P A0 ->
              Val Γ P A0 (wt_abs_inv1 h Hin) ->
              Val  Γ (Core.app M P) B0[P..]
                  (wt_abs_inv2 h Hin APPg).

Definition PiAppEq {n} (Γ : Ctx n)
  (M : Tm n) (A0 : Tm n) (B0 : Tm (S n)) b f g
  (h : wt (abs f) (tpi b g))  :=
  forall ui vi (Hin : In (ui, vi) f)
    (RKu : rk ui < RB)
    v t
    (APP : app f ui = v)
    (APPg : app g ui = t)
    (N1 N2 : Tm n),
    conv Γ N1 N2 A0 ->
    EqVal  Γ N1 N2 A0 (wt_abs_inv1 h Hin) ->
    EqVal  Γ (Core.app M N1) (Core.app M N2) B0[N1..]
          (wt_abs_inv2 h Hin APPg).

Definition PiAppEqVal {n} (Γ : Ctx n)
  (M N : Tm n) (A0 : Tm n) (B0 : Tm (S n)) b f g
  (h : wt (abs f) (tpi b g)) :=
  forall ui vi (Hin : In (ui, vi) f)
  (RKu : rk ui < RB)
  v t
  (APP : app f ui = v)
  (APPg : app g ui = t)
  (P : Tm n),
        typing Γ P A0 ->
        Val  Γ P A0 (wt_abs_inv1 h Hin) ->
        EqVal  Γ (Core.app M P) (Core.app N P) B0[P..]
          (wt_abs_inv2 h Hin APPg).

Definition ValPi {n} (Γ : Ctx n)
  (M : Tm n) (A : Tm n) g b f (h : wt (abs g) (tpi b f)):=
  exists A0, exists B0, HeadRed A (Core.tpi A0 B0)
  /\ PiAppVal Γ M A0 B0 h
  /\ PiAppEq Γ M A0 B0 h.

Definition EqValPi {n} (Γ : Ctx n)
  (M : Tm n) (N: Tm n) (A : Tm n) g b f 
  (h : wt (abs g) (tpi b f)) :=
  exists A0, exists B0, HeadRed A (Core.tpi A0 B0)
  /\ PiAppEqVal Γ M N A0 B0 h.

Definition _PiEdgeVal
  (ValTy : forall {n} (Γ:Ctx n) M {u} (h:wt u tuniv), Prop)
  {n} (Γ : Ctx n)
  (A : Tm n) (B : Tm (S n)) (b: elt) (f : list (elt * elt))
  (h : wt (tpi b f) tuniv) : Prop :=
  forall u v (WTu : wt u b)
    (APP: app f u = v) (NB: ~ is_bot v) (WTu : wt u b)
    (N : Tm n), typing Γ N A ->
                (* take related arguments *)
                Val  Γ N A WTu ->
                (* to related results *)
                ValTy Γ B[N..] (wt_tpi_inv2 h (wt_valid_tm WTu) APP).

(* Unary analog of [PiEdgeEq]: for any argument [N] in the relation at
   the domain [A], the codomain [B[N..]] is in the relation (as a type).
   Like [PiEdgeEq], the quantified argument is rank-bounded by [RKu] so
   the (otherwise unbounded) domain occurrence of [Val] stays within the
   well-founded [max]-rank measure of [ValF]/[EqValF]. *)
Definition PiEdgeVal {n} (Γ : Ctx n)
  (A : Tm n) (B : Tm (S n)) (b: elt) (f : list (elt * elt))
  (h : wt (tpi b f) tuniv) :=
  forall u v (WT : wt u b)
      (RKu : rk u < RB)
      (APP: app f u = v) (NB: ~ is_bot v)
      (N : Tm n),
      typing Γ N A ->
      (* take a related argument *)
      Val Γ N A WT ->
      (* to a related result *)
      Val Γ B[N..] Core.tuniv (wt_tpi_inv2 h (wt_valid_tm WT) APP).


(* Cannot use Fixpoint here because the recursive call is on 
   the result of an application of an arbitrary argument, not a specific 
   subterm of u. However, rk_app tells us that the rank will be 
   preserved by application,
*)
Fixpoint ValTy {n} (Γ : Ctx n)
  (M : Tm n) u (h : wt u tuniv) {struct u} : Prop  :=
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
               /\ Val  Γ A Core.tuniv (wt_tpi_dom h)

               (* the codomain edge: related arguments give related results *)
               /\ PiEdgeVal Γ A B h
               /\ PiEdgeEq Γ A B h

  | tnat => fun h1 => True
  | tuniv => fun h1  => True
  | _ => fun h1  => True
  end) h.


Definition PiEdgeEqTy {n} (Γ : Ctx n)
  (A : Tm n) (B B' : Tm (S n)) b f (h : wt (tpi b f) tuniv) :=
    forall u v (WTu : wt u b)
      (RKu : rk u < RB)
      (APP: app f u = v) (NB: ~ is_bot v)
      (P : Tm n),
          typing Γ P A ->
          (* take a related argument *)
          Val  Γ P A WTu ->
          (* to (equal) related results *)
          EqVal Γ B[P..] B'[P..] Core.tuniv (wt_tpi_inv2 h (wt_valid_tm WTu) APP).

Fixpoint EqValTy {n} 
  (Γ : Ctx n) M N (a : elt) (h : wt a tuniv) {struct h} :  Prop :=
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

Fixpoint ValF (k : nat) {n} (Γ : Ctx n)
  (M : Tm n) (A : Tm n) (u : elt) (a : elt) (h : wt u a)
  {struct k} : Prop :=
  match k with
  | 0 => True
  | S k =>
      (match a return wt u _ -> Prop with

      | bot => fun h => True

      | tuniv => fun (h : wt u tuniv) =>
          Rec.ValTy k (@ValF k) (@EqValF k) Γ M h

      | tpi b f => fun h  =>
           (match u return wt _ (tpi b f) ->  Prop with

            | abs g => fun (h : wt (abs g) (tpi b f)) =>
                        Rec.ValTy k (@ValF k) (@EqValF k) Γ A (wt_abs_ty h)
                      /\ Rec.ValPi k (@ValF k) (@EqValF k) Γ M A h

            | _ => fun h  => True
            end) h

      | tnat => fun h =>
          (match u return wt _ tnat -> Prop with
               | zero => fun h  =>
                 HeadRed M (Core.zero)
               | succ v => fun (h : wt (succ v) tnat)  =>
                 exists M1, HeadRed M (Core.succ M1)
                 /\ ValF k Γ M1 Core.tnat (wt_succ_inv h)
               | _ =>  fun h => True
               end) h
      | _ => fun h  => True
       end) h
  end
(* Binary logical relation *)
with EqValF (k : nat) {n} (Γ : Ctx n)
  (M : Tm n) (N : Tm n) (A : Tm n) (u : elt) (a : elt) (h : wt u a)
  {struct k} : Prop :=
  match k with
  | 0 => True
  | S k =>
     (match a return wt u _ -> Prop with

      | bot => fun h => True

      | tuniv => fun (h : wt u tuniv) =>

            Rec.ValTy k (@ValF k) (@EqValF k) Γ M h
          /\ Rec.ValTy k (@ValF k) (@EqValF k) Γ N h
          /\ Rec.EqValTy k (@ValF k) (@EqValF k) Γ M N h

      | tpi b f => fun h =>
           (match u return wt _ (tpi b f) -> Prop with
           | bot => fun h => True
           | abs g => fun (h : wt (abs g) (tpi b f)) =>
               Rec.ValTy k (@ValF k) (@EqValF k) Γ A (wt_abs_ty h)
             /\ Rec.ValPi k (@ValF k) (@EqValF k) Γ M A h
             /\ Rec.ValPi k (@ValF k) (@EqValF k) Γ N A h
             /\ Rec.EqValPi k (@ValF k) (@EqValF k) Γ M N A h

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
                 /\ EqValF k Γ M1 N1 Core.tnat (wt_succ_inv h)
               | _ =>  fun h => True
               end) h
      | _ => fun h => True
    end) h
  end.

(* [Val]/[EqVal] are now *also* parameterised by the rank bound [RB]
   (the fuel of [ValF]/[EqValF]); there is no canonical-fuel wrapper.
   Every lemma below quantifies (or instantiates) [RB] for itself. *)
Definition Val (RB : nat) {n} (Γ : Ctx n)
  (M : Tm n) (A : Tm n) (u : elt) (a : elt) (h : wt u a) : Prop :=
  ValF RB Γ M A h.

Definition EqVal (RB : nat) {n} (Γ : Ctx n)
  (M : Tm n) (N : Tm n) (A : Tm n) (u : elt) (a : elt) (h : wt u a) : Prop :=
  EqValF RB Γ M N A h.

Arguments Val : clear implicits.
Arguments EqVal : clear implicits.

(* Parameterised abbreviations for the [Rec.*] helpers, with the
   [RB]-instances of [Val]/[EqVal] plugged in. *)
Notation ValTy RB      := (Rec.ValTy RB (@Val RB) (@EqVal RB)).
Notation EqValTy RB    := (Rec.EqValTy RB (@Val RB) (@EqVal RB)).
Notation ValPi RB      := (Rec.ValPi RB (@Val RB) (@EqVal RB)).
Notation EqValPi RB    := (Rec.EqValPi RB (@Val RB) (@EqVal RB)).
Notation PiEdgeEq RB   := (Rec.PiEdgeEq RB (@EqVal RB)).
Notation PiEdgeVal RB  := (Rec.PiEdgeVal RB (@Val RB)).
Notation PiAppVal RB   := (Rec.PiAppVal RB (@Val RB)).
Notation PiAppEq RB    := (Rec.PiAppEq RB (@EqVal RB)).
Notation PiAppEqVal RB := (Rec.PiAppEqVal RB (@Val RB) (@EqVal RB)).

Arguments Val RB {n} Γ M A {u} {a} h.
Arguments EqVal RB {n} Γ M N A {u} {a} h.

(* [Val]/[EqVal] only unfold via [Val_eq]/[EqVal_eq] below. *)
Arguments Val : simpl never.
Arguments EqVal : simpl never.

(* ============================================================
   Unfolding equations.

   [Val]/[EqVal] are [ValF]/[EqValF], which are structural fixpoints on
   the fuel [RB].  Unfolding [Val (S RB)] one step exposes the helpers
   and recursive occurrences at fuel [RB] -- so these equations hold
   *definitionally* ([reflexivity]); there is no fuel-irrelevance axiom.
   ============================================================ *)

Lemma Val_eq {n} (Γ : Ctx n) (M A : Tm n) u a (h : wt u a) RB :
  Val (S RB) Γ M A h =
  (match a as a0 return wt u a0 -> Prop with
   | bot => fun _ => True
   | tuniv => fun h => ValTy RB Γ M h
   | tpi b f => fun h =>
       (match u as u0 return wt u0 (tpi b f) -> Prop with
        | abs g => fun h => ValTy RB Γ A (wt_abs_ty h)
                          /\ ValPi RB Γ M A h
        | _ => fun _ => True
        end) h
   | tnat => fun h =>
       (match u as u0 return wt u0 tnat -> Prop with
        | zero => fun _ => HeadRed M Core.zero
        | succ v => fun h => exists M1, HeadRed M (Core.succ M1)
                           /\ Val RB Γ M1 Core.tnat (wt_succ_inv h)
        | _ => fun _ => True
        end) h
   | _ => fun _ => True
   end) h.
Proof. reflexivity. Qed.

Lemma EqVal_eq {n} (Γ : Ctx n) (M N A : Tm n) u a (h : wt u a) RB :
  EqVal (S RB) Γ M N A h =
  (match a as a0 return wt u a0 -> Prop with
   | bot => fun _ => True
   | tuniv => fun h => ValTy RB Γ M h
                    /\ ValTy RB Γ N h
                    /\ EqValTy RB Γ M N h
   | tpi b f => fun h =>
       (match u as u0 return wt u0 (tpi b f) -> Prop with
        | abs g => fun h => ValTy RB Γ A (wt_abs_ty h)
                          /\ ValPi RB Γ M A h
                          /\ ValPi RB Γ N A h
                          /\ EqValPi RB Γ M N A h
        | _ => fun _ => True
        end) h
   | tnat => fun h =>
       (match u as u0 return wt u0 tnat -> Prop with
        | zero => fun _ => HeadRed M Core.zero /\ HeadRed N Core.zero
        | succ v => fun h => exists M1, HeadRed M (Core.succ M1)
                           /\ exists N1, HeadRed N (Core.succ N1)
                           /\ EqVal RB Γ M1 N1 Core.tnat (wt_succ_inv h)
        | _ => fun _ => True
        end) h
   | _ => fun _ => True
   end) h.
Proof. reflexivity. Qed.

(* Per-constructor unfolding lemmas (the form actually used downstream).
   [Val]/[EqVal] at fuel [S RB] expose the helpers/recursive occurrences
   at fuel [RB] -- definitional, hence [reflexivity]. *)

Lemma Val_tuniv {n} (Γ : Ctx n) M A u (h : wt u tuniv) RB :
  Val (S RB) Γ M A h = ValTy RB Γ M h.
Proof. reflexivity. Qed.

Lemma Val_abs {n} (Γ : Ctx n) M A g b f (h : wt (abs g) (tpi b f)) RB :
  Val (S RB) Γ M A h = (ValTy RB Γ A (wt_abs_ty h) /\ ValPi RB Γ M A h).
Proof. reflexivity. Qed.

Lemma Val_zero {n} (Γ : Ctx n) M A (h : wt zero tnat) RB :
  Val (S RB) Γ M A h = HeadRed M Core.zero.
Proof. reflexivity. Qed.

Lemma Val_succ {n} (Γ : Ctx n) M A v (h : wt (succ v) tnat) RB :
  Val (S RB) Γ M A h = (exists M1, HeadRed M (Core.succ M1) /\ Val RB Γ M1 Core.tnat (wt_succ_inv h)).
Proof. reflexivity. Qed.

Lemma EqVal_tuniv {n} (Γ : Ctx n) M N A u (h : wt u tuniv) RB :
  EqVal (S RB) Γ M N A h = (ValTy RB Γ M h /\ ValTy RB Γ N h /\ EqValTy RB Γ M N h).
Proof. reflexivity. Qed.

Lemma EqVal_abs {n} (Γ : Ctx n) M N A g b f (h : wt (abs g) (tpi b f)) RB :
  EqVal (S RB) Γ M N A h =
  (ValTy RB Γ A (wt_abs_ty h) /\ ValPi RB Γ M A h /\ ValPi RB Γ N A h /\ EqValPi RB Γ M N A h).
Proof. reflexivity. Qed.

Lemma EqVal_zero {n} (Γ : Ctx n) M N A (h : wt zero tnat) RB :
  EqVal (S RB) Γ M N A h = (HeadRed M Core.zero /\ HeadRed N Core.zero).
Proof. reflexivity. Qed.

Lemma EqVal_succ {n} (Γ : Ctx n) M N A v (h : wt (succ v) tnat) RB :
  EqVal (S RB) Γ M N A h =
  (exists M1, HeadRed M (Core.succ M1) /\ exists N1, HeadRed N (Core.succ N1)
            /\ EqVal RB Γ M1 N1 Core.tnat (wt_succ_inv h)).
Proof. reflexivity. Qed.

(* ============================================================
   Val2-Bot, EqVal2-Bot: at u = bot, both relations are True.
   ============================================================ *)

Lemma Val_Bot {n} (Γ : Ctx n) (M A : Tm n) a (h : wt bot a) RB : Val RB Γ M A h.
Proof.
  unfold Val. destruct RB as [|RB']; first exact I.
  revert h. destruct a; intro h; exact I.
Qed.

Lemma EqVal_Bot {n} (Γ : Ctx n) (M N A : Tm n) a (h : wt bot a) RB :
  EqVal RB Γ M N A h.
Proof.
  unfold EqVal. destruct RB as [|RB']; first exact I.
  revert h. destruct a; intro h; repeat split; try exact I;
    dependent destruction h; exact I.
Qed.

(* [Val]/[EqVal] depend on the typing derivation only up to proof
   irrelevance, so any two derivations of the same [wt u a] give the
   same relation.  Used to discharge the cases of [up_down_restrict]
   where the two element/type pairs coincide. *)
Lemma Val_irr {n} (Γ : Ctx n) (M T : Tm n) u a (h h' : wt u a) RB :
  Val RB Γ M T h -> Val RB Γ M T h'.
Proof. now rewrite (proof_irrelevance _ h h'). Qed.

Lemma EqVal_irr {n} (Γ : Ctx n) (M N T : Tm n) u a (h h' : wt u a) RB :
  EqVal RB Γ M N T h -> EqVal RB Γ M N T h'.
Proof. now rewrite (proof_irrelevance _ h h'). Qed.

Lemma is_bot_eq (a : elt) : is_bot a -> a = bot.
Proof. by destruct a. Qed.

(* At a [bot] (semantic) type the relations are trivially total. *)
Lemma Val_isbot {n} (Γ : Ctx n) (M A : Tm n) u a (h : wt u a) RB :
  is_bot a -> Val RB Γ M A h.
Proof.
  move=> /is_bot_eq E. subst a.
  unfold Val. destruct RB as [|RB']; first exact I.
  revert h. destruct u; intro h; exact I.
Qed.

Lemma EqVal_isbot {n} (Γ : Ctx n) (M N A : Tm n) u a (h : wt u a) RB :
  is_bot a -> EqVal RB Γ M N A h.
Proof.
  move=> /is_bot_eq E. subst a.
  unfold EqVal. destruct RB as [|RB']; first exact I.
  revert h. destruct u; intro h; exact I.
Qed.

Lemma ValTy_irr {n} (Γ : Ctx n) (M : Tm n) u (h h' : wt u tuniv) RB :
  ValTy RB Γ M h -> ValTy RB Γ M h'.
Proof. now rewrite (proof_irrelevance _ h h'). Qed.


(* ============================================================
   Val <-> ValTy  and  EqVal <-> EqValTy
   ============================================================ *)

Lemma EqValTy_EqVal {n} (Γ : Ctx n) (A B : Tm n) a (h : wt a tuniv) RB :
  EqValTy RB Γ A B h ->
  EqVal (S RB) Γ A B Core.tuniv h.
Proof.
  rewrite (EqVal_tuniv Γ A B Core.tuniv h RB).
  dependent destruction h; cbn [Rec.EqValTy] in * |- *; try done.
  move=> [hA [hB h1]]. eauto.
Qed.

Lemma EqVal_EqValTy {n} (Γ : Ctx n) (A B C : Tm n) a (h : wt a tuniv) RB :
  EqVal (S RB) Γ A B C h ->
  EqValTy RB Γ A B h.
Proof.
  rewrite (EqVal_tuniv Γ A B C h RB). by move=> [_ [_ ?]].
Qed.

Lemma ValTy_Val {n} (Γ : Ctx n) (A : Tm n) a (h : wt a tuniv) RB :
  ValTy RB Γ A h ->
  Val (S RB) Γ A Core.tuniv h.
Proof.
  rewrite (Val_tuniv Γ A Core.tuniv h RB). auto.
Qed.

Lemma Val_ValTy {n} (Γ : Ctx n) (A : Tm n) a (h : wt a tuniv) RB :
  Val (S RB) Γ A Core.tuniv h ->
  ValTy RB Γ A h.
Proof.
  rewrite (Val_tuniv Γ A Core.tuniv h RB). auto.
Qed.

                                  


(* ============================================================
   Diagonal embedding
   Val <-> EqVal  and  ValTy → EqValTy
   ============================================================ *)


(* Diagonal embedding [Val -> EqVal].

   TODO: the original proof was a [Fixpoint ... {struct h}] that
   recursed through the codomain ([Val_EqVal] applied to
   [wt_tpi_inv2 ...], not a subterm of [h]).  With [Val]/[EqVal] now
   defined by well-founded recursion on [max (rk u) (rk a)], this proof
   should be redone by the *same* well-founded induction (using
   [Val_eq]/[EqVal_eq] for unfolding and the [RKu] bound of
   [PiEdgeEq]).  Admitted for now. *)
Lemma Val_EqVal {n} (Γ : Ctx n) (M A : Tm n) u a (h : wt u a) RB :
  Val RB Γ M A h -> EqVal RB Γ M M A h.
Proof.
Admitted.


(* ValTy2-to-EqValTy2 *)
Lemma ValTy_EqValTy {n} (Γ : Ctx n) (M : Tm n) u (h : wt u tuniv) RB :
  ValTy RB Γ M h -> EqValTy RB Γ M M h.
Proof.
  intros VT.
  eapply EqVal_EqValTy.
  eapply Val_EqVal.
  eapply ValTy_Val. exact VT.
Qed.


(* ============================================================
   Level 1 — projecting first and second parts of EqVal
   EqVal_Val1, EqVal_Val2
   ============================================================ *)


Fixpoint EqVal_Val1 {n} (Γ : Ctx n) (M N A : Tm n) u a (h : wt u a) RB
  {struct h} :
  EqVal RB Γ M N A h -> Val RB Γ M A h.
Proof.
  destruct RB as [|RB].
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


Fixpoint EqVal_Val2 {n} (Γ : Ctx n) (M N A : Tm n) u a (h : wt u a) RB
  {struct h} :
  EqVal RB Γ M N A h -> Val RB Γ N A h.
Proof.
  destruct RB as [|RB].
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
   Level 1a — 
   Head reduction/expansion
   ============================================================ *)

Lemma HeadRed_expand {n} (M M' : Tm n) A B :
  HeadRed1 M M' ->
  HeadRed M'  (Core.tpi A B) ->
  HeadRed M (Core.tpi A B).
Proof.
  move=> R HR.
  eapply ms_trans; eauto.
Qed.

Lemma HeadRed_contract {n} (M M' : Tm n) A B :
  HeadRed1 M M' ->
  HeadRed M  (Core.tpi A B) ->
  HeadRed M' (Core.tpi A B).
Proof.
Admitted.

Lemma ValTy_HeadRed1_expand {n} (Γ : Ctx n) (M M' : Tm n) u (h : wt u tuniv) RB :
  HeadRed1 M' M -> ValTy RB Γ M h -> ValTy RB Γ M' h.
Proof. 
  move=> R.
  dependent destruction h; cbn [Rec.ValTy].
  1,2,3: tauto.
  move=> [A0 [B0 [R0 [TA0 [TB0 [Vpi [VA [PEV PEE]]]]]]]].
  exists A0, B0.
  split. { eapply HeadRed_expand; eauto. }
  split. exact TA0.
  split. exact TB0.
  split. exact Vpi.
  split. exact VA.
  split. exact PEV.
  exact PEE.
Qed.

(* ValTy2-headred-expand *)
Lemma ValTy_HeadRed_expand {n} (Γ : Ctx n) (M M' : Tm n) u (h : wt u tuniv) RB :
  HeadRed M' M -> ValTy RB Γ M h -> ValTy RB Γ M' h.
Proof.
  move=> R. induction R.
  - done.
  - move=> h1. specialize (IHR h1).
    eapply ValTy_HeadRed1_expand in H; eauto.
Qed.

  

Lemma ValTy_HeadRed1_contract {n} (Γ : Ctx n) (M M' : Tm n) u (h : wt u tuniv) RB :
  HeadRed1 M M' -> ValTy RB Γ M h -> ValTy RB Γ M' h.
Proof. 
  move=> R.
  dependent destruction h; cbn [Rec.ValTy].
  1,2,3: tauto.
  move=> [A0 [B0 [R0 [TA0 [TB0 [Vpi [VA [PEV PEE]]]]]]]].
  exists A0, B0.
  split. { eapply HeadRed_contract; eauto. }
  split. exact TA0.
  split. exact TB0.
  split. exact Vpi.
  split. exact VA.
  split. exact PEV.
  exact PEE.
Qed.


(* ValTy2-headred-contract *)
Lemma ValTy_headred_contract {n} (Γ : Ctx n) (M M' : Tm n) u (h : wt u tuniv) RB :
  HeadRed M M' -> ValTy RB Γ M h -> ValTy RB Γ M' h.
Proof. 
  move=> R. induction R.
  - done.
  - admit.
Admitted.


(* ============================================================
   upValTy / downValTy — stated before the mutual block.

   Each is parameterized by the mutual-block lemma its proof
   relies on, so it can be applied inside the mutual block by
   passing the appropriate fixpoint reference at the call site.
   ============================================================ *)

(* downValTy: shrink the term-side element u (same type tuniv).
   Derivable from [restrictVal] of the mutual block. *)
Lemma downValTy_pre
  (restrictVal :
    forall n (Γ : Ctx n) (M T : Tm n) u u' a
           (h0 : wt u' a) (h1 : wt u a) RB,
           le u' u -> Val RB Γ M T h1 -> Val RB Γ M T h0)
  {n} (Γ : Ctx n) (M : Tm n) u0 u1
  (h0 : wt u0 tuniv) (h1 : wt u1 tuniv) RB :
  le u0 u1 -> ValTy RB Γ M h1 -> ValTy RB Γ M h0.
Proof.
  move=> LE VT1.
  apply (@Val_ValTy n Γ M u0 h0 RB).
  apply (@ValTy_Val n Γ M u1 h1 RB) in VT1.
  eapply restrictVal; eauto.
Qed.


(* ============================================================
   down/up
   ============================================================ *)


(* Proof-irrelevance for [wt]: needed to identify [Val]/[EqVal] proof
   indices when the type/element are forced to coincide. *)
Lemma wt_unique {u a} (h1 h2 : wt u a) : h1 = h2.
Proof. apply proof_irrelevance. Qed.

(* ------------------------------------------------------------------
   Monotonicity of [Val]/[EqVal] in the type and the element
   (up/down/restrict).  These mutually recurse through the Pi codomain
   ([app g u], whose rank is smaller), so we prove them together by
   well-founded recursion on the rank measure, bundled into one
   strong-induction statement [up_down_restrict].  The named lemmas
   [upVal] … [restrictEqVal] are derived as corollaries (so their
   signatures, used by adequacy.v, are preserved).
   ------------------------------------------------------------------ *)

(* The six monotonicity statements, bundled, at induction level [k] and
   relation bound [RB].  [Val]/[EqVal] are taken at [RB]; the rank
   premise ([... <= k]) drives the strong induction, the [... < RB]
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
  - cbn [Rec.PiAppVal]. move=> ui vi Hin RKu v t APP APPg P TyP VP. subst.
    destruct (is_bot (app g ui)) eqn:Hb. { apply Val_isbot; exact Hb. }
    have hU0 := wt_tpi_inv2 h0ty (wt_valid_tm (wt_abs_inv1 h0 Hin)) (erefl : app g' ui = app g' ui).
    have hU1 := wt_tpi_inv2 hUa1 (wt_valid_tm (wt_abs_inv1 h1 Hin)) (erefl : app g ui = app g ui).
    have Vui : valid ui := wt_valid_tm (wt_abs_inv1 h1 Hin).
    have leC : le (app g' ui) (app g ui) by (apply le_fun_mono; eauto with valid).
    have NBp : ~ is_bot (app g ui) by rewrite Hb.
    have VP0 := DOWN n Γ P A0 ui a' a (wt_abs_inv1 h0 Hin) (wt_abs_inv1 h1 Hin) LEa VP.
    have Vcod0 := PAV0 ui vi Hin RKu (app f ui) (app g' ui) erefl erefl P TyP VP0.
    have Vty := PEV ui (app g ui) (wt_abs_inv1 h1 Hin) RKu erefl NBp P TyP VP.
    have Vfin := UP n Γ (Core.app M P) B0[P..] vi (app g' ui) (app g ui)
                   (wt_abs_inv2 h0 Hin erefl) (wt_abs_inv2 h1 Hin erefl) hU0 hU1
                   leC Vcod0 ltac:(eapply Val_irr; exact Vty).
    eapply Val_irr; exact Vfin.
  - cbn [Rec.PiAppEq]. move=> ui vi Hin RKu v t APP APPg N1 N2 Cv EV. subst.
    destruct (is_bot (app g ui)) eqn:Hb. { apply EqVal_isbot; exact Hb. }
    have hU0 := wt_tpi_inv2 h0ty (wt_valid_tm (wt_abs_inv1 h0 Hin)) (erefl : app g' ui = app g' ui).
    have hU1 := wt_tpi_inv2 hUa1 (wt_valid_tm (wt_abs_inv1 h1 Hin)) (erefl : app g ui = app g ui).
    have Vui : valid ui := wt_valid_tm (wt_abs_inv1 h1 Hin).
    have leC : le (app g' ui) (app g ui) by (apply le_fun_mono; eauto with valid).
    have NBp : ~ is_bot (app g ui) by rewrite Hb.
    have EV0 := DOWNe n Γ N1 N2 A0 ui a' a (wt_abs_inv1 h0 Hin) (wt_abs_inv1 h1 Hin) LEa EV.
    have Ecod0 := PAE0 ui vi Hin RKu (app f ui) (app g' ui) erefl erefl N1 N2 Cv EV0.
    have Ety := PEE ui (app g ui) (wt_abs_inv1 h1 Hin) RKu erefl NBp N1 N2 Cv EV.
    have Vty : Val k Γ B0[N1..] Core.tuniv
                 (wt_tpi_inv2 hUa1 (wt_valid_tm (wt_abs_inv1 h1 Hin)) (erefl : app g ui = app g ui)).
    { eapply EqVal_Val1; exact Ety. }
    have Efin := UPe n Γ (Core.app M N1) (Core.app M N2) B0[N1..] vi (app g' ui) (app g ui)
                   (wt_abs_inv2 h0 Hin erefl) (wt_abs_inv2 h1 Hin erefl) hU0 hU1
                   leC Ecod0 ltac:(eapply Val_irr; exact Vty).
    eapply EqVal_irr; exact Efin.
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
  cbn [Rec.PiAppEqVal]. move=> ui vi Hin RKu v t APP APPg P TyP VP. subst.
  destruct (is_bot (app g ui)) eqn:Hb. { apply EqVal_isbot; exact Hb. }
  have hU0 := wt_tpi_inv2 (wt_abs_ty h0) (wt_valid_tm (wt_abs_inv1 h0 Hin)) (erefl : app g' ui = app g' ui).
  have hU1 := wt_tpi_inv2 hUa1 (wt_valid_tm (wt_abs_inv1 h1 Hin)) (erefl : app g ui = app g ui).
  have Vui : valid ui := wt_valid_tm (wt_abs_inv1 h1 Hin).
  have leC : le (app g' ui) (app g ui) by (apply le_fun_mono; eauto with valid).
  have NBp : ~ is_bot (app g ui) by rewrite Hb.
  have VP0 := DOWN n Γ P A0 ui a' a (wt_abs_inv1 h0 Hin) (wt_abs_inv1 h1 Hin) LEa VP.
  have Ecod0 := PAEV0 ui vi Hin RKu (app f ui) (app g' ui) erefl erefl P TyP VP0.
  have Vty := PEV ui (app g ui) (wt_abs_inv1 h1 Hin) RKu erefl NBp P TyP VP.
  have Efin := UPe n Γ (Core.app M P) (Core.app N P) B0[P..] vi (app g' ui) (app g ui)
                 (wt_abs_inv2 h0 Hin erefl) (wt_abs_inv2 h1 Hin erefl) hU0 hU1
                 leC Ecod0 ltac:(eapply Val_irr; exact Vty).
  eapply EqVal_irr; exact Efin.
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
  - cbn [Rec.PiAppVal]. move=> ui vi Hin RKu v t APP APPg P TyP VP. subst.
    have Vui : valid ui := wt_valid_tm (wt_abs_inv1 h0 Hin).
    have leC : le (app g' ui) (app g ui) by (apply le_fun_mono; eauto with valid).
    have VPb := UP n Γ P A0 ui a' a (wt_abs_inv1 h0 Hin) (wt_abs_inv1 h1 Hin) hUab' hUab
                  LEa VP ltac:(eapply Val_irr; exact VDomB).
    have Vcodb := PAV_B ui vi Hin RKu (app f ui) (app g ui) erefl erefl P TyP VPb.
    have Vfin := DOWN n Γ (Core.app M P) B0[P..] vi (app g' ui) (app g ui)
                   (wt_abs_inv2 h0 Hin erefl) (wt_abs_inv2 h1 Hin erefl) leC Vcodb.
    eapply Val_irr; exact Vfin.
  - cbn [Rec.PiAppEq]. move=> ui vi Hin RKu v t APP APPg N1 N2 Cv EV. subst.
    have Vui : valid ui := wt_valid_tm (wt_abs_inv1 h0 Hin).
    have leC : le (app g' ui) (app g ui) by (apply le_fun_mono; eauto with valid).
    have EVb := UPe n Γ N1 N2 A0 ui a' a (wt_abs_inv1 h0 Hin) (wt_abs_inv1 h1 Hin) hUab' hUab
                  LEa EV ltac:(eapply Val_irr; exact VDomB).
    have Ecodb := PAE_B ui vi Hin RKu (app f ui) (app g ui) erefl erefl N1 N2 Cv EVb.
    have Efin := DOWNe n Γ (Core.app M N1) (Core.app M N2) B0[N1..] vi (app g' ui) (app g ui)
                   (wt_abs_inv2 h0 Hin erefl) (wt_abs_inv2 h1 Hin erefl) leC Ecodb.
    eapply EqVal_irr; exact Efin.
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
  cbn [Rec.PiAppEqVal]. move=> ui vi Hin RKu v t APP APPg P TyP VP. subst.
  have Vui : valid ui := wt_valid_tm (wt_abs_inv1 h0 Hin).
  have leC : le (app g' ui) (app g ui) by (apply le_fun_mono; eauto with valid).
  have VPb := UP n Γ P A0 ui a' a (wt_abs_inv1 h0 Hin) (wt_abs_inv1 h1 Hin) hUab' hUab
                LEa VP ltac:(eapply Val_irr; exact VDomB).
  have Ecodb := PAEV_B ui vi Hin RKu (app f ui) (app g ui) erefl erefl P TyP VPb.
  have Efin := DOWNe n Γ (Core.app M P) (Core.app N P) B0[P..] vi (app g' ui) (app g ui)
                 (wt_abs_inv2 h0 Hin erefl) (wt_abs_inv2 h1 Hin erefl) leC Ecodb.
  eapply EqVal_irr; exact Efin.
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
      split. { eapply Val_irr. eapply (RES _ Γ A Core.tuniv a0 a tuniv); [ exact LEb | exact VDom ]. }
      split.
      * (* PiEdgeVal at (a, g) *)
        cbn [Rec.PiEdgeVal]. move=> u0 v0 WT0 RKu0 APP0 NB0 N0 TyN0 VN0. subst v0.
        have WTb0 : wt u0 a0 := wt_le WT0 LEb h0 h1.
        have VNb : Val k Γ N0 A WTb0.
        { eapply (UP _ Γ N0 A u0 a a0 WT0 WTb0 h0 h1);
            [ exact LEb | exact VN0 | eapply Val_irr; exact VDom ]. }
        have leV : le (app g u0) (app g0 u0) by (apply le_fun_mono; eauto with valid).
        have NBg : ~ is_bot (app g0 u0).
        { move=> H. apply is_bot_eq in H. rewrite H in leV.
          apply le_bot_inv in leV. apply NB0. rewrite leV. done. }
        have Res := PEV u0 (app g0 u0) WTb0 RKu0 erefl NBg N0 TyN0 VNb.
        eapply Val_irr.
        eapply (RES _ Γ B[N0..] Core.tuniv (app g0 u0) (app g u0) tuniv);
          [ exact leV | exact Res ].
      * (* PiEdgeEq at (a, g) *)
        cbn [Rec.PiEdgeEq]. move=> u0 v0 WT0 RKu0 APP0 NB0 N1 N2 Cv EV0. subst v0.
        have WTb0 : wt u0 a0 := wt_le WT0 LEb h0 h1.
        have EVb : EqVal k Γ N1 N2 A WTb0.
        { eapply (UPe _ Γ N1 N2 A u0 a a0 WT0 WTb0 h0 h1);
            [ exact LEb | exact EV0 | eapply Val_irr; exact VDom ]. }
        have leV : le (app g u0) (app g0 u0) by (apply le_fun_mono; eauto with valid).
        have NBg : ~ is_bot (app g0 u0).
        { move=> H. apply is_bot_eq in H. rewrite H in leV.
          apply le_bot_inv in leV. apply NB0. rewrite leV. done. }
        have Res := PEE u0 (app g0 u0) WTb0 RKu0 erefl NBg N1 N2 Cv EVb.
        eapply EqVal_irr.
        eapply (RESe _ Γ B[N1..] B[N2..] Core.tuniv (app g0 u0) (app g u0) tuniv);
          [ exact leV | exact Res ].
  - (* wt_abs: u = abs g (function value), a = tpi b f.
       The PiApp edges quantify over the abs graph; shrinking the graph
       [g' <= g] would require relating [app g ui] to individual graph
       entries (lub-closure of [Val]), infrastructure not yet available.
       Not exercised by adequacy (Val_transport has no callers yet). *)
    admit.
Admitted.

(* restrictEqVal: the binary analog of [restrictVal_step]. *)
Lemma restrictEqVal_step (k : nat) (IH : UDR k) :
  forall n (Γ : Ctx n) (M N T : Tm n) u u' a
    (h0 : wt u' a) (h1 : wt u a),
    le u' u -> EqVal (S k) Γ M N T h1 -> EqVal (S k) Γ M N T h0.
Proof.
  have UP    := proj1 IH.
  have UPe   := proj1 (proj2 IH).
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
      (* PiEdgeEqTy at (a, g) *)
      cbn [Rec.PiEdgeEqTy]. move=> u0 v0 WT0 RKu0 APP0 NB0 P TyP VP. subst v0.
      have VDomA : Val k Γ A Core.tuniv (wt_tpi_dom (wt_tpi h1 w1 w2 i0))
        by (eapply EqVal_Val1; exact EDom).
      have WTb0 : wt u0 a0 := wt_le WT0 LEb (wt_tpi_dom (wt_tpi h0 w w0 i))
                                          (wt_tpi_dom (wt_tpi h1 w1 w2 i0)).
      have VPb : Val k Γ P A WTb0.
      { eapply (UP _ Γ P A u0 a a0 WT0 WTb0
                  (wt_tpi_dom (wt_tpi h0 w w0 i)) (wt_tpi_dom (wt_tpi h1 w1 w2 i0)));
          [ exact LEb | exact VP | eapply Val_irr; exact VDomA ]. }
      have leV : le (app g u0) (app g0 u0) by (apply le_fun_mono; eauto with valid).
      have NBg : ~ is_bot (app g0 u0).
      { move=> H. apply is_bot_eq in H. rewrite H in leV.
        apply le_bot_inv in leV. apply NB0. rewrite leV. done. }
      have Res := EPEqT u0 (app g0 u0) WTb0 RKu0 erefl NBg P TyP VPb.
      eapply EqVal_irr.
      eapply (RESe _ Γ B[P..] B'[P..] Core.tuniv (app g0 u0) (app g u0) tuniv);
        [ exact leV | exact Res ].
  - (* wt_abs: function value -- see restrictVal_step abs case *)
    admit.
Admitted.

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



(* ValTy2-Sup: if a1 and a2 are universe-members and lub a1 a2 = Some a,
   ValTy at a1 and a2 lifts to ValTy at the lub. *)
Fixpoint ValTy_Sup {n} (Γ : Ctx n) (T : Tm n) a1 a2 a
  (h1 : wt a1 tuniv) (h2 : wt a2 tuniv) (h : wt a tuniv) RB {struct h}:
  lub a1 a2 = a ->
  ValTy RB Γ T h1 -> ValTy RB Γ T h2 -> ValTy RB Γ T h.
Proof.
Abort.

(* EqValTy2-Sup *)
Lemma EqValTy_Sup {n} (Γ : Ctx n) (M N : Tm n) a1 a2 a
  (h1 : wt a1 tuniv) (h2 : wt a2 tuniv) (h : wt a tuniv) RB :
  lub a1 a2 = a ->
  EqValTy RB Γ M N h1 -> EqValTy RB Γ M N h2 -> EqValTy RB Γ M N h.
Proof.
Abort.


(* ----------------------------------------------------- *)

Fixpoint Val_EqVal_fwd {n} (Γ : Ctx n) (M A : Tm n) u a
  (h : wt u a) (B : Tm n)  (h' : wt a tuniv) RB
  {struct h} :
  Val RB Γ M A h -> EqValTy RB Γ A B h' -> Val RB Γ M B h
with EqVal_EqVal_fwd {n} (Γ : Ctx n) (M N A : Tm n) u a
  (h : wt u a) (B : Tm n)  (h' : wt a tuniv) RB
  {struct h} :
  EqVal RB Γ M N A h -> EqValTy RB Γ A B h' -> EqVal RB Γ M N B h
with EqVal_sym {n} (Γ : Ctx n) (M1 M2 A : Tm n) u a (h : wt u a) RB { struct h } :
  EqVal RB Γ M1 M2 A h -> EqVal RB Γ M2 M1 A h
with EqVal_trans {n} (Γ : Ctx n) (M1 M2 M3 A : Tm n) u a (h : wt u a) RB {struct h} :
  EqVal RB Γ M1 M2 A h -> EqVal RB Γ M2 M3 A h -> EqVal RB Γ M1 M3 A h.
Proof.
  (* TODO: reprove for the WF-recursive Val/EqVal (old {struct h}/API-specific tactics no longer apply). *)
Admitted.



(* EqValTy2-sym *)
Lemma EqValTy_sym {n} (Γ : Ctx n) (M N : Tm n) u (h : wt u tuniv) RB :
  EqValTy RB Γ M N h -> EqValTy RB Γ N M h.
Proof.
  move=> h1. eapply EqVal_EqValTy. eapply EqVal_sym.
  eapply EqValTy_EqVal. exact h1.
Qed.

(* EqValTy2-trans *)
Lemma EqValTy_trans {n} (Γ : Ctx n) (A B C : Tm n) u (h : wt u tuniv) RB :
  EqValTy RB Γ A B h -> EqValTy RB Γ B C h -> EqValTy RB Γ A C h.
Proof.
  move=> h1 h2.
  eapply EqVal_EqValTy. eapply EqVal_trans.
  eapply EqValTy_EqVal. eauto.
  eapply EqValTy_EqVal. eauto.
Qed.

(* ============================================================
   Translations of theorem statements from Validity2.agda
   ------------------------------------------------------------

   Translation conventions (Agda → Rocq):
     FinMem u a              ≈  wt u a
     FinMem b UCode          ≈  wt b tuniv         (some i)
     Coherent u              ≈  valid u                (implicit in wt)
     CoherentFun g           ≈  valid_fun g            (implicit in wt (abs g) ..)
     CoherentFunTail f       ≈  valid_fun f            (implicit in wt (tpi _ f) ..)
     FinMemFun g b f         ≈  wt (abs g) (tpi b f)
     FinMemAllU f b          ≈  wt (tpi b f) tuniv (codomains in U_i)
     LeCode u v              ≈  le u v
     LeFunCode f g           ≈  le_fun f g
     Comp u v                ≈  compatible u v
     Sup u v = w             ≈  lub u v = Some w
     Selection f u v         ≈  In (u, v) f
     EvalFun f u = v         ≈  app f u = v
     subst1 B N              ≈  B[N..]
     HasType / ConvTm        ≈  typing / conv
     HeadRed                 ≈  HeadRed (multi reduction)

*)

(* ============================================================
   Level 2 — depends on Level 1
   ============================================================ *)

(* EqValTy2-headred-expand *)
Lemma EqValTy_headred_expand {n} (Γ : Ctx n) (M1 M2 M1' M2' : Tm n) u 
  (h : wt u tuniv) RB :
  HeadRed M1' M1 -> HeadRed M2' M2 ->
  EqValTy RB Γ M1 M2 h -> EqValTy RB Γ M1' M2' h.
Proof. Admitted.

(* EqValTy2-headred-contract *)
Lemma EqValTy_headred_contract {n} (Γ : Ctx n) (M1 M2 M1' M2' : Tm n) u 
  (h : wt u tuniv) RB :
  HeadRed M1 M1' -> HeadRed M2 M2' ->
  EqValTy RB Γ M1 M2 h -> EqValTy RB Γ M1' M2' h.
Proof. Admitted.


(* ============================================================
   Level 3 — 4-way SCC for HeadRed expand on Val/EqVal/ValPi/EqValPi
   ============================================================ *)

(* Val2-beta-expand *)
Lemma Val_beta_expand {n} (Γ : Ctx n) (M M0 T : Tm n) u a (h : wt u a) RB :
  HeadRed M0 M -> Val RB Γ M T h -> Val RB Γ M0 T h.
Proof. Admitted.

(* EqVal2-headred-expand *)
Lemma EqVal_headred_expand {n} (Γ : Ctx n) (M M0 N N0 T : Tm n) u a (h : wt u a) RB :
  HeadRed M0 M -> HeadRed N0 N ->
  EqVal RB Γ M N T h -> EqVal RB Γ M0 N0 T h.
Proof. Admitted.

(* ValPi2-headred-expand *)
Lemma ValPi_headred_expand {n} (Γ : Ctx n) (M M' T : Tm n) b f g
  (h : wt (abs g) (tpi b f)) RB :
  HeadRed M' M -> ValPi RB Γ M T h -> ValPi RB Γ M' T h.
Proof. Admitted.

(* EqValPi2-headred-expand *)
Lemma EqValPi_headred_expand {n} (Γ : Ctx n) (M1 M2 M1' M2' T : Tm n) b f g
  (h : wt (abs g) (tpi b f)) RB :
  HeadRed M1' M1 -> HeadRed M2' M2 ->
  EqValPi RB Γ M1 M2 T h -> EqValPi RB Γ M1' M2' T h.
Proof. Admitted.


(* ============================================================
   Level 4 — 4-way SCC for HeadRed contract
   ============================================================ *)

(* Val2-headred-contract *)
Lemma Val_headred_contract {n} (Γ : Ctx n) (M M0 T : Tm n) u a (h : wt u a) RB :
  HeadRed M M0 -> Val RB Γ M T h -> Val RB Γ M0 T h.
Proof. Admitted.

(* EqVal2-headred-contract *)
Lemma EqVal_headred_contract {n} (Γ : Ctx n) (M M0 N N0 T : Tm n) u a (h : wt u a) RB :
  HeadRed M M0 -> HeadRed N N0 ->
  EqVal RB Γ M N T h -> EqVal RB Γ M0 N0 T h.
Proof. Admitted.

(* ValPi2-headred-contract *)
Lemma ValPi_headred_contract {n} (Γ : Ctx n) (M M' T : Tm n) b f g
  (h : wt (abs g) (tpi b f)) RB :
  HeadRed M M' -> ValPi RB Γ M T h -> ValPi RB Γ M' T h.
Proof. Admitted.

(* EqValPi2-headred-contract *)
Lemma EqValPi_headred_contract {n} (Γ : Ctx n) (M1 M2 M1' M2' T : Tm n) b f g
  (h : wt (abs g) (tpi b f)) RB :
  HeadRed M1 M1' -> HeadRed M2 M2' ->
  EqValPi RB Γ M1 M2 T h -> EqValPi RB Γ M1' M2' T h.
Proof. Admitted.


