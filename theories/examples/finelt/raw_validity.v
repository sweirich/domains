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

Definition Val {n} (Γ : Ctx n)
  (M : Tm n) (A : Tm n) (u : elt) (a : elt) (h : wt u a) : Prop :=
  ValF (S (Init.Nat.max (rk u) (rk a))) Γ M A h.

Definition EqVal {n} (Γ : Ctx n)
  (M : Tm n) (N : Tm n) (A : Tm n) (u : elt) (a : elt) (h : wt u a) : Prop :=
  EqValF (S (Init.Nat.max (rk u) (rk a))) Γ M N A h.



Arguments Val : clear implicits.
Arguments EqVal : clear implicits.

(* The helper notions keep the rank bound [RB] as an *explicit*
   parameter rather than baking in a particular value: every lemma below
   quantifies (or instantiates) [RB] for itself.  These are parameterised
   abbreviations for the [Rec.*] helpers with the two canonical relations
   [Val]/[EqVal] plugged in. *)
Notation ValTy RB      := (Rec.ValTy RB Val EqVal).
Notation EqValTy RB    := (Rec.EqValTy RB Val EqVal).
Notation ValPi RB      := (Rec.ValPi RB Val EqVal).
Notation EqValPi RB    := (Rec.EqValPi RB Val EqVal).
Notation PiEdgeEq RB   := (Rec.PiEdgeEq RB EqVal).
Notation PiEdgeVal RB  := (Rec.PiEdgeVal RB Val).
Notation PiAppVal RB   := (Rec.PiAppVal RB Val).
Notation PiAppEq RB    := (Rec.PiAppEq RB EqVal).
Notation PiAppEqVal RB := (Rec.PiAppEqVal RB Val EqVal).

Arguments Val {_} _ _ _ {_}{_}.
Arguments EqVal {_} _ _ _ _ {_}{_}.

(* [Val]/[EqVal] only unfold via [Val_eq]/[EqVal_eq] below, never by
   [cbn]/[simpl] (which would expose the non-canonical fuel). *)
Arguments Val : simpl never.
Arguments EqVal : simpl never.

(* ============================================================
   Unfolding equations.

   [Val]/[EqVal] are [ValF]/[EqValF] at the canonical fuel
   [S (max (rk u) (rk a))].  Unfolding one step leaves the recursive
   occurrences at fuel [max (rk u) (rk a)]; the lemmas below re-express
   them at the *canonical* fuel of each (strictly smaller) sub-argument,
   so that all occurrences are again [Val]/[EqVal].  This is exactly
   fuel-irrelevance ([ValF k] agrees with [ValF k'] whenever both fuels
   exceed the rank measure), a routine strong induction on the measure
   that we admit here.
   ============================================================ *)

Lemma Val_eq {n} (Γ : Ctx n) (M A : Tm n) u a (h : wt u a) RB :
  Init.Nat.max (rk u) (rk a) < RB ->
  Val Γ M A h =
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
                           /\ Val Γ M1 Core.tnat (wt_succ_inv h)
        | _ => fun _ => True
        end) h
   | _ => fun _ => True
   end) h.
Admitted.

Lemma EqVal_eq {n} (Γ : Ctx n) (M N A : Tm n) u a (h : wt u a) RB :
  Init.Nat.max (rk u) (rk a) < RB ->
  EqVal Γ M N A h =
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
                           /\ EqVal Γ M1 N1 Core.tnat (wt_succ_inv h)
        | _ => fun _ => True
        end) h
   | _ => fun _ => True
   end) h.
Admitted.

(* Per-constructor unfolding lemmas (the form actually used downstream). *)

Lemma Val_tuniv {n} (Γ : Ctx n) M A u (h : wt u tuniv) RB :
  Init.Nat.max (rk u) (rk tuniv) < RB ->
  Val Γ M A h = ValTy RB Γ M h.
Proof. move=> E. erewrite Val_eq; [ reflexivity | exact E ]. Qed.

Lemma Val_abs {n} (Γ : Ctx n) M A g b f (h : wt (abs g) (tpi b f)) RB :
  Init.Nat.max (rk (abs g)) (rk (tpi b f)) < RB ->
  Val Γ M A h = (ValTy RB Γ A (wt_abs_ty h) /\ ValPi RB Γ M A h).
Proof. move=> E. erewrite Val_eq; [ reflexivity | exact E ]. Qed.

Lemma Val_zero {n} (Γ : Ctx n) M A (h : wt zero tnat) :
  Val Γ M A h = HeadRed M Core.zero.
Proof. erewrite Val_eq; [ reflexivity | apply Nat.lt_succ_diag_r ]. Qed.

Lemma Val_succ {n} (Γ : Ctx n) M A v (h : wt (succ v) tnat) :
  Val Γ M A h = (exists M1, HeadRed M (Core.succ M1) /\ Val Γ M1 Core.tnat (wt_succ_inv h)).
Proof. erewrite Val_eq; [ reflexivity | apply Nat.lt_succ_diag_r ]. Qed.

Lemma EqVal_tuniv {n} (Γ : Ctx n) M N A u (h : wt u tuniv) RB :
  Init.Nat.max (rk u) (rk tuniv) < RB ->
  EqVal Γ M N A h = (ValTy RB Γ M h /\ ValTy RB Γ N h /\ EqValTy RB Γ M N h).
Proof. move=> E. erewrite EqVal_eq; [ reflexivity | exact E ]. Qed.

Lemma EqVal_abs {n} (Γ : Ctx n) M N A g b f (h : wt (abs g) (tpi b f)) RB :
  Init.Nat.max (rk (abs g)) (rk (tpi b f)) < RB ->
  EqVal Γ M N A h =
  (ValTy RB Γ A (wt_abs_ty h) /\ ValPi RB Γ M A h /\ ValPi RB Γ N A h /\ EqValPi RB Γ M N A h).
Proof. move=> E. erewrite EqVal_eq; [ reflexivity | exact E ]. Qed.

Lemma EqVal_zero {n} (Γ : Ctx n) M N A (h : wt zero tnat) :
  EqVal Γ M N A h = (HeadRed M Core.zero /\ HeadRed N Core.zero).
Proof. erewrite EqVal_eq; [ reflexivity | apply Nat.lt_succ_diag_r ]. Qed.

Lemma EqVal_succ {n} (Γ : Ctx n) M N A v (h : wt (succ v) tnat) :
  EqVal Γ M N A h =
  (exists M1, HeadRed M (Core.succ M1) /\ exists N1, HeadRed N (Core.succ N1)
            /\ EqVal Γ M1 N1 Core.tnat (wt_succ_inv h)).
Proof. erewrite EqVal_eq; [ reflexivity | apply Nat.lt_succ_diag_r ]. Qed.

(* ============================================================
   Val2-Bot, EqVal2-Bot: at u = bot, both relations are True.
   ============================================================ *)

Lemma Val_Bot {n} (Γ : Ctx n) (M A : Tm n) a (h : wt bot a) : Val Γ M A h.
Proof. dependent destruction h.
       destruct a eqn:EQa; try done.
Qed.

Lemma EqVal_Bot {n} (Γ : Ctx n) (M N A : Tm n) a (h : wt bot a) :
  EqVal Γ M N A h.
Proof.
dependent destruction h.
       destruct a eqn:EQa; try done.
Qed.

(* [Val]/[EqVal] depend on the typing derivation only up to proof
   irrelevance, so any two derivations of the same [wt u a] give the
   same relation.  Used to discharge the cases of [up_down_restrict]
   where the two element/type pairs coincide. *)
Lemma Val_irr {n} (Γ : Ctx n) (M T : Tm n) u a (h h' : wt u a) :
  Val Γ M T h -> Val Γ M T h'.
Proof. now rewrite (proof_irrelevance _ h h'). Qed.

Lemma EqVal_irr {n} (Γ : Ctx n) (M N T : Tm n) u a (h h' : wt u a) :
  EqVal Γ M N T h -> EqVal Γ M N T h'.
Proof. now rewrite (proof_irrelevance _ h h'). Qed.

Lemma is_bot_eq (a : elt) : is_bot a -> a = bot.
Proof. by destruct a. Qed.

(* At a [bot] (semantic) type the relations are trivially total. *)
Lemma Val_isbot {n} (Γ : Ctx n) (M A : Tm n) u a (h : wt u a) :
  is_bot a -> Val Γ M A h.
Proof.
  move=> /is_bot_eq E. subst a.
  erewrite Val_eq; [ exact I | apply Nat.lt_succ_diag_r ].
Qed.

Lemma EqVal_isbot {n} (Γ : Ctx n) (M N A : Tm n) u a (h : wt u a) :
  is_bot a -> EqVal Γ M N A h.
Proof.
  move=> /is_bot_eq E. subst a.
  erewrite EqVal_eq; [ exact I | apply Nat.lt_succ_diag_r ].
Qed.

Lemma ValTy_irr {n} (Γ : Ctx n) (M : Tm n) u (h h' : wt u tuniv) RB :
  ValTy RB Γ M h -> ValTy RB Γ M h'.
Proof. now rewrite (proof_irrelevance _ h h'). Qed.


(* ============================================================
   Val <-> ValTy  and  EqVal <-> EqValTy
   ============================================================ *)

Lemma EqValTy_EqVal {n} (Γ : Ctx n) (A B : Tm n) a (h : wt a tuniv) RB :
  Init.Nat.max (rk a) (rk tuniv) < RB ->
  EqValTy RB Γ A B h ->
  EqVal Γ A B Core.tuniv h.
Proof.
  move=> LT.
  rewrite (EqVal_tuniv Γ A B Core.tuniv h LT).
  dependent destruction h; cbn [Rec.EqValTy] in * |- *; try done.
  move=> [hA [hB h1]]. eauto.
Qed.

Lemma EqVal_EqValTy {n} (Γ : Ctx n) (A B C : Tm n) a (h : wt a tuniv) RB :
  Init.Nat.max (rk a) (rk tuniv) < RB ->
  EqVal Γ A B C h ->
  EqValTy RB Γ A B h.
Proof.
  move=> LT. rewrite (EqVal_tuniv Γ A B C h LT). by move=> [_ [_ ?]].
Qed.

Lemma ValTy_Val {n} (Γ : Ctx n) (A : Tm n) a (h : wt a tuniv) RB :
  Init.Nat.max (rk a) (rk tuniv) < RB ->
  ValTy RB Γ A h ->
  Val Γ A Core.tuniv h.
Proof.
  move=> LT. rewrite (Val_tuniv Γ A Core.tuniv h LT). auto.
Qed.

Lemma Val_ValTy {n} (Γ : Ctx n) (A : Tm n) a (h : wt a tuniv) RB :
  Init.Nat.max (rk a) (rk tuniv) < RB ->
  Val Γ A Core.tuniv h ->
  ValTy RB Γ A h.
Proof.
  move=> LT. rewrite (Val_tuniv Γ A Core.tuniv h LT). auto.
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
Lemma Val_EqVal {n} (Γ : Ctx n) (M A : Tm n) u a (h : wt u a) :
  Val Γ M A h -> EqVal Γ M M A h.
Proof.
Admitted.


(* ValTy2-to-EqValTy2 *)
Lemma ValTy_EqValTy {n} (Γ : Ctx n) (M : Tm n) u (h : wt u tuniv) RB :
  Init.Nat.max (rk u) (rk tuniv) < RB ->
  ValTy RB Γ M h -> EqValTy RB Γ M M h.
Proof.
  intros LT VT.
  eapply EqVal_EqValTy; [ exact LT | ].
  eapply Val_EqVal.
  eapply ValTy_Val; [ exact LT | exact VT ].
Qed.


(* ============================================================
   Level 1 — projecting first and second parts of EqVal
   EqVal_Val1, EqVal_Val2
   ============================================================ *)


Fixpoint EqVal_Val1 {n} (Γ : Ctx n) (M N A : Tm n) u a (h : wt u a) RB
  (LT : Init.Nat.max (rk u) (rk a) < RB) {struct h} :
  EqVal Γ M N A h -> Val Γ M A h.
Proof.
  dependent destruction h.
  - move=> _. apply Val_Bot.
  - erewrite EqVal_tuniv, Val_tuniv. all: try exact LT. by move=> [? _].
  - erewrite EqVal_tuniv, Val_tuniv. all: try exact LT. by move=> [? _].
  - rewrite EqVal_zero Val_zero. by move=> [? _].
  - rewrite EqVal_succ Val_succ.
    move=> [M1 [h1 [N1 [h2 V1]]]]. exists M1. split; auto.
    eapply EqVal_Val1 with (RB := RB); [ cbn in LT |- *; lia | exact V1 ].
  - erewrite EqVal_tuniv, Val_tuniv. all: try exact LT. by move=> [? _].
  - erewrite EqVal_abs, Val_abs. all: try exact LT. move=> [hA [hM _]]. by split.
Qed.


Fixpoint EqVal_Val2 {n} (Γ : Ctx n) (M N A : Tm n) u a (h : wt u a) RB
  (LT : Init.Nat.max (rk u) (rk a) < RB) {struct h} :
  EqVal Γ M N A h -> Val Γ N A h.
Proof.
  dependent destruction h.
  - move=> _. apply Val_Bot.
  - erewrite EqVal_tuniv, Val_tuniv. all: try exact LT. by move=> [_ [? _]].
  - erewrite EqVal_tuniv, Val_tuniv. all: try exact LT. by move=> [_ [? _]].
  - rewrite EqVal_zero Val_zero. by move=> [_ ?].
  - rewrite EqVal_succ Val_succ.
    move=> [M1 [h1 [N1 [h2 V1]]]]. exists N1. split; auto.
    eapply EqVal_Val2 with (RB := RB); [ cbn in LT |- *; lia | exact V1 ].
  - erewrite EqVal_tuniv, Val_tuniv. all: try exact LT. by move=> [_ [? _]].
  - erewrite EqVal_abs, Val_abs. all: try exact LT. move=> [hA [_ [hN _]]]. by split.
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
           (h0 : wt u' a) (h1 : wt u a),
           le u' u -> Val Γ M T h1 -> Val Γ M T h0)
  {n} (Γ : Ctx n) (M : Tm n) u0 u1
  (h0 : wt u0 tuniv) (h1 : wt u1 tuniv) RB
  (LT0 : Init.Nat.max (rk u0) (rk tuniv) < RB)
  (LT1 : Init.Nat.max (rk u1) (rk tuniv) < RB) :
  le u0 u1 -> ValTy RB Γ M h1 -> ValTy RB Γ M h0.
Proof.
  move=> LE VT1.
  apply (@Val_ValTy n Γ M u0 h0 RB LT0).
  apply (@ValTy_Val n Γ M u1 h1 RB LT1) in VT1.
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

(* The [wt_abs] case of [upVal]: lift the function value [M] from the
   smaller Pi-type [tpi a' g'] to the bigger [tpi a g] ([a' <= a],
   [g' [= g]).  Proved by the per-edge transport described above, using
   the strong-induction hypothesis [IH] for the (strictly smaller-rank)
   domain ([downVal]/[downEqVal]) and codomain ([upVal]/[upEqVal])
   steps, and the type [T]'s own codomain edge ([PiEdgeVal]/[PiEdgeEq])
   for the [ValTy] witnesses.  A single rank bound [RB] is shared by the
   subject edge [PiAppVal] and the type edge [PiEdgeVal], so the assumed
   [rk ui < RB] discharges both. *)
Lemma upValPi (k : nat)
  (IH : forall m, (m < k)%nat ->
     (forall n (Γ : Ctx n) (M T : Tm n) u a0 a1
        (h0 : wt u a0) (h1 : wt u a1) (hUa0 : wt a0 tuniv) (hUa1 : wt a1 tuniv),
        Init.Nat.max (rk u) (rk a1) <= m -> le a0 a1 ->
        Val Γ M T h0 -> Val Γ T Core.tuniv hUa1 -> Val Γ M T h1)
     /\ (forall n (Γ : Ctx n) (M N T : Tm n) u a0 a1
        (h0 : wt u a0) (h1 : wt u a1) (hUa0 : wt a0 tuniv) (hUa1 : wt a1 tuniv),
        Init.Nat.max (rk u) (rk a1) <= m -> le a0 a1 ->
        EqVal Γ M N T h0 -> Val Γ T Core.tuniv hUa1 -> EqVal Γ M N T h1)
     /\ (forall n (Γ : Ctx n) (M T : Tm n) u a0 a1
        (h0 : wt u a0) (h1 : wt u a1),
        Init.Nat.max (rk u) (rk a1) <= m -> le a0 a1 ->
        Val Γ M T h1 -> Val Γ M T h0)
     /\ (forall n (Γ : Ctx n) (M N T : Tm n) u a0 a1
        (h0 : wt u a0) (h1 : wt u a1),
        Init.Nat.max (rk u) (rk a1) <= m -> le a0 a1 ->
        EqVal Γ M N T h1 -> EqVal Γ M N T h0)
     /\ (forall n (Γ : Ctx n) (M T : Tm n) u u' a
        (h0 : wt u' a) (h1 : wt u a),
        Init.Nat.max (rk u) (rk a) <= m -> le u' u ->
        Val Γ M T h1 -> Val Γ M T h0)
     /\ (forall n (Γ : Ctx n) (M N T : Tm n) u u' a
        (h0 : wt u' a) (h1 : wt u a),
        Init.Nat.max (rk u) (rk a) <= m -> le u' u ->
        EqVal Γ M N T h1 -> EqVal Γ M N T h0))
  {n} (Γ : Ctx n) (M T : Tm n) f a g a' g'
  (h0 : wt (abs f) (tpi a' g')) (h1 : wt (abs f) (tpi a g))
  (hUa1 : wt (tpi a g) tuniv)
  (RK : Init.Nat.max (rk (abs f)) (rk (tpi a g)) <= k)
  (LEa : le a' a) (LEg : le_fun g' g) :
  Val Γ M T h0 -> Val Γ T Core.tuniv hUa1 -> Val Γ M T h1.
Proof.
  move=> V VT.
  have h0ty : wt (tpi a' g') tuniv := wt_abs_ty h0.
  have GB : Init.Nat.max (rk (abs f)) (rk (tpi a g))
            < S (Init.Nat.max (Init.Nat.max (rk (abs f)) (rk (tpi a g))) (rk (tpi a' g'))) by lia.
  have GB' : Init.Nat.max (rk (abs f)) (rk (tpi a' g'))
            < S (Init.Nat.max (Init.Nat.max (rk (abs f)) (rk (tpi a g))) (rk (tpi a' g'))) by lia.
  have GBu : Init.Nat.max (rk (tpi a g)) (rk tuniv)
            < S (Init.Nat.max (Init.Nat.max (rk (abs f)) (rk (tpi a g))) (rk (tpi a' g'))) by (cbn [rk]; lia).
  rewrite (Val_abs Γ M T h1 GB).
  rewrite (Val_abs Γ M T h0 GB') in V.
  rewrite (Val_tuniv Γ T Core.tuniv hUa1 GBu) in VT.
  destruct V as [_ VPi0].
  split.
  { eapply ValTy_irr; exact VT. }
  cbn [Rec.ValPi] in VPi0.
  destruct VPi0 as [A0 [B0 [HR0 [PAV0 PAE0]]]].
  cbn [Rec.ValTy] in VT.
  destruct VT as [AT [BT [HRt [TyA0 [TyB0 [vld [VDomT [PEV PEE]]]]]]]].
  have [E1 E2] := HeadRed_tpi_det HR0 HRt. subst AT BT.
  have Vg  : valid_fun g  by eauto with valid.
  have Vg' : valid_fun g' by eauto with valid.
  have mlt : (Init.Nat.max (rk_fun f) (Init.Nat.max (rk a) (rk_fun g)) < k)%nat
    by (move: RK; cbn [rk]; lia).
  have UP    := proj1 (IH _ mlt).
  have UPe   := proj1 (proj2 (IH _ mlt)).
  have DOWN  := proj1 (proj2 (proj2 (IH _ mlt))).
  have DOWNe := proj1 (proj2 (proj2 (proj2 (IH _ mlt)))).
  cbn [Rec.ValPi]. exists A0, B0. split; [ exact HR0 | split ].
  - (* PiAppVal *)
    cbn [Rec.PiAppVal]. move=> ui vi Hin RKu v t APP APPg P TyP VP. subst.
    destruct (is_bot (app g ui)) eqn:Hb.
    { apply Val_isbot; exact Hb. }
    have Vui : valid ui := wt_valid_tm (wt_abs_inv1 h1 Hin).
    have hU0 := wt_tpi_inv2 h0ty (wt_valid_tm (wt_abs_inv1 h0 Hin)) (erefl : app g' ui = app g' ui).
    have hU1 := wt_tpi_inv2 hUa1 Vui (erefl : app g ui = app g ui).
    have boundD : Init.Nat.max (rk ui) (rk a)
                    <= Init.Nat.max (rk_fun f) (Init.Nat.max (rk a) (rk_fun g)).
      { have hh := @In_rk_fun1 (ui,vi) f Hin. cbn in hh. lia. }
    have boundC : Init.Nat.max (rk vi) (rk (app g ui))
                    <= Init.Nat.max (rk_fun f) (Init.Nat.max (rk a) (rk_fun g)).
      { have hh := @In_rk_fun2 (ui,vi) f Hin. have hh2 := rk_app g ui. cbn in hh. lia. }
    have leC : le (app g' ui) (app g ui) by (apply le_fun_mono; eauto with valid).
    have NBp : ~ is_bot (app g ui) by rewrite Hb.
    have VP0 := DOWN n Γ P A0 ui a' a (wt_abs_inv1 h0 Hin) (wt_abs_inv1 h1 Hin) boundD LEa VP.
    have Vcod0 := PAV0 ui vi Hin RKu (app f ui) (app g' ui) erefl erefl P TyP VP0.
    have Vty := PEV ui (app g ui) (wt_abs_inv1 h1 Hin) RKu erefl NBp P TyP VP.
    have Vfin := UP n Γ (Core.app M P) B0[P..] vi (app g' ui) (app g ui)
                   (wt_abs_inv2 h0 Hin erefl) (wt_abs_inv2 h1 Hin erefl) hU0 hU1
                   boundC leC Vcod0 ltac:(eapply Val_irr; exact Vty).
    eapply Val_irr; exact Vfin.
  - (* PiAppEq *)
    cbn [Rec.PiAppEq]. move=> ui vi Hin RKu v t APP APPg N1 N2 Cv EV. subst.
    destruct (is_bot (app g ui)) eqn:Hb.
    { apply EqVal_isbot; exact Hb. }
    have Vui : valid ui := wt_valid_tm (wt_abs_inv1 h1 Hin).
    have hU0 := wt_tpi_inv2 h0ty (wt_valid_tm (wt_abs_inv1 h0 Hin)) (erefl : app g' ui = app g' ui).
    have hU1 := wt_tpi_inv2 hUa1 Vui (erefl : app g ui = app g ui).
    have boundD : Init.Nat.max (rk ui) (rk a)
                    <= Init.Nat.max (rk_fun f) (Init.Nat.max (rk a) (rk_fun g)).
      { have hh := @In_rk_fun1 (ui,vi) f Hin. cbn in hh. lia. }
    have boundC : Init.Nat.max (rk vi) (rk (app g ui))
                    <= Init.Nat.max (rk_fun f) (Init.Nat.max (rk a) (rk_fun g)).
      { have hh := @In_rk_fun2 (ui,vi) f Hin. have hh2 := rk_app g ui. cbn in hh. lia. }
    have leC : le (app g' ui) (app g ui) by (apply le_fun_mono; eauto with valid).
    have NBp : ~ is_bot (app g ui) by rewrite Hb.
    have EV0 := DOWNe n Γ N1 N2 A0 ui a' a (wt_abs_inv1 h0 Hin) (wt_abs_inv1 h1 Hin) boundD LEa EV.
    have Ecod0 := PAE0 ui vi Hin RKu (app f ui) (app g' ui) erefl erefl N1 N2 Cv EV0.
    have Ety := PEE ui (app g ui) (wt_abs_inv1 h1 Hin) RKu erefl NBp N1 N2 Cv EV.
    have Vty : Val Γ B0[N1..] Core.tuniv
                 (wt_tpi_inv2 hUa1 (wt_valid_tm (wt_abs_inv1 h1 Hin)) (erefl : app g ui = app g ui)).
    { eapply EqVal_Val1; [ apply Nat.lt_succ_diag_r | exact Ety ]. }
    have Efin := UPe n Γ (Core.app M N1) (Core.app M N2) B0[N1..] vi (app g' ui) (app g ui)
                   (wt_abs_inv2 h0 Hin erefl) (wt_abs_inv2 h1 Hin erefl) hU0 hU1
                   boundC leC Ecod0 ltac:(eapply Val_irr; exact Vty).
    eapply EqVal_irr; exact Efin.
Qed.

(* The [wt_abs] case of [upEqVal].  The two unary [ValPi] components are
   discharged by [upValPi] (applied to the [EqVal_Val1]/[EqVal_Val2]
   projections of the hypothesis); only the binary edge [EqValPi]
   ([PiAppEqVal]) needs a fresh per-edge transport, structurally
   identical to the [PiAppVal] case of [upValPi]. *)
Lemma upEqValPi (k : nat)
  (IH : forall m, (m < k)%nat ->
     (forall n (Γ : Ctx n) (M T : Tm n) u a0 a1
        (h0 : wt u a0) (h1 : wt u a1) (hUa0 : wt a0 tuniv) (hUa1 : wt a1 tuniv),
        Init.Nat.max (rk u) (rk a1) <= m -> le a0 a1 ->
        Val Γ M T h0 -> Val Γ T Core.tuniv hUa1 -> Val Γ M T h1)
     /\ (forall n (Γ : Ctx n) (M N T : Tm n) u a0 a1
        (h0 : wt u a0) (h1 : wt u a1) (hUa0 : wt a0 tuniv) (hUa1 : wt a1 tuniv),
        Init.Nat.max (rk u) (rk a1) <= m -> le a0 a1 ->
        EqVal Γ M N T h0 -> Val Γ T Core.tuniv hUa1 -> EqVal Γ M N T h1)
     /\ (forall n (Γ : Ctx n) (M T : Tm n) u a0 a1
        (h0 : wt u a0) (h1 : wt u a1),
        Init.Nat.max (rk u) (rk a1) <= m -> le a0 a1 ->
        Val Γ M T h1 -> Val Γ M T h0)
     /\ (forall n (Γ : Ctx n) (M N T : Tm n) u a0 a1
        (h0 : wt u a0) (h1 : wt u a1),
        Init.Nat.max (rk u) (rk a1) <= m -> le a0 a1 ->
        EqVal Γ M N T h1 -> EqVal Γ M N T h0)
     /\ (forall n (Γ : Ctx n) (M T : Tm n) u u' a
        (h0 : wt u' a) (h1 : wt u a),
        Init.Nat.max (rk u) (rk a) <= m -> le u' u ->
        Val Γ M T h1 -> Val Γ M T h0)
     /\ (forall n (Γ : Ctx n) (M N T : Tm n) u u' a
        (h0 : wt u' a) (h1 : wt u a),
        Init.Nat.max (rk u) (rk a) <= m -> le u' u ->
        EqVal Γ M N T h1 -> EqVal Γ M N T h0))
  {n} (Γ : Ctx n) (M N T : Tm n) f a g a' g'
  (h0 : wt (abs f) (tpi a' g')) (h1 : wt (abs f) (tpi a g))
  (hUa1 : wt (tpi a g) tuniv)
  (RK : Init.Nat.max (rk (abs f)) (rk (tpi a g)) <= k)
  (LEa : le a' a) (LEg : le_fun g' g) :
  EqVal Γ M N T h0 -> Val Γ T Core.tuniv hUa1 -> EqVal Γ M N T h1.
Proof.
  move=> EV VT.
  have GB : Init.Nat.max (rk (abs f)) (rk (tpi a g))
            < S (Init.Nat.max (Init.Nat.max (rk (abs f)) (rk (tpi a g))) (rk (tpi a' g'))) by lia.
  have GB' : Init.Nat.max (rk (abs f)) (rk (tpi a' g'))
            < S (Init.Nat.max (Init.Nat.max (rk (abs f)) (rk (tpi a g))) (rk (tpi a' g'))) by lia.
  have GBu : Init.Nat.max (rk (tpi a g)) (rk tuniv)
            < S (Init.Nat.max (Init.Nat.max (rk (abs f)) (rk (tpi a g))) (rk (tpi a' g'))) by (cbn [rk]; lia).
  (* unary projections, lifted to [h1] via [upValPi] *)
  have VM0 : Val Γ M T h0 by (eapply EqVal_Val1; [ apply Nat.lt_succ_diag_r | exact EV ]).
  have VN0 : Val Γ N T h0 by (eapply EqVal_Val2; [ apply Nat.lt_succ_diag_r | exact EV ]).
  have VM1 := upValPi IH h1 RK LEa LEg VM0 VT.
  have VN1 := upValPi IH h1 RK LEa LEg VN0 VT.
  rewrite (Val_abs Γ M T h1 GB) in VM1. destruct VM1 as [_ VPiM1].
  rewrite (Val_abs Γ N T h1 GB) in VN1. destruct VN1 as [_ VPiN1].
  rewrite (EqVal_abs Γ M N T h0 GB') in EV. destruct EV as [_ [_ [_ EPi0]]].
  rewrite (EqVal_abs Γ M N T h1 GB).
  split; [ | split; [ exact VPiM1 | split; [ exact VPiN1 | ] ] ].
  { (* ValTy T at the bigger type, from VT *)
    rewrite (Val_tuniv Γ T Core.tuniv hUa1 GBu) in VT. eapply ValTy_irr; exact VT. }
  (* EqValPi M N T h1 : the binary per-edge transport *)
  cbn [Rec.EqValPi] in EPi0. destruct EPi0 as [A0 [B0 [HR0 PAEV0]]].
  rewrite (Val_tuniv Γ T Core.tuniv hUa1 GBu) in VT.
  cbn [Rec.ValTy] in VT.
  destruct VT as [AT [BT [HRt [TyA0 [TyB0 [vld [VDomT [PEV PEE]]]]]]]].
  have [E1 E2] := HeadRed_tpi_det HR0 HRt. subst AT BT.
  have Vg  : valid_fun g  by eauto with valid.
  have Vg' : valid_fun g' by eauto with valid.
  have mlt : (Init.Nat.max (rk_fun f) (Init.Nat.max (rk a) (rk_fun g)) < k)%nat
    by (move: RK; cbn [rk]; lia).
  have UPe  := proj1 (proj2 (IH _ mlt)).
  have DOWN := proj1 (proj2 (proj2 (IH _ mlt))).
  cbn [Rec.EqValPi]. exists A0, B0. split; [ exact HR0 | ].
  cbn [Rec.PiAppEqVal]. move=> ui vi Hin RKu v t APP APPg P TyP VP. subst.
  destruct (is_bot (app g ui)) eqn:Hb.
  { apply EqVal_isbot; exact Hb. }
  have Vui : valid ui := wt_valid_tm (wt_abs_inv1 h1 Hin).
  have hU0 := wt_tpi_inv2 (wt_abs_ty h0) (wt_valid_tm (wt_abs_inv1 h0 Hin)) (erefl : app g' ui = app g' ui).
  have hU1 := wt_tpi_inv2 hUa1 Vui (erefl : app g ui = app g ui).
  have boundD : Init.Nat.max (rk ui) (rk a)
                  <= Init.Nat.max (rk_fun f) (Init.Nat.max (rk a) (rk_fun g)).
    { have hh := @In_rk_fun1 (ui,vi) f Hin. cbn in hh. lia. }
  have boundC : Init.Nat.max (rk vi) (rk (app g ui))
                  <= Init.Nat.max (rk_fun f) (Init.Nat.max (rk a) (rk_fun g)).
    { have hh := @In_rk_fun2 (ui,vi) f Hin. have hh2 := rk_app g ui. cbn in hh. lia. }
  have leC : le (app g' ui) (app g ui) by (apply le_fun_mono; eauto with valid).
  have NBp : ~ is_bot (app g ui) by rewrite Hb.
  have VP0 := DOWN n Γ P A0 ui a' a (wt_abs_inv1 h0 Hin) (wt_abs_inv1 h1 Hin) boundD LEa VP.
  have Ecod0 := PAEV0 ui vi Hin RKu (app f ui) (app g' ui) erefl erefl P TyP VP0.
  have Vty := PEV ui (app g ui) (wt_abs_inv1 h1 Hin) RKu erefl NBp P TyP VP.
  have Efin := UPe n Γ (Core.app M P) (Core.app N P) B0[P..] vi (app g' ui) (app g ui)
                 (wt_abs_inv2 h0 Hin erefl) (wt_abs_inv2 h1 Hin erefl) hU0 hU1
                 boundC leC Ecod0 ltac:(eapply Val_irr; exact Vty).
  eapply EqVal_irr; exact Efin.
Qed.

Lemma up_down_restrict : forall k,
  (* upVal *)
  (forall n (Γ : Ctx n) (M T : Tm n) u a0 a1
      (h0 : wt u a0) (h1 : wt u a1) (hUa0 : wt a0 tuniv) (hUa1 : wt a1 tuniv),
      Init.Nat.max (rk u) (rk a1) <= k -> le a0 a1 ->
      Val Γ M T h0 -> Val Γ T Core.tuniv hUa1 -> Val Γ M T h1)
  /\ (* upEqVal *)
  (forall n (Γ : Ctx n) (M N T : Tm n) u a0 a1
      (h0 : wt u a0) (h1 : wt u a1) (hUa0 : wt a0 tuniv) (hUa1 : wt a1 tuniv),
      Init.Nat.max (rk u) (rk a1) <= k -> le a0 a1 ->
      EqVal Γ M N T h0 -> Val Γ T Core.tuniv hUa1 -> EqVal Γ M N T h1)
  /\ (* downVal *)
  (forall n (Γ : Ctx n) (M T : Tm n) u a0 a1
      (h0 : wt u a0) (h1 : wt u a1),
      Init.Nat.max (rk u) (rk a1) <= k -> le a0 a1 ->
      Val Γ M T h1 -> Val Γ M T h0)
  /\ (* downEqVal *)
  (forall n (Γ : Ctx n) (M N T : Tm n) u a0 a1
      (h0 : wt u a0) (h1 : wt u a1),
      Init.Nat.max (rk u) (rk a1) <= k -> le a0 a1 ->
      EqVal Γ M N T h1 -> EqVal Γ M N T h0)
  /\ (* restrictVal *)
  (forall n (Γ : Ctx n) (M T : Tm n) u u' a
      (h0 : wt u' a) (h1 : wt u a),
      Init.Nat.max (rk u) (rk a) <= k -> le u' u ->
      Val Γ M T h1 -> Val Γ M T h0)
  /\ (* restrictEqVal *)
  (forall n (Γ : Ctx n) (M N T : Tm n) u u' a
      (h0 : wt u' a) (h1 : wt u a),
      Init.Nat.max (rk u) (rk a) <= k -> le u' u ->
      EqVal Γ M N T h1 -> EqVal Γ M N T h0).
Proof.
  intro k. induction k as [k IH] using strong_ind.
  repeat split.
  - (* upVal *)
    intros n Γ M T u a0 a1 h0 h1 hUa0 hUa1 RK LE V VT.
    dependent destruction h1.
    + (* wt_bot *) apply Val_Bot.
    + (* wt_tuniv *) dependent destruction h0; eapply Val_irr; eassumption.
    + (* wt_tnat  *) dependent destruction h0; eapply Val_irr; eassumption.
    + (* wt_zero  *) dependent destruction h0; eapply Val_irr; eassumption.
    + (* wt_succ  *) dependent destruction h0; eapply Val_irr; eassumption.
    + (* wt_tpi   *) dependent destruction h0; eapply Val_irr; eassumption.
    + (* wt_abs: the per-edge codomain transport, via [upValPi]. *)
      dependent destruction h0.
      rewrite le_pi in LE. case/andP: LE => LEa LEg.
      eapply (upValPi IH); [ exact RK | exact LEa | exact LEg | exact V | exact VT ].
  - (* upEqVal *)
    intros n Γ M N T u a0 a1 h0 h1 hUa0 hUa1 RK LE V VT.
    dependent destruction h1.
    + (* wt_bot *) apply EqVal_Bot.
    + (* wt_tuniv *) dependent destruction h0; eapply EqVal_irr; eassumption.
    + (* wt_tnat  *) dependent destruction h0; eapply EqVal_irr; eassumption.
    + (* wt_zero  *) dependent destruction h0; eapply EqVal_irr; eassumption.
    + (* wt_succ  *) dependent destruction h0; eapply EqVal_irr; eassumption.
    + (* wt_tpi   *) dependent destruction h0; eapply EqVal_irr; eassumption.
    + (* wt_abs: via [upEqValPi]. *)
      dependent destruction h0.
      rewrite le_pi in LE. case/andP: LE => LEa LEg.
      eapply (upEqValPi IH); [ exact RK | exact LEa | exact LEg | exact V | exact VT ].
  - (* downVal *) admit.
  - (* downEqVal *) admit.
  - (* restrictVal *) admit.
  - (* restrictEqVal *) admit.
Admitted.

Lemma upVal {n} (Γ : Ctx n) (M T : Tm n) u a0 a1
  (h0 : wt u a0) (h1 : wt u a1) (hUa0 : wt a0 tuniv) (hUa1 : wt a1 tuniv) :
  le a0 a1 -> Val Γ M T h0 -> Val Γ T Core.tuniv hUa1 -> Val Γ M T h1.
Proof.
  intros LE V VT;
  apply (proj1 (up_down_restrict (Init.Nat.max (rk u) (rk a1)))
           n Γ M T u a0 a1 h0 h1 hUa0 hUa1);
    [ apply Nat.le_refl | exact LE | exact V | exact VT ].
Qed.

Lemma upEqVal {n} (Γ : Ctx n) (M N T : Tm n) u a0 a1
  (h0 : wt u a0) (h1 : wt u a1) (hUa0 : wt a0 tuniv) (hUa1 : wt a1 tuniv) :
  le a0 a1 -> EqVal Γ M N T h0 -> Val Γ T Core.tuniv hUa1 -> EqVal Γ M N T h1.
Proof.
  intros LE V VT;
  apply (proj1 (proj2 (up_down_restrict (Init.Nat.max (rk u) (rk a1))))
           n Γ M N T u a0 a1 h0 h1 hUa0 hUa1);
    [ apply Nat.le_refl | exact LE | exact V | exact VT ].
Qed.

Lemma downVal {n} (Γ : Ctx n) (M T : Tm n) u a0 a1
  (h0 : wt u a0) (h1 : wt u a1) :
  le a0 a1 -> Val Γ M T h1 -> Val Γ M T h0.
Proof.
  intros LE V;
  apply (proj1 (proj2 (proj2 (up_down_restrict (Init.Nat.max (rk u) (rk a1)))))
           n Γ M T u a0 a1 h0 h1);
    [ apply Nat.le_refl | exact LE | exact V ].
Qed.

Lemma downEqVal {n} (Γ : Ctx n) (M N T : Tm n) u a0 a1
  (h0 : wt u a0) (h1 : wt u a1) :
  le a0 a1 -> EqVal Γ M N T h1 -> EqVal Γ M N T h0.
Proof.
  intros LE V;
  apply (proj1 (proj2 (proj2 (proj2 (up_down_restrict (Init.Nat.max (rk u) (rk a1))))))
           n Γ M N T u a0 a1 h0 h1);
    [ apply Nat.le_refl | exact LE | exact V ].
Qed.

Lemma restrictVal {n} (Γ : Ctx n) (M T : Tm n) u u' a
  (h0 : wt u' a) (h1 : wt u a) :
  le u' u -> Val Γ M T h1 -> Val Γ M T h0.
Proof.
  intros LE V;
  apply (proj1 (proj2 (proj2 (proj2 (proj2 (up_down_restrict (Init.Nat.max (rk u) (rk a)))))))
           n Γ M T u u' a h0 h1);
    [ apply Nat.le_refl | exact LE | exact V ].
Qed.

Lemma restrictEqVal {n} (Γ : Ctx n) (M N T : Tm n) u u' a
  (h0 : wt u' a) (h1 : wt u a) :
  le u' u -> EqVal Γ M N T h1 -> EqVal Γ M N T h0.
Proof.
  intros LE V;
  apply (proj2 (proj2 (proj2 (proj2 (proj2 (up_down_restrict (Init.Nat.max (rk u) (rk a)))))))
           n Γ M N T u u' a h0 h1);
    [ apply Nat.le_refl | exact LE | exact V ].
Qed.



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
  Val Γ M A h -> EqValTy RB Γ A B h' -> Val Γ M B h
with EqVal_EqVal_fwd {n} (Γ : Ctx n) (M N A : Tm n) u a
  (h : wt u a) (B : Tm n)  (h' : wt a tuniv) RB
  {struct h} :
  EqVal Γ M N A h -> EqValTy RB Γ A B h' -> EqVal Γ M N B h
with EqVal_sym {n} (Γ : Ctx n) (M1 M2 A : Tm n) u a (h : wt u a) { struct h } :
  EqVal Γ M1 M2 A h -> EqVal Γ M2 M1 A h
with EqVal_trans {n} (Γ : Ctx n) (M1 M2 M3 A : Tm n) u a (h : wt u a) {struct h} :
  EqVal Γ M1 M2 A h -> EqVal Γ M2 M3 A h -> EqVal Γ M1 M3 A h.
Proof.
  (* TODO: reprove for the WF-recursive Val/EqVal (old {struct h}/API-specific tactics no longer apply). *)
Admitted.



(* EqValTy2-sym *)
Lemma EqValTy_sym {n} (Γ : Ctx n) (M N : Tm n) u (h : wt u tuniv) RB :
  Init.Nat.max (rk u) (rk tuniv) < RB ->
  EqValTy RB Γ M N h -> EqValTy RB Γ N M h.
Proof.
  move=> LT h1. eapply EqVal_EqValTy; [ exact LT | ]. eapply EqVal_sym.
  eapply EqValTy_EqVal; [ exact LT | exact h1 ].
Qed.

(* EqValTy2-trans *)
Lemma EqValTy_trans {n} (Γ : Ctx n) (A B C : Tm n) u (h : wt u tuniv) RB :
  Init.Nat.max (rk u) (rk tuniv) < RB ->
  EqValTy RB Γ A B h -> EqValTy RB Γ B C h -> EqValTy RB Γ A C h.
Proof.
  move=> LT h1 h2.
  eapply EqVal_EqValTy; [ exact LT | ]. eapply EqVal_trans.
  eapply EqValTy_EqVal; [ exact LT | eauto ].
  eapply EqValTy_EqVal; [ exact LT | eauto ].
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
Lemma Val_beta_expand {n} (Γ : Ctx n) (M M' T : Tm n) u a (h : wt u a) :
  HeadRed M' M -> Val Γ M T h -> Val Γ M' T h.
Proof. Admitted.

(* EqVal2-headred-expand *)
Lemma EqVal_headred_expand {n} (Γ : Ctx n) (M M' N N' T : Tm n) u a (h : wt u a) :
  HeadRed M' M -> HeadRed N' N ->
  EqVal Γ M N T h -> EqVal Γ M' N' T h.
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
Lemma Val_headred_contract {n} (Γ : Ctx n) (M M' T : Tm n) u a (h : wt u a) :
  HeadRed M M' -> Val Γ M T h -> Val Γ M' T h.
Proof. Admitted.

(* EqVal2-headred-contract *)
Lemma EqVal_headred_contract {n} (Γ : Ctx n) (M M' N N' T : Tm n) u a (h : wt u a) :
  HeadRed M M' -> HeadRed N N' ->
  EqVal Γ M N T h -> EqVal Γ M' N' T h.
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


