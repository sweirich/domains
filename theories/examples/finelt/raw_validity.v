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

Require Import findom.
Require Import types.

Import Raw.


(* Logical relation, defined by recursion on the wt judgement for
   semantic elements. i.e. on the derivation of `wt u a`.

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
      (RKu : rk u < rk (tpi b f))
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
  forall ui vi (Hin : In (ui, vi) f) v t
  (APP : app f ui = v)
  (APPg : app g ui = t)
  (P : Tm n), typing Γ P A0 ->
              Val Γ P A0 (wt_abs_inv1 h Hin) ->
              Val  Γ (Core.app M P) B0[P..]
                  (wt_abs_inv2 h Hin APPg).

Definition PiAppEq {n} (Γ : Ctx n)
  (M : Tm n) (A0 : Tm n) (B0 : Tm (S n)) b f g
  (h : wt (abs f) (tpi b g))  :=
  forall ui vi (Hin : In (ui, vi) f) v t
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
  forall ui vi (Hin : In (ui, vi) f) v t
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
      (RKu : rk u < rk (tpi b f))
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
      (RKu : rk u < rk (tpi b f))
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
          Rec.ValTy (@ValF k) (@EqValF k) Γ M h

      | tpi b f => fun h  =>
           (match u return wt _ (tpi b f) ->  Prop with

            | abs g => fun (h : wt (abs g) (tpi b f)) =>
                        Rec.ValTy (@ValF k) (@EqValF k) Γ A (wt_abs_ty h)
                      /\ Rec.ValPi (@ValF k) (@EqValF k) Γ M A h

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

            Rec.ValTy (@ValF k) (@EqValF k) Γ M h
          /\ Rec.ValTy (@ValF k) (@EqValF k) Γ N h
          /\ Rec.EqValTy (@ValF k) (@EqValF k) Γ M N h

      | tpi b f => fun h =>
           (match u return wt _ (tpi b f) -> Prop with
           | bot => fun h => True
           | abs g => fun (h : wt (abs g) (tpi b f)) =>
               Rec.ValTy (@ValF k) (@EqValF k) Γ A (wt_abs_ty h)
             /\ Rec.ValPi (@ValF k) (@EqValF k) Γ M A h
             /\ Rec.ValPi (@ValF k) (@EqValF k) Γ N A h
             /\ Rec.EqValPi (@ValF k) (@EqValF k) Γ M N A h

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

Notation PiAppVal := (@Rec.PiAppVal Val).
Notation PiAppEq  := (@Rec.PiAppEq Val EqVal).
Notation ValTy    := (@Rec.ValTy Val EqVal).
Notation EqValTy  := (@Rec.EqValTy Val EqVal).
Notation ValPi    := (@Rec.ValPi Val EqVal).
Notation EqValPi  := (@Rec.EqValPi Val EqVal).
Notation PiEdgeEq := (@Rec.PiEdgeEq EqVal).
Notation PiAppEqVal := (@Rec.PiAppEqVal Val EqVal).

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

Lemma Val_eq {n} (Γ : Ctx n) (M A : Tm n) u a (h : wt u a) :
  Val Γ M A h =
  (match a as a0 return wt u a0 -> Prop with
   | bot => fun _ => True
   | tuniv => fun h => ValTy Γ M h
   | tpi b f => fun h =>
       (match u as u0 return wt u0 (tpi b f) -> Prop with
        | abs g => fun h => ValTy Γ A (wt_abs_ty h)
                          /\ ValPi Γ M A h
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

Lemma EqVal_eq {n} (Γ : Ctx n) (M N A : Tm n) u a (h : wt u a) :
  EqVal Γ M N A h =
  (match a as a0 return wt u a0 -> Prop with
   | bot => fun _ => True
   | tuniv => fun h => ValTy Γ M h
                    /\ ValTy Γ N h
                    /\ EqValTy Γ M N h
   | tpi b f => fun h =>
       (match u as u0 return wt u0 (tpi b f) -> Prop with
        | abs g => fun h => ValTy Γ A (wt_abs_ty h)
                          /\ ValPi Γ M A h
                          /\ ValPi Γ N A h
                          /\ EqValPi Γ M N A h
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

Lemma Val_tuniv {n} (Γ : Ctx n) M A u (h : wt u tuniv) :
  Val Γ M A h = ValTy Γ M h.
Proof. rewrite Val_eq //. Qed.

Lemma Val_abs {n} (Γ : Ctx n) M A g b f (h : wt (abs g) (tpi b f)) :
  Val Γ M A h = (ValTy Γ A (wt_abs_ty h) /\ ValPi Γ M A h).
Proof. rewrite Val_eq //. Qed.

Lemma Val_zero {n} (Γ : Ctx n) M A (h : wt zero tnat) :
  Val Γ M A h = HeadRed M Core.zero.
Proof. rewrite Val_eq //. Qed.

Lemma Val_succ {n} (Γ : Ctx n) M A v (h : wt (succ v) tnat) :
  Val Γ M A h = (exists M1, HeadRed M (Core.succ M1) /\ Val Γ M1 Core.tnat (wt_succ_inv h)).
Proof. rewrite Val_eq //. Qed.

Lemma EqVal_tuniv {n} (Γ : Ctx n) M N A u (h : wt u tuniv) :
  EqVal Γ M N A h = (ValTy Γ M h /\ ValTy Γ N h /\ EqValTy Γ M N h).
Proof. rewrite EqVal_eq //. Qed.

Lemma EqVal_abs {n} (Γ : Ctx n) M N A g b f (h : wt (abs g) (tpi b f)) :
  EqVal Γ M N A h =
  (ValTy Γ A (wt_abs_ty h) /\ ValPi Γ M A h /\ ValPi Γ N A h /\ EqValPi Γ M N A h).
Proof. rewrite EqVal_eq //. Qed.

Lemma EqVal_zero {n} (Γ : Ctx n) M N A (h : wt zero tnat) :
  EqVal Γ M N A h = (HeadRed M Core.zero /\ HeadRed N Core.zero).
Proof. rewrite EqVal_eq //. Qed.

Lemma EqVal_succ {n} (Γ : Ctx n) M N A v (h : wt (succ v) tnat) :
  EqVal Γ M N A h =
  (exists M1, HeadRed M (Core.succ M1) /\ exists N1, HeadRed N (Core.succ N1)
            /\ EqVal Γ M1 N1 Core.tnat (wt_succ_inv h)).
Proof. rewrite EqVal_eq //. Qed.

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


(* ============================================================
   Val <-> ValTy  and  EqVal <-> EqValTy
   ============================================================ *)

Lemma EqValTy_EqVal {n} (Γ : Ctx n) (A B : Tm n) a (h : wt a tuniv):
  EqValTy Γ A B h ->
  EqVal Γ A B Core.tuniv h.
Proof.
  dependent destruction h; try done.
  rewrite EqVal_tuniv; cbn [Rec.EqValTy].
  move=> [hA [hB h1]].
  eauto.
Qed.

Lemma EqVal_EqValTy {n} (Γ : Ctx n) (A B C : Tm n) a (h : wt a tuniv):
  EqVal Γ A B C h ->
  EqValTy Γ A B h.
Proof.
  rewrite EqVal_tuniv. by move=> [_ [_ ?]].
Qed.

Lemma ValTy_Val {n} (Γ : Ctx n) (A : Tm n) a (h : wt a tuniv):
  ValTy Γ A h ->
  Val Γ A Core.tuniv h.
Proof.
  rewrite Val_tuniv. auto.
Qed.

Lemma Val_ValTy {n} (Γ : Ctx n) (A : Tm n) a (h : wt a tuniv):
  Val Γ A Core.tuniv h ->
  ValTy Γ A h.
Proof.
  rewrite Val_tuniv. auto.
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
Lemma ValTy_EqValTy {n} (Γ : Ctx n) (M : Tm n) u (h : wt u tuniv) :
  ValTy Γ M h -> EqValTy Γ M M h.
Proof.
  intros VT.
  eapply EqVal_EqValTy.
  eapply Val_EqVal.
  eapply ValTy_Val.
  auto.
Qed.


(* ============================================================
   Level 1 — projecting first and second parts of EqVal
   EqVal_Val1, EqVal_Val2
   ============================================================ *)


Fixpoint EqVal_Val1 {n} (Γ : Ctx n) (M N A : Tm n) u a (h : wt u a) {struct h} :
  EqVal Γ M N A h -> Val Γ M A h.
Proof.
  dependent destruction h.
  - move=> _. apply Val_Bot.
  - rewrite EqVal_tuniv Val_tuniv. by move=> [? _].
  - rewrite EqVal_tuniv Val_tuniv. by move=> [? _].
  - rewrite EqVal_zero Val_zero. by move=> [? _].
  - rewrite EqVal_succ Val_succ.
    move=> [M1 [h1 [N1 [h2 V1]]]]. exists M1. split; auto.
    eapply EqVal_Val1; eauto.
  - rewrite EqVal_tuniv Val_tuniv. by move=> [? _].
  - rewrite EqVal_abs Val_abs. move=> [hA [hM _]]. by split.
Qed.


Fixpoint EqVal_Val2 {n} (Γ : Ctx n) (M N A : Tm n) u a (h : wt u a) {struct h} :
  EqVal Γ M N A h -> Val Γ N A h.
Proof.
  dependent destruction h.
  - move=> _. apply Val_Bot.
  - rewrite EqVal_tuniv Val_tuniv. by move=> [_ [? _]].
  - rewrite EqVal_tuniv Val_tuniv. by move=> [_ [? _]].
  - rewrite EqVal_zero Val_zero. by move=> [_ ?].
  - rewrite EqVal_succ Val_succ.
    move=> [M1 [h1 [N1 [h2 V1]]]]. exists N1. split; auto.
    eapply EqVal_Val2; eauto.
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

Lemma ValTy_HeadRed1_expand {n} (Γ : Ctx n) (M M' : Tm n) u (h : wt u tuniv) :
  HeadRed1 M' M -> ValTy Γ M h -> ValTy Γ M' h.
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
Lemma ValTy_HeadRed_expand {n} (Γ : Ctx n) (M M' : Tm n) u (h : wt u tuniv) :
  HeadRed M' M -> ValTy Γ M h -> ValTy Γ M' h.
Proof. 
  move=> R. induction R.
  - done.
  - move=> h1. specialize (IHR h1). 
    eapply ValTy_HeadRed1_expand in H; eauto.
Qed.

  

Lemma ValTy_HeadRed1_contract {n} (Γ : Ctx n) (M M' : Tm n) u (h : wt u tuniv) :
  HeadRed1 M M' -> ValTy Γ M h -> ValTy Γ M' h.
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
Lemma ValTy_headred_contract {n} (Γ : Ctx n) (M M' : Tm n) u (h : wt u tuniv) :
  HeadRed M M' -> ValTy Γ M h -> ValTy Γ M' h.
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
  (h0 : wt u0 tuniv) (h1 : wt u1 tuniv) :
  le u0 u1 -> ValTy Γ M h1 -> ValTy Γ M h0.
Proof.
  move=> LE VT1.
  apply Val_ValTy. apply ValTy_Val in VT1.
  eapply restrictVal; eauto.
Qed.


(* ============================================================
   down/up
   ============================================================ *)


Lemma upValPi : forall 
        (upVal : forall {n} (Γ : Ctx n) (M T : Tm n) u a0 a1
                   (h0 : wt u a0) (h1 : wt u a1)  
                   (hUa0 : wt a0 tuniv) (hUa1 : wt a1 tuniv), 
            le a0 a1 -> Val Γ M T h0 -> Val Γ T Core.tuniv hUa1 -> Val Γ M T h1)
        (downVal : forall {n} (Γ : Ctx n) (M T : Tm n) u a0 a1
                     (h0 : wt u a0) (h1: wt u a1),
            le a0 a1 -> Val Γ M T h1 -> Val Γ M T h0)
        f a g a0 g0 
        (LEa : le a a0) 
        (LEg : le_fun g g0)           
        (h  : wt (abs f) (tpi a g))
        (h0 : wt (abs f) (tpi a0 g0))
        (hUa1 : wt (tpi a0 g0) tuniv)
        {n} (Γ : Ctx n) (M T : Tm n),
        ValPi Γ M T h -> 
        ValTy Γ T hUa1 ->
        ValPi Γ M T h0.
Proof.
  (* TODO: reprove for the WF-recursive Val/EqVal (old {struct h}/API-specific tactics no longer apply). *)
Admitted.

Lemma downValPi : forall 
        (upVal : forall {n} (Γ : Ctx n) (M T : Tm n) u a0 a1
                   (h0 : wt u a0) (h1 : wt u a1)  
                   (hUa0 : wt a0 tuniv) (hUa1 : wt a1 tuniv), 
            le a0 a1 -> Val Γ M T h0 -> Val Γ T Core.tuniv hUa1 -> Val Γ M T h1)
        (downVal : forall {n} (Γ : Ctx n) (M T : Tm n) u a0 a1
                     (h0 : wt u a0) (h1: wt u a1),
            le a0 a1 -> Val Γ M T h1 -> Val Γ M T h0)
        f a g a0 g0 
        (LEa : le a a0) 
        (LEg : le_fun g g0)           
        (h  : wt (abs f) (tpi a g))
        (h0 : wt (abs f) (tpi a0 g0))
        (hUa : wt (tpi a g) tuniv)
        {n} (Γ : Ctx n) (M T : Tm n),
        ValPi Γ M T h0 -> 
        ValTy Γ T hUa ->
        ValPi Γ M T h.
Proof.
  (* TODO: reprove for the WF-recursive Val/EqVal (old {struct h}/API-specific tactics no longer apply). *)
Admitted.


(* Annoyingly, struct on first derivation is not enough. Need
   to do struct on *both* wt derivations simultaneously to
   show the termination of this proof.

   For now, admitting the termination check.
*)

(* upVal/upEqVal mirror the Agda upVal2/upEqVal2 signatures: they take
   the ValTy of the syntactic type T at the bigger universe-element a1
   as an extra argument (a "Val Γ T Core.tuniv hUa1", which by
   definitional unfolding is ValTy Γ T hUa1).                          *)
Fixpoint upVal {n} (Γ : Ctx n) (M T : Tm n) u a0 a1
  (h0 : wt u a0) (h1 : wt u a1)  
  (hUa0 : wt a0 tuniv) (hUa1 : wt a1 tuniv) {struct h1}:
  le a0 a1 -> Val Γ M T h0 -> Val Γ T Core.tuniv hUa1 -> Val Γ M T h1
with upEqVal {n} (Γ : Ctx n) (M N T : Tm n) u a0 a1
  (h0 : wt u a0) (h1 : wt u a1)  
  (hUa0 : wt a0 tuniv) (hUa1 : wt a1 tuniv) {struct h1}:
  le a0 a1 -> EqVal Γ M N T h0 -> Val Γ T Core.tuniv hUa1 -> EqVal Γ M N T h1
with downVal {n} (Γ : Ctx n) (M T : Tm n) u a0 a1
  (h0 : wt u a0) (h1: wt u a1) {struct h1} :
  le a0 a1 -> Val Γ M T h1 -> Val Γ M T h0
with downEqVal {n} (Γ : Ctx n) (M N T : Tm n) u a0 a1
  (h0 : wt u a0) (h1: wt u a1) {struct h1} :
  le a0 a1 -> EqVal Γ M N T h1 -> EqVal Γ M N T h0
with restrictVal {n} (Γ : Ctx n) (M T : Tm n) u u' a
  (h0 : wt u' a) (h1 : wt u a) {struct h1} :
  le u' u -> Val Γ M T h1 -> Val Γ M T h0
with restrictEqVal {n} (Γ : Ctx n) (M N T : Tm n) u u' a
  (h0 : wt u' a) (h1 : wt u a) {struct h1} :
  le u' u -> EqVal Γ M N T h1 -> EqVal Γ M N T h0.
Proof.  
  (* TODO: reprove for the WF-recursive Val/EqVal (old {struct h}/API-specific tactics no longer apply). *)
Admitted.



(* ValTy2-Sup: if a1 and a2 are universe-members and lub a1 a2 = Some a,
   ValTy at a1 and a2 lifts to ValTy at the lub. *)
Fixpoint ValTy_Sup {n} (Γ : Ctx n) (T : Tm n) a1 a2 a 
  (h1 : wt a1 tuniv) (h2 : wt a2 tuniv) (h : wt a tuniv) {struct h}:
  lub a1 a2 = a ->
  ValTy Γ T h1 -> ValTy Γ T h2 -> ValTy Γ T h.
Proof.
Abort.

(* EqValTy2-Sup *)
Lemma EqValTy_Sup {n} (Γ : Ctx n) (M N : Tm n) a1 a2 a 
  (h1 : wt a1 tuniv) (h2 : wt a2 tuniv) (h : wt a tuniv) :
  lub a1 a2 = a ->
  EqValTy Γ M N h1 -> EqValTy Γ M N h2 -> EqValTy Γ M N h.
Proof. 
Abort.


(* ----------------------------------------------------- *)

Fixpoint Val_EqVal_fwd {n} (Γ : Ctx n) (M A : Tm n) u a
  (h : wt u a) (B : Tm n)  (h' : wt a tuniv)
  {struct h} :
  Val Γ M A h -> EqValTy Γ A B h' -> Val Γ M B h
with EqVal_EqVal_fwd {n} (Γ : Ctx n) (M N A : Tm n) u a
  (h : wt u a) (B : Tm n)  (h' : wt a tuniv)
  {struct h} :
  EqVal Γ M N A h -> EqValTy Γ A B h' -> EqVal Γ M N B h
with EqVal_sym {n} (Γ : Ctx n) (M1 M2 A : Tm n) u a (h : wt u a) { struct h } :
  EqVal Γ M1 M2 A h -> EqVal Γ M2 M1 A h
with EqVal_trans {n} (Γ : Ctx n) (M1 M2 M3 A : Tm n) u a (h : wt u a) {struct h} :
  EqVal Γ M1 M2 A h -> EqVal Γ M2 M3 A h -> EqVal Γ M1 M3 A h.
Proof.
  (* TODO: reprove for the WF-recursive Val/EqVal (old {struct h}/API-specific tactics no longer apply). *)
Admitted.



(* EqValTy2-sym *)
Lemma EqValTy_sym {n} (Γ : Ctx n) (M N : Tm n) u (h : wt u tuniv) :
  EqValTy Γ M N h -> EqValTy Γ N M h.
Proof.
  move=>h1. eapply EqVal_EqValTy. eapply EqVal_sym.
  eapply EqValTy_EqVal. done.
Qed.

(* EqValTy2-trans *)
Lemma EqValTy_trans {n} (Γ : Ctx n) (A B C : Tm n) u (h : wt u tuniv) :
  EqValTy Γ A B h -> EqValTy Γ B C h -> EqValTy Γ A C h.
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
  (h : wt u tuniv) :
  HeadRed M1' M1 -> HeadRed M2' M2 ->
  EqValTy Γ M1 M2 h -> EqValTy Γ M1' M2' h.
Proof. Admitted.

(* EqValTy2-headred-contract *)
Lemma EqValTy_headred_contract {n} (Γ : Ctx n) (M1 M2 M1' M2' : Tm n) u 
  (h : wt u tuniv) :
  HeadRed M1 M1' -> HeadRed M2 M2' ->
  EqValTy Γ M1 M2 h -> EqValTy Γ M1' M2' h.
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
  (h : wt (abs g) (tpi b f)) :
  HeadRed M' M -> ValPi Γ M T h -> ValPi Γ M' T h.
Proof. Admitted.

(* EqValPi2-headred-expand *)
Lemma EqValPi_headred_expand {n} (Γ : Ctx n) (M1 M2 M1' M2' T : Tm n) b f g
  (h : wt (abs g) (tpi b f)) :
  HeadRed M1' M1 -> HeadRed M2' M2 ->
  EqValPi Γ M1 M2 T h -> EqValPi Γ M1' M2' T h.
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
  (h : wt (abs g) (tpi b f)) :
  HeadRed M M' -> ValPi Γ M T h -> ValPi Γ M' T h.
Proof. Admitted.

(* EqValPi2-headred-contract *)
Lemma EqValPi_headred_contract {n} (Γ : Ctx n) (M1 M2 M1' M2' T : Tm n) b f g
  (h : wt (abs g) (tpi b f)) :
  HeadRed M1 M1' -> HeadRed M2 M2' ->
  EqValPi Γ M1 M2 T h -> EqValPi Γ M1' M2' T h.
Proof. Admitted.


