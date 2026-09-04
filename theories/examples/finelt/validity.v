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

Require raw_validity.
Module R := raw_validity.


Import SyntaxNotations.
Import SubstNotations.
Import typing.Notations.

Open Scope syntax_scope.
Import Raw.

Definition Val {n} (Γ : Ctx n) (M A : Tm n) {u a} (h: wt u a) : Prop := 
  forall k, max (rk u) (rk a) < k -> R.Val k Γ M A h.
Definition EqVal {n} (Γ : Ctx n) (M N A : Tm n) {u a} (h: wt u a) : Prop := 
  forall k, max (rk u) (rk a) < k -> R.EqVal k Γ M N A h.
Definition ValTy {n} (Γ : Ctx n) (M : Tm n) {u} (h: wt u tuniv) : Prop := 
  forall k, max (rk u) 1 < k -> R.ValTy k Γ M h.
Definition EqValTy {n} (Γ : Ctx n) (M N : Tm n) {u} (h: wt u tuniv) : Prop := 
  forall k, max (rk u) 1 < k -> R.EqValTy k Γ M N h.

Lemma EqVal_Val1 
Lemma Val_EqVal
Lemma Val_transport
Lemma Val_transport_up


