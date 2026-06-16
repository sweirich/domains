From Stdlib Require Import Relations List Program
     ssreflect ssrfun ssrbool.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

From Stdlib Require Import Classes.RelationClasses Classes.Morphisms Lia Arith.

Require Import smpl.Smpl.
Require Import utils.all.
Require Import finelt.utils.

From Equations Require Import Equations.

Require Import findom.
Import findom.Raw.
Require Import types.

(* ============================================================
   Selection.v  —  Coq port of MIN/Model/Selection.agda

   A [Selection f u v] is a "compatible sub-multiset" of the finite
   function [f]: [u] is the join (lub) of a chosen subset of [f]'s keys
   and [v] the join of the corresponding values.  [sel_take] records the
   compatibility of each selected key/value with the running join, so
   the joins stay valid.

   This is the infrastructure that the function-VALUE edge of the
   logical relation must quantify over (instead of exact graph entries
   [In (ui,vi) f]) in order to support the [wt_abs] monotonicity case:
   a selection is a *join* of edges, typed at the value's domain, which
   transports across both type- and value-graph refinement.

   Agda → Coq dictionary:
     FinEl                 elt
     FinFun                list (elt * elt)
     Bot / Sup u v         bot / lub u v
     Comp u v              compatible u v
     Coherent u            valid u
     CoherentFun(Tail)     valid_fun
     FinMem a b            wt a b           (semantic membership = typing)
     EvalFun f u           app f u
     LeCode / LeFunCode    le / le_fun
     FinMem-Sup-element     wt_lub
   ============================================================ *)

(* ------------------------------------------------------------
   The Selection relation.
   ------------------------------------------------------------ *)
Inductive Selection : list (elt * elt) -> elt -> elt -> Prop :=
| sel_nil  : Selection nil bot bot
| sel_skip : forall p g u v, Selection g u v -> Selection (p :: g) u v
| sel_take : forall pu pv g u v,
    compatible pu u -> compatible pv v ->
    Selection g u v ->
    Selection ((pu, pv) :: g) (lub pu u) (lub pv v).

(* The empty (skip-everything) selection of any graph yields [bot]/[bot]. *)
Lemma sel_skip_all (g : list (elt * elt)) : Selection g bot bot.
Proof. induction g as [|p g IH]; [ exact sel_nil | exact (sel_skip p IH) ]. Qed.

(* A single edge in the graph is a (singleton) selection. *)
Lemma singleton_selection (pu pv : elt) (g : list (elt * elt)) :
  In (pu, pv) g -> Selection g (lub pu bot) (lub pv bot).
Proof.
  induction g as [|p g IH]; first done.
  move=> [->|Hin].
  - apply sel_take; [ apply compatible_bot | apply compatible_bot | apply sel_skip_all ].
  - exact (sel_skip p (IH Hin)).
Qed.

(* ------------------------------------------------------------
   Coherent-Selection: the joins produced by a selection are valid.
   ------------------------------------------------------------ *)
Lemma valid_Selection (f : list (elt * elt)) u v :
  valid_fun f -> Selection f u v -> valid u /\ valid v.
Proof.
  move=> Vf S. induction S as [| p g u v S IH | pu pv g u v Ck Cv S IH ].
  - split; exact erefl.
  - destruct p as [pu0 pv0]. apply IH. exact (valid_fun_tail Vf).
  - have HD := valid_fun_head Vf.
    have [Vu Vv] := IH (valid_fun_tail Vf).
    split.
    + apply valid_lub; [ exact Ck | exact (key_valid _ _ _ HD) | exact Vu ].
    + apply valid_lub; [ exact Cv | exact (val_valid _ _ _ HD) | exact Vv ].
Qed.

(* ------------------------------------------------------------
   FinMem-Selection: if every key of [f] is in (typed at) [b], then the
   selected key-join [u] is also in [b].  ([wt_lub]-closure.)
   ------------------------------------------------------------ *)
Lemma wt_Selection (f : list (elt * elt)) u v b :
  wt b tuniv ->
  valid_fun f ->
  (forall ui vi, In (ui, vi) f -> wt ui b) ->
  Selection f u v -> wt u b.
Proof.
  move=> Hb Vf Keys S.
  induction S as [| p g u v S IH | pu pv g u v Ck Cv S IH ].
  - exact (wt_bot Hb).
  - destruct p as [pu0 pv0]. apply IH.
    + exact (valid_fun_tail Vf).
    + by move=> ui vi Hin; apply (Keys ui vi); right.
  - have Wpu : wt pu b by apply (Keys pu pv); left.
    have Wu  : wt u b.
    { apply IH; [ eapply valid_fun_tail; exact Vf
                | by move=> ui vi Hin; apply (Keys ui vi); right ]. }
    apply (wt_lub Wpu); [ exact Ck | exact Wu ].
Qed.

(* ------------------------------------------------------------
   selectionBelow: for any argument [x], the edges of [f] with key
   below [x] form a selection whose key-join is [<= x] and whose
   value-join is exactly [app f x] (the function's value at [x]).

   This is the canonical selection used to turn an "arbitrary argument
   [x]" into the [Selection]-indexed edge.
   ------------------------------------------------------------ *)
Lemma selectionBelow (f : list (elt * elt)) (x : elt) :
  valid_fun f -> valid x ->
  exists u v, Selection f u v /\ le u x /\ app f x = v.
Proof.
  move=> Vf Vx.
  induction f as [|[pu pv] g IH].
  - exists bot, bot. split; [ exact sel_nil | split; [ apply le_bot' | apply app_nil_eq ] ].
  - have Vg : valid_fun g by eapply valid_fun_tail; exact Vf.
    have HD := valid_fun_head Vf.
    have [u [v [S [Le Eq]]]] := IH Vg.
    rewrite app_cons_eq.
    destruct (le pu x) eqn:Lpu.
    + (* pu <= x: take this edge *)
      have Cku : compatible pu u
        by (eapply le_compatible_pair; [ exact Vx | exact Lpu | exact Le ]).
      have Cv  : compatible pv v.
      { rewrite -Eq. eapply compatible_coherent_app;
          [ eapply le_compatible; [ exact Vx | exact Lpu ] | exact (compat _ _ _ HD) ]. }
      exists (lub pu u), (lub pv v).
      split; [ exact (sel_take Cku Cv S) | ].
      split; [ apply le_sup_lub; [ exact Lpu | exact Le ] | by rewrite Eq ].
    + (* ~ pu <= x: skip this edge *)
      exists u, v.
      split; [ exact (sel_skip (pu, pv) S) | ].
      split; [ exact Le | by rewrite Eq ].
Qed.

(* ------------------------------------------------------------
   Selection-le-EvalFun: the value-join of a selection of [f] is below
   the application [app g u] of any larger graph [g] (le_fun f g) at the
   selection's key-join.

   TODO (next milestone): this is the remaining monotonicity lemma; its
   proof needs argument-monotonicity of [app] ([le_fun_mono_arg]) and
   lub/compatibility bookkeeping along the selection.  Stated here so the
   [Selection] interface used by the value-edge restriction is complete.
   ------------------------------------------------------------ *)
Lemma Selection_le_app (f g : list (elt * elt)) u v :
  valid_fun f -> valid_fun g -> le_fun f g -> valid u ->
  Selection f u v -> le v (app g u).
Proof.
  move=> Vf Vg LE Vu S. move: Vf LE Vu.
  induction S as [| p f' u v S IH | pu0 pv0 f' u' v' Ck Cv S IH ]; move=> Vf LE Vu.
  - apply le_bot'.
  - destruct p as [pu0 pv0]. apply IH.
    + exact (valid_fun_tail Vf).
    + move: LE => /=. by move=> /andP [_ ?].
    + exact Vu.
  - have Hf  := valid_fun_head Vf.
    have Vf' := valid_fun_tail Vf.
    have Vpu0 : valid pu0 := key_valid _ _ _ Hf.
    have Vpv0 : valid pv0 := val_valid _ _ _ Hf.
    have [Vu' Vv'] := valid_Selection Vf' S.
    move: (LE) => /= /andP [LEhd LEtl].
    have Vju : valid (lub pu0 u') by (apply valid_lub; [ exact Ck | exact Vpu0 | exact Vu' ]).
    have Vgu : valid (app g (lub pu0 u')) by (apply valid_app; [ exact Vg | exact Vju ]).
    have Lpu : le pu0 (lub pu0 u') by (apply le_lub_left; [ exact Ck | exact Vpu0 | exact Vu' ]).
    have Lu' : le u' (lub pu0 u') by (apply le_lub_right; [ exact Ck | exact Vpu0 | exact Vu' ]).
    apply le_sup_lub.
    + have Vgpu0 : valid (app g pu0) by (apply valid_app; [ exact Vg | exact Vpu0 ]).
      have step : le (app g pu0) (app g (lub pu0 u'))
        by (apply le_fun_mono_arg; [ exact Vg | exact Vpu0 | exact Vju | exact Lpu ]).
      eapply le_trans; [ exact Vpv0 | exact Vgpu0 | exact Vgu | exact LEhd | exact step ].
    + have HIH : le v' (app g u') by (apply IH; [ exact Vf' | exact LEtl | exact Vu' ]).
      have Vgu' : valid (app g u') by (apply valid_app; [ exact Vg | exact Vu' ]).
      have step : le (app g u') (app g (lub pu0 u'))
        by (apply le_fun_mono_arg; [ exact Vg | exact Vu' | exact Vju | exact Lu' ]).
      eapply le_trans; [ exact Vv' | exact Vgu' | exact Vgu | exact HIH | exact step ].
Qed.
