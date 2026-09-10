From Stdlib Require Import Relations List Program
     ssreflect ssrfun ssrbool.
From Stdlib Require Import Classes.RelationClasses 
  Classes.Morphisms Lia Arith.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Require Import findom.
Require Import types.
Require Import syntax.syntax.
Require Import syntax.typing.

Import SyntaxNotations.
Import SubstNotations.

Open Scope syntax_scope.

Import Raw.

(** * raw_semantics.v: The evaluation relation [EvalRel]

    This file defines the denotational meaning of a (well-scoped) term [Tm n]
    as a relation [EvalRel M ρ a] between a finite environment [ρ] and a finite
    element [a]: "[a] is a (finite) approximation of the value of [M] under
    [ρ]".  This is the Coq analogue of Agda's [EvalRel] / the model's ideal.

    The principal structural properties — proven by induction on the term —
    are that the set of approximations of a term is an *ideal*:
    - [EvalRel_valid]      every approximation is [valid];
    - [EvalRel_bot]        [bot] always approximates (the ideal is non-empty);
    - [EvalRel_mono_env]   monotone in the environment;
    - [EvalRel_down]       downward closed in the value;
    - [EvalRel_compatible] approximations of one term are pairwise compatible;
    - [EvalRel_sup]        closed under joins of compatible approximations;
    - [EvalRel_ideal]      the directed-closure package used downstream. *)

(* ------------------------------------------------- *)

(** ** Part 1: Finite environments *)

(** A finite environment assigns a finite element to each free variable. *)
Definition Env n := fin n -> elt.


(** ** Part 2: EvalRel *)

Notation " a ↦ b " := (singleton a b) (at level 70).

(** [EvalRel M ρ a]: the finite element [a] approximates the value of term [M]
    in environment [ρ].  For a function ([abs]/[tpi]) the table [g] is sound
    when, for *every* valid argument [u], some well-typed approximation [x <= u]
    of the argument makes the body evaluate to the recorded result [app g u].
    Defining the function case via this "well-typed approximation below [u]"
    (rather than demanding [u] itself be well-typed) is what makes
    [EvalRel_fun_compatible] and the ideal properties go through. *)
(** [Approx step k u]: [u] approximates the [k]-th Kleene approximant of a
    fixpoint, where [step p w] reads "the step function maps [p] to [w]" (one
    edge).  [Y_0 = bot] and [Y_(k+1) = g Y_k].  Recursion is structural in the
    index [k] and independent of [EvalRel]; supplying this explicit Kleene
    index at the use site is what keeps [EvalRel]'s fixpoint clause
    structurally recursive (Agda NAT [Approx]). *)
Fixpoint Approx (step : elt -> elt -> Prop) (k : nat) (u : elt) : Prop :=
  match k with
  | 0 => valid u /\ le u bot
  | S k => exists p, Approx step k p /\ step p u
  end.

(* The value recorded by a single edge is valid. *)
Lemma valid_singleton_val (a b : elt) : valid (a ↦ b) -> valid b.
Proof.
  unfold singleton. destruct (is_bot b) eqn:Hb.
  - move=> _. destruct b; done.
  - move=> H.
    move: (valid_fun_subterms_prop _ (valid_abs _ H) a b (or_introl erefl)).
    by move=> [_ Vb].
Qed.

(* Every Kleene approximant is valid, given that the step's values are. *)
Lemma Approx_valid (step : elt -> elt -> Prop) :
  (forall p w, step p w -> valid w) ->
  forall k u, Approx step k u -> valid u.
Proof.
  move=> Hs k. induction k as [ | k IH ]; move=> u H.
  - exact (proj1 H).
  - move: H => [p [_ Hst]]. exact (Hs p u Hst).
Qed.

(* One-step unfolding of [lub] on function tables. *)
Lemma lub_abs (f g : list (elt * elt)) :
  lub (abs f) (abs g) = if compatible_fun f g then abs (f ++ g) else bot.
Proof. reflexivity. Qed.

(* Constructing and inverting the validity of a single edge. *)
Lemma valid_singleton (a b : elt) : valid a -> valid b -> valid (a ↦ b).
Proof.
  move=> Va Vb. unfold singleton. destruct (is_bot b) eqn:Hb; [ done | ].
  have Nb : ~~ le b bot
    by (apply /negP => H; move: H => /le_bot_inv Eb; subst b; done).
  cbn. rewrite andbT /_valid_fun /=.
  rewrite (compatible_refl Va) (compatible_refl Vb) Va Vb Nb. done.
Qed.

Lemma valid_singleton_key (a b : elt) :
  valid (a ↦ b) -> is_bot b = false -> valid a.
Proof.
  unfold singleton. move=> H Hb. rewrite Hb in H.
  move: (valid_fun_subterms_prop _ (valid_abs _ H) a b (or_introl erefl)).
  by move=> [Va _].
Qed.

(* A single edge is monotone in the value it records. *)
Lemma le_singleton_val (p u u' : elt) :
  valid p -> valid u' -> le u' u -> le (p ↦ u') (p ↦ u).
Proof.
  move=> Vp Vu' L. unfold singleton.
  destruct (is_bot u') eqn:Hu'.
  - destruct u'; try done. all: apply le_bot'.
  - destruct (is_bot u) eqn:Hu.
    + exfalso. destruct u; try done.
      all: move: L => /le_bot_inv Eu'; subst u'; done.
    + rewrite le_abs le_fun_cons. apply /andP. split.
      * rewrite app_cons_eq app_nil_eq lub_bot_r (le_refl Vp) /=. exact L.
      * apply le_fun_nil.
Qed.

(* Kleene approximants are downward closed, given a downward-closed step. *)
Lemma Approx_down (step : elt -> elt -> Prop) :
  (forall p w w', step p w -> valid w' -> le w' w -> step p w') ->
  forall k u u', Approx step k u -> valid u' -> le u' u -> Approx step k u'.
Proof.
  move=> Hs k. induction k as [ | k IH ]; move=> u u' H Vu' L.
  - move: H => [_ Lb]. split; [ exact Vu' | ].
    move: Lb => /le_bot_inv Eu. subst u.
    move: L => /le_bot_inv Eu'. subst u'. apply le_bot'.
  - move: H => [p [Hp Hst]].
    exists p. split; [ exact Hp | exact (Hs _ _ _ Hst Vu' L) ].
Qed.

(* Join-closure of the Kleene approximants (Agda [YSup]).  Induction on the
   first index, with the second universally quantified; the [bot] approximants
   are absorbed because [lub bot x = x]. *)
Lemma Approx_sup (step : elt -> elt -> Prop)
  (Hmerge : forall p1 w1 p2 w2,
      step p1 w1 -> step p2 w2 -> is_bot w1 = false -> is_bot w2 = false ->
      compatible p1 p2 ->
      compatible w1 w2 /\ step (lub p1 p2) (lub w1 w2)) :
  forall k1 a k2 b, Approx step k1 a -> Approx step k2 b ->
    compatible a b /\ exists k, Approx step k (lub a b).
Proof.
  induction k1 as [ | k1 IH ]; move=> a k2 b HA HB.
  - move: HA => [Va La]. move: La => /le_bot_inv Ea. subst a.
    split; [ done | exists k2; rewrite lub_bot_l; exact HB ].
  - destruct (is_bot a) eqn:Ha.
    { destruct a; try done.
      split; [ done | exists k2; rewrite lub_bot_l; exact HB ]. }
    destruct (is_bot b) eqn:Hb.
    { destruct b; try done.
      split; [ apply compatible_bot | exists (S k1); rewrite lub_bot_r; exact HA ]. }
    destruct k2 as [ | k2 ].
    { exfalso. move: HB => [_ Lb]. move: Lb => /le_bot_inv Eb. subst b. done. }
    move: HA => [p1 [Hp1 Hs1]]. move: HB => [p2 [Hp2 Hs2]].
    move: (IH p1 k2 p2 Hp1 Hp2) => [Cp [kp Hkp]].
    move: (Hmerge _ _ _ _ Hs1 Hs2 Ha Hb Cp) => [Cab Hst].
    split; [ exact Cab | ].
    exists (S kp), (lub p1 p2). split; [ exact Hkp | exact Hst ].
Qed.

(* Relabelling the step along a pointwise implication (Agda [Approx-mon]). *)
Lemma Approx_mon (step step' : elt -> elt -> Prop) :
  (forall p w, step p w -> step' p w) ->
  forall k u, Approx step k u -> Approx step' k u.
Proof.
  move=> Hs k. induction k as [ | k IH ]; move=> u H.
  - exact H.
  - move: H => [p [Hp Hst]].
    exists p. split; [ exact (IH _ Hp) | exact (Hs _ _ Hst) ].
Qed.

Fixpoint EvalRel {n} (t : Tm n) : Env n -> elt -> Prop :=
  (* NOTE: this says that we can find a well-typed approximation for
     any argument u, even if u is not itself well-typed.
     This well-typed approximation contains enough information to
     evaluate the function.
     We need to define it this way instead of the more straightforward

       forall u v, wt u a -> app g u = v -> EvalRel M (u .: ρ) v

     because the naive version requires that we have a well typed finelt
     for the argument to get the evaluation of the body of the function.
     This is too restrictive to show properties like EvalRel_fun_compatible
` *)
  let EvalRel_fun {n} (M : Tm (S n)) :=
    fun ρ a g =>
      forall u v, valid u -> app g u = v ->
        exists x (h:wt x a), le x u /\ EvalRel M (x .: ρ) v
  in
  match t return Env n -> elt -> Prop with
  | Core.var i =>
      fun ρ b => valid b /\ le b (ρ i)
  | Core.tuniv => fun ρ b =>
             le b tuniv
  (* [tprop] is a code leaf, exactly like [tuniv] (Agda [RawSemanticsSigma]:
     [EvalRel Prop rho c = LeCode c PropCode]). *)
  | Core.tprop => fun ρ b =>
             le b tprop
  (* Unit: the TYPE is a code leaf like [tuniv]; its element [tstar] has NO
     informative code -- [le b bot] is [b = bot].  That single clause is the
     whole content of the design decision recorded in
     [unit_extension_plan.md]: it is what makes eta for unit hold. *)
  | Core.tunit => fun ρ b =>
             le b tunit
  | Core.tstar => fun ρ b =>
             le b bot
  | Core.tnat => fun ρ b =>
             le b tnat
  | Core.zero => fun ρ b =>
             le b zero
  | Core.succ M => fun ρ b =>
      if is_bot b then True else
         valid b /\ exists a, le b (succ a) /\ EvalRel M ρ a
  | Core.tpi A B => fun ρ b =>
        match b with
        | bot => True
        | tpi a g =>
            valid a /\ valid_fun g
            /\ EvalRel A ρ a
            /\ exists a', EvalRel A ρ a'
            /\ EvalRel_fun B ρ a' g
        | _ => False
        end
  | Core.app M N => fun ρ b =>
         if is_bot b then True else
            exists a, EvalRel M ρ (a ↦ b) /\ EvalRel N ρ a
  | Core.abs A M => fun ρ b =>
         match b with
         | bot => True

         | abs g =>
                valid_fun g /\ ~~ is_nil g
              /\ exists a (h: wt a tuniv), EvalRel A ρ a
              /\ EvalRel_fun M ρ a g

         | _ => False
         end
  | ncase M M0 M1 => fun ρ c =>
        (* caseNat semantics (Agda NAT [CaseBranch]): the scrutinee [M] takes
           some value [w], and [c] lies below the corresponding branch.
           [w = zero] selects the zero-branch [M0]; [w = succ v] selects the
           succ-branch [M1] with the predecessor [v] bound; [w = bot] forces
           [c] below [bot]. *)
        exists w, EvalRel M ρ w /\
          match w with
          | bot    => valid c /\ le c bot
          | zero   => EvalRel M0 ρ c
          | succ v => EvalRel M1 (v .: ρ) c
          | _      => False
          end
  | fix_ M => fun ρ b =>
        (* Y: the union over the Kleene index of the approximants, the step
           being single-edge application of [M] (Agda NAT [EvalRel (Y g)]). *)
        exists k, Approx (fun p w => EvalRel M ρ (p ↦ w)) k b
  | Core.tid A M0 M1 => fun ρ c =>
        (* [Id A a b] is a type former, exactly like [tpi]: it evaluates to the
           code [tid t u v] whose components evaluate [A], [a], [b]
           (Agda ID [EvalRel (Id A a b)]). *)
        match c with
        | bot => True
        | tid t u v =>
            valid (tid t u v)
            /\ EvalRel A ρ t /\ EvalRel M0 ρ u /\ EvalRel M1 ρ v
        | _ => False
        end
  | Core.rfl M => fun ρ c =>
        (* [Ref a] is a value former, like [abs]: it evaluates to the proof
           [rfl w] whose witness evaluates [a] (Agda ID [EvalRel (Ref a)]). *)
        match c with
        | bot => True
        | rfl w => EvalRel M ρ w
        | _ => False
        end
  | jcase M0 M1 M => fun ρ c =>
        (* Based J (Agda ID [EvalRel (J C d p)] / [JBranch]).  Like [ncase],
           the scrutinee [M] -- the *proof* -- takes some value [w] and [c] lies
           below the corresponding branch.  A genuine proof [rfl w'] contracts
           [jcase C d (rfl a)] to [app d a], so [c] must be recorded by the edge
           [w' ↦ c] of [d]: exactly the [app] clause.  The motive [M0] is
           irrelevant to the *value* -- it only constrains the type. *)
        exists w, EvalRel M ρ w /\
          match w with
          | bot    => valid c /\ le c bot
          | rfl w' => EvalRel M1 ρ (w' ↦ c)
          | _      => False
          end
  | Core.tsig A B => fun ρ b =>
        (* Σ mirrors [tpi] verbatim (Agda SigmaProp [EvalRel (Sigma A B)]):
           a type former evaluating to the code [tsig a g].  Agda's
           [Coherent (SigmaCode a f)] is this [valid a /\ valid_fun g], and its
           [Selection]-indexed codomain condition is our [EvalRel_fun]. *)
        match b with
        | bot => True
        | tsig a g =>
            valid a /\ valid_fun g
            /\ EvalRel A ρ a
            /\ exists a', EvalRel A ρ a'
            /\ EvalRel_fun B ρ a' g
        | _ => False
        end
  | Core.mkpair M N => fun ρ c =>
        (* [mkpair] is a value former like [abs]/[rfl]: it evaluates to the
           code [mkpair x y] whose components evaluate [M] and [N] (Agda
           [EvalRel (MkPair M N)]).  The [valid] conjunct is what carries the
           "not both [bot]" side condition of [valid (mkpair _ _)] -- the one
           place Σ is not a transcription of [tpi]. *)
        match c with
        | bot => True
        | mkpair x y => valid (mkpair x y) /\ EvalRel M ρ x /\ EvalRel N ρ y
        | _ => False
        end
  | Core.pfst M => fun ρ c =>
        (* the projections (Agda [EvalRel (Fst M)] / [EvalRel (Snd M)]): the
           result is one component of a pair code that [M] evaluates to.  Agda
           spells out one clause per code shape; they are all this clause. *)
        if is_bot c then True else exists y, EvalRel M ρ (mkpair c y)
  | Core.psnd M => fun ρ c =>
        if is_bot c then True else exists x, EvalRel M ρ (mkpair x c)
  end.


(** The soundness condition on a function table, named at top level: for every
    valid argument [u] there is a well-typed approximation [x <= u] of the
    argument under which the body [M] evaluates to the recorded result [app g u].
    This is exactly the function clause of [EvalRel] above. *)
Definition EvalRel_fun {n} (M : Tm (S n)) :=
    fun ρ a g =>
      forall u v, valid u -> app g u = v ->
        exists x (h:wt x a), le x u /\ EvalRel M (x .: ρ) v.

(* ---------------------------------------------------------------------
   Type-valued companion for the abs case (used by Lam_L1).

   Choice 1 (full refactor of EvalRel to Type) cascades through every
   downstream file (~60 Prop-only patterns to lift to iffT/* and many
   destructure patterns to update).  As a contained alternative we keep
   EvalRel in Prop and expose this In-indexed Type-valued companion.

   The Prop→Type direction (EvalRel_fun → EvalRel_funT) is where choice
   would otherwise be needed; closing it constructively requires Choice 1.
   The Type→Prop direction is trivial.  *)
Definition EvalRel_funT {n} (M : Tm (S n))
  (ρ : Env n) (a : elt) (g : list (elt * elt)) : Type :=
  forall p, In p g ->
    { z : elt & ((wt z a * (le z (fst p) = true)) *
                 EvalRel M (z .: ρ) (snd p))%type }.


(** * validity *)


Definition valid_env {n} (ρ : Env n) :=
  forall x, valid (ρ x).

Lemma valid_nil : valid_env null.
  unfold valid_env. auto_case. Qed.
Lemma valid_cons n x (ρ : Env n) 
  : valid x -> valid_env ρ -> valid_env (x .: ρ).
Proof.  move=> Vx Vr. unfold valid_env. auto_case. Qed.

Hint Resolve valid_cons: valid.

  
(** Every approximation of a term is a valid element. *)
Lemma EvalRel_valid {n} (M : Tm n) (ρ : Env n) (u : elt) :
  EvalRel M ρ u -> valid u.
Proof.
  move: ρ u.
  induction M.
  all: move=> ρ u.
  all: cbn [EvalRel].
  - auto.
  - (* abs *)
    destruct u; try done.
    move=> [Vl [Nl [a [WT [E1 _]]]]].
    cbn. apply /andP. split; eauto.
  - destruct (is_bot u) eqn:h.
    destruct u; try done.
    move=> [a [E1 E2]].
    apply IHM1 in E1.
    unfold singleton in E1.
    rewrite h in E1.
    cbn in E1.
    move: E1 => /andP.
    move=> [h1 _]. move: h1 => /andP. move=> [h1 h2].
    move: h2 => /andP. move=> [h2 _]. move: h2 => /andP. auto.
  - destruct u; try done.
  - destruct (is_bot u) eqn:h.
    destruct u; try done.
    eauto.
  - (* ncase *)
    move=> [w [_ Hb]]. destruct w; try done.
    + exact (proj1 Hb).
    + exact (IHM2 _ _ Hb).
    + exact (IHM3 _ _ Hb).
  - (* tnat *) destruct u; try done.
  - (* tpi *)
    destruct u; try done.
    move=> [Vu [Vf [WTu [E1 _]]]].
    eapply valid_tpi_intro; eauto.
  - (* tuniv *) destruct u; try done.
  - (* fix_: every Kleene approximant is valid, since each step edge records
       a valid value *)
    move=> [k HA].
    eapply Approx_valid; [ | exact HA ].
    move=> p w Hst. eapply valid_singleton_val. exact (IHM _ _ Hst).
  - (* tid: the clause records the code's validity *)
    destruct u; try done. move=> [V _]. exact V.
  - (* rfl: [valid (rfl w)] is [valid w] *)
    destruct u; try done. move=> H. cbn. exact (IHM _ _ H).
  - (* jcase: as for [ncase], but the proof branch is an [app] edge *)
    move=> [w [_ Hb]]. destruct w; try done.
    + exact (proj1 Hb).
    + eapply valid_singleton_val. exact (IHM2 _ _ Hb).
  - (* tsig: the [tpi] argument verbatim *)
    destruct u; try done.
    move=> [Vu [Vf [WTu [E1 _]]]].
    eapply valid_tsig_intro; eauto.
  - (* mkpair: the clause records the code's validity (this is where the
       "not both bot" condition is carried) *)
    destruct u; try done. move=> [V _]. exact V.
  - (* pfst: the result is the first component of a pair code *)
    destruct (is_bot u) eqn:h.
    destruct u; try done.
    move=> [y H]. exact (valid_mkpair1 _ _ (IHM _ _ H)).
  - (* psnd: ... and the second *)
    destruct (is_bot u) eqn:h.
    destruct u; try done.
    move=> [x H]. exact (valid_mkpair2 _ _ (IHM _ _ H)).
  - (* tprop: the second sort's code is a leaf, like [tuniv] *) destruct u; try done.
  - (* tunit: the unit type code, a leaf like [tuniv] *) destruct u; try done.
  - (* tstar: the unit element: [le b bot] forces [b = bot] *) destruct u; try done.
Qed.

(** * monotonicity *)

(** Pointwise extension of the information order [le] to environments. *)
Definition le_env {n} (ρ1 ρ2 : Env n) :=
  forall x, le (ρ1 x) (ρ2 x).
Lemma le_env_nil : le_env null null.
  unfold le_env. auto_case. Qed.
Lemma le_env_cons n u v (ρ1 ρ2 : Env n):
  le u v -> le_env ρ1 ρ2 -> le_env (u .: ρ1) (v .: ρ2).
Proof. move=> L1 L2. unfold le_env. auto_case. Qed.


(** [EvalRel] is monotone in the environment: enlarging [ρ] to [ρ'] preserves
    every approximation. *)
Lemma EvalRel_mono_env {n} (M : Tm n) (ρ ρ' : Env n) u :
  EvalRel M ρ u -> valid_env ρ -> valid_env ρ' -> le_env ρ ρ' -> EvalRel M ρ' u.
Proof.
  dependent induction M.
  all: cbn [EvalRel].
  all: move=> h1 V1 V2 h2.
  - (* M = x *)
    specialize (h2 f). specialize (V1 f). specialize (V2 f).
    move: h1 => [Vu h1].
    split; auto. eapply (le_trans Vu V1 V2); eauto.
  - (* M = Abs M1 M2,  *)
    destruct u ; try done.
    move: h1 => [Vl [Nl [a [WT [ER f]]]]].
    repeat split; eauto.
    exists a. repeat split; eauto.
    move=> u1 v1 Vu1 h3.
    specialize (f u1 v1 Vu1 h3).
    destruct f as [x [Lex [WT2 EM2]]].
    have Vx: valid x. eauto with valid.
    exists x. repeat split; eauto.
    eapply IHM2; eauto with valid.
    eapply le_env_cons; eauto using le_refl.
  - (* M = app M1 M2 *)
    destruct (is_bot u); try done.
    destruct h1 as [a [E1 E2]].
    exists a. split; eauto.
  - (* M = zero *)
    destruct (is_bot u); try done.
  - (* M = succ M *)
    destruct (is_bot u); try done.
    destruct h1 as [Vu [a [LE E]]].
    eapply IHM in E; eauto.
  - (* M = ncase *)
    destruct h1 as [w [EM Hb]]. exists w. split.
    + eapply IHM1; eauto.
    + destruct w as [ | | | | v | | | | | | | | ]; try contradiction.
      * exact Hb.
      * eapply IHM2; eauto.
      * have Vv : valid v := EvalRel_valid EM.
        eapply IHM3; eauto using le_env_cons, le_refl, valid_cons.
  - (* M = tnat *)
    destruct (is_bot u); try done.
  - (* M = tpi M1 M2 *)
    destruct u; try done.
    destruct h1 as [Vu [Vl [WT1 [a' [E1 h3]]]]].
    repeat split; eauto.
    exists a'.
    repeat split; eauto.
    intros u1 v1 Vu1 APP.
    specialize (h3 u1 v1 Vu1 APP).
    destruct h3 as [x [Lx [WT E2]]].
    exists x. repeat split; eauto.
    eapply IHM2; eauto with valid.
    eapply le_env_cons; eauto using le_refl.
    eapply le_refl; eauto with valid.
  - (* M = tuniv n *)
    destruct u; try done.
  - (* M = fix_: relabel the step along the environment monotonicity of [M] *)
    move: h1 => [k HA].
    exists k. eapply Approx_mon; [ | exact HA ].
    move=> p w Hst.
    eapply IHM; [ exact Hst | exact V1 | exact V2 | exact h2 ].
  - (* M = tid: componentwise *)
    destruct u; try done.
    move: h1 => [V [E1 [E2 E3]]].
    split; [ exact V | ].
    split; [ eapply IHM1; eauto | ].
    split; [ eapply IHM2; eauto | eapply IHM3; eauto ].
  - (* M = rfl *)
    destruct u; try done. eapply IHM; eauto.
  - (* M = jcase *)
    destruct h1 as [w [EM Hb]]. exists w. split.
    + eapply IHM3; eauto.
    + destruct w as [ | | | | v | | | | | | | | ]; try contradiction.
      * exact Hb.
      * eapply IHM2; eauto.
  - (* M = tsig M1 M2: the [tpi] argument verbatim *)
    destruct u; try done.
    destruct h1 as [Vu [Vl [WT1 [a' [E1 h3]]]]].
    repeat split; eauto.
    exists a'.
    repeat split; eauto.
    intros u1 v1 Vu1 APP.
    specialize (h3 u1 v1 Vu1 APP).
    destruct h3 as [x [Lx [WT E2]]].
    exists x. repeat split; eauto.
    eapply IHM2; eauto with valid.
    eapply le_env_cons; eauto using le_refl.
    eapply le_refl; eauto with valid.
  - (* M = mkpair M1 M2: componentwise, as [tid] *)
    destruct u; try done.
    move: h1 => [V [E1 E2]].
    split; [ exact V | ].
    split; [ eapply IHM1; eauto | eapply IHM2; eauto ].
  - (* M = pfst M *)
    destruct (is_bot u); try done.
    destruct h1 as [y H]. exists y. eapply IHM; eauto.
  - (* M = psnd M *)
    destruct (is_bot u); try done.
    destruct h1 as [x H]. exists x. eapply IHM; eauto.
  - (* tprop: a code leaf, like [tuniv] *)
    destruct u; try done.
  - (* tunit: the unit type code, a leaf like [tuniv] *)
    destruct u; try done.
  - (* tstar: the unit element: [le b bot] forces [b = bot] *)
    destruct u; try done.
Qed.


(** [bot] approximates every term: the ideal is always non-empty. *)
Lemma EvalRel_bot {n} (M : Tm n) (ρ : Env n) :
  EvalRel M ρ bot.
Proof.
  move: ρ. induction M; intro ρ; cbn.
  all: try solve [ split; [done | apply le_bot'] ].
  all: try solve [ apply le_bot' ].
  all: try solve [ done ].
  (* ncase *)
  - exists bot. split; [ apply IHM1 | split; [ done | apply le_bot' ] ].
  (* fix_: [bot] is the 0-th Kleene approximant *)
  - exists 0. split; [ done | apply le_bot' ].
  (* jcase: dispatch the scrutinee at [bot] *)
  - exists bot. split; [ apply IHM3 | split; [ done | apply le_bot' ] ].
Qed.

(** Downward closure: any valid element below an approximation is itself an
    approximation. *)
Lemma EvalRel_down n (M : Tm n) (ρ : Env n) u u' :
  valid_env ρ -> valid u' ->
  EvalRel M ρ u -> le u' u -> EvalRel M ρ u'.
Proof.
  move:ρ u u'.
  dependent induction M.
  all: move=> ρ u u' Vρ Vu' ER1 LE.
  all: have Vu1: valid u by eapply EvalRel_valid; eauto.
  all: cbn in ER1.
  all: cbn.

  - (* var *)
    move: ER1 => [_ LE1].
    split; eauto. eapply le_trans; eauto.

  - (* abs A M *)
    destruct u; try done.
    + (* u = bot, so u' = bot *)
      apply le_bot_inv in LE. subst u'. done.
    + (* u = abs l *)
      move: ER1 => [Vl [Nl [a [WTa [Ea h]]]]].
      destruct u' as [ | | | | | | l0 | | | | | | ]; try done.
      (* only u' = abs l0 case remains *)
      cbn in Vu'.
      have Vl0 : valid_fun l0 by move/andP : Vu' => [? _].
      have Nl0 : ~~ is_nil l0 by move/andP : Vu' => [_ ?].
      repeat split; eauto with valid.
      exists a. repeat split; eauto.
      unfold EvalRel_fun in h |- *.
      move=> u v0 Vu APP0.
      destruct (valid_app_exists Vl Vu) as [v [APP Vv]].
      rewrite le_abs in LE.
      move: (le_fun_mono Vl0 Vl LE Vu) => LEv. rewrite APP0 APP in LEv.
      destruct (h u v Vu APP) as [x [WTx [LEx ER2]]].
      exists x. exists WTx. split; auto.
      eapply (IHM2 _ v v0); eauto.
      eapply valid_cons; eauto.
      eapply wt_valid_tm; eauto.
      rewrite -APP0. eapply (@valid_app l0 u); eauto.
  - (* app M1 M2 *)
    destruct (is_bot u') eqn:Hu'.
    + (* u' = bot, trivial *)
      destruct u'; done.
    + (* u' not bot: u not bot either since le u' u and valid u' *)
      destruct (is_bot u) eqn:Hu.
      ++ (* u = bot, so u' = bot, contradiction *)
         destruct u; try done. apply le_bot_inv in LE. subst u'.
         cbn in Hu'. done.
      ++ destruct ER1 as [a [E1 E2]].
         exists a. split; eauto.
         (* le (a ↦ u') (a ↦ u): by IHM1 we descend M1 from (a↦u) to (a↦u'). *)
         have Va: valid a by eapply EvalRel_valid; eauto.
         have Vau1: valid (a ↦ u) by eapply EvalRel_valid; eauto.
         have Vau': valid (a ↦ u').
         { unfold singleton. rewrite Hu'.
           cbn.
           apply /andP; split; last by [].
           apply /andP; split. apply /andP; split.
           - cbn. apply /andP; split; last by [].
             apply /andP; split; last by [].
             apply /implyP => _. by apply compatible_refl.
           - cbn. apply /andP; split; last by [].
             apply /negP => Lub. apply le_bot_inv in Lub. subst u'. done.
           - cbn. by rewrite Va Vu'. }
         have LEau: le (a ↦ u') (a ↦ u).
         { unfold singleton. rewrite Hu' Hu. rewrite le_abs.
           rewrite le_fun_cons.
           have La: le a a by apply le_refl.
           rewrite app_cons_eq La /= lub_bot_r.
           by rewrite LE. }
         eapply IHM1; eauto.

  - (* zero *)
    have Vz: valid zero by done.
    eapply (le_trans (v := u)); eauto.

  - (* succ M *)
    destruct (is_bot u') eqn:Hu'.
    + destruct u'; done.
    + destruct (is_bot u) eqn:Hu.
      ++ destruct u; try done. apply le_bot_inv in LE. subst u'.
         cbn in Hu'. done.
      ++ destruct ER1 as [Vu0 [a [LEa Ea]]].
         have Va: valid a by eapply EvalRel_valid; eauto.
         have Vsa: valid (succ a) by cbn; rewrite Va.
         split; first by [].
         exists a. split; last by [].
         eapply (le_trans (v := u)); eauto.

  - (* ncase *)
    destruct ER1 as [w [EM Hb]]. exists w. split; [ exact EM | ].
    destruct w as [ | | | | v | | | | | | | | ]; try contradiction.
    + (* bot: branch [valid u /\ le u bot] descends to [valid u' /\ le u' bot] *)
      move: Hb => [_ Lub]. split; [ exact Vu' | ].
      have Vb : valid bot by done.
      eapply le_trans; [ exact Vu' | exact Vu1 | exact Vb | exact LE | exact Lub ].
    + (* zero: descend the zero-branch [M2] *)
      eapply IHM2; eauto.
    + (* succ v: descend the succ-branch [M3] in the extended env *)
      have Vv : valid v := EvalRel_valid EM.
      eapply IHM3; eauto using valid_cons.

  - (* tnat *)
    have Vt: valid tnat by done.
    eapply (le_trans (v := u)); eauto.

  - (* tpi A B *)

    destruct u as [ | | | | | a f | | | | | | | ]; try done.
    + (* u = bot, u' = bot *)
      apply le_bot_inv in LE. subst u'. done.
    + (* u = tpi a f *)
      destruct u' as [ | | | | | a' f' | | | | | | | ]; try done.
      (* only u' = tpi a' f' case *)
      move: ER1 => [Va [Vf [evA [a0 [evA0 body1]]]]].
      cbn in Vu'.
      move: Vu' => /andP. move=> [Va' Vf'].
      fold (valid_fun f') in Vf'.
      rewrite le_tpi in LE. move: LE => /andP. move=> [LEa LEf].

      split. apply Va'.
      split. apply Vf'.

      split. eapply (IHM1 _ a a'); eauto.
      exists a0.
      split. eauto.
      move=> u v Vu APP.
      destruct (valid_app_exists Vf Vu) as [w [APPw Vw]].
      move: (le_fun_mono Vf' Vf LEf Vu) => LEv. rewrite APP APPw in LEv.
      destruct (body1 u w Vu APPw) as [x [WTx [LEx ERx]]].
      exists x.
      split. auto.
      split. auto.
      eapply IHM2; eauto.
      eapply valid_cons. eapply wt_valid_tm. eauto. eauto.
      rewrite -APP. eapply (@valid_app f' u); eauto.
  - (* tuniv *)
    have Vt: valid tuniv by done.
    eapply (le_trans (v := u)); eauto.
  - (* fix_: the Kleene approximants are downward closed, since a single edge
       of the step function is monotone in the value it records *)
    move: ER1 => [k HA]. exists k.
    eapply Approx_down; [ | exact HA | exact Vu' | exact LE ].
    move=> q w w' Hst Vw' Lw.
    have Vsing : valid (q ↦ w) := EvalRel_valid Hst.
    destruct (is_bot w) eqn:Hw.
    + (* the edge records [bot], so [q ↦ w] is [bot] and so is [q ↦ w'] *)
      have Ew' : is_bot w' = true.
      { destruct w; try done. move: Lw => /le_bot_inv ->. done. }
      unfold singleton in Hst |- *. rewrite Hw in Hst. rewrite Ew'. exact Hst.
    + have Vq : valid q := valid_singleton_key Vsing Hw.
      eapply IHM;
        [ exact Vρ | apply valid_singleton; [ exact Vq | exact Vw' ]
        | exact Hst | apply le_singleton_val; [ exact Vq | exact Vw' | exact Lw ] ].
  - (* tid: componentwise, as for [tpi] but with no function table *)
    destruct u as [ | | | | | | | t v w | | | | | ]; try done.
    + (* u = bot, so u' = bot *)
      apply le_bot_inv in LE. subst u'. done.
    + destruct u' as [ | | | | | | | t' v' w' | | | | | ]; try done.
      move: ER1 => [_ [EA [E0 E1]]].
      autorewrite with le in LE.
      move: LE => /andP. move=> [LE12 LEw]. move: LE12 => /andP. move=> [LEt LEv].
      have Vu'c := Vu'. cbn in Vu'c.
      move: Vu'c => /andP. move=> [V12 Vw']. move: V12 => /andP. move=> [Vt' Vv'].
      split; [ exact Vu' | ].
      split; [ eapply IHM1; eauto | ].
      split; [ eapply IHM2; eauto | eapply IHM3; eauto ].
  - (* rfl: the witness descends *)
    destruct u as [ | | | | | | | | w | | | | ]; try done.
    + apply le_bot_inv in LE. subst u'. done.
    + destruct u' as [ | | | | | | | | w' | | | | ]; try done.
      autorewrite with le in LE. eapply IHM; eauto.
  - (* jcase: as for [ncase]; the proof branch is an [app] edge, which is
       monotone in the value it records *)
    destruct ER1 as [w [EM Hb]]. exists w. split; [ exact EM | ].
    destruct w as [ | | | | | | | | v | | | | ]; try contradiction.
    + move: Hb => [_ Lub]. split; [ exact Vu' | ].
      have Vb : valid bot by done.
      eapply le_trans; [ exact Vu' | exact Vu1 | exact Vb | exact LE | exact Lub ].
    + (* rfl v: shrink the edge [v ↦ u] to [v ↦ u'] *)
      have Vsing : valid (v ↦ u) := EvalRel_valid Hb.
      destruct (is_bot u) eqn:Hu.
      * have Eu' : is_bot u' = true.
        { destruct u; try done. move: LE => /le_bot_inv ->. done. }
        unfold singleton in Hb |- *. rewrite Hu in Hb. rewrite Eu'. exact Hb.
      * have Vv : valid v := valid_singleton_key Vsing Hu.
        eapply IHM2;
          [ exact Vρ | apply valid_singleton; [ exact Vv | exact Vu' ]
          | exact Hb | apply le_singleton_val; [ exact Vv | exact Vu' | exact LE ] ].
  - (* tsig A B: the [tpi] argument verbatim, with [le_sig] for [le_tpi] *)
    destruct u as [ | | | | | | | | | a f | | | ]; try done.
    + (* u = bot, u' = bot *)
      apply le_bot_inv in LE. subst u'. done.
    + destruct u' as [ | | | | | | | | | a' f' | | | ]; try done.
      move: ER1 => [Va [Vf [evA [a0 [evA0 body1]]]]].
      cbn in Vu'.
      move: Vu' => /andP. move=> [Va' Vf'].
      fold (valid_fun f') in Vf'.
      rewrite le_sig in LE. move: LE => /andP. move=> [LEa LEf].
      split. apply Va'.
      split. apply Vf'.
      split. eapply (IHM1 _ a a'); eauto.
      exists a0.
      split. eauto.
      move=> u v Vu APP.
      destruct (valid_app_exists Vf Vu) as [w [APPw Vw]].
      move: (le_fun_mono Vf' Vf LEf Vu) => LEv. rewrite APP APPw in LEv.
      destruct (body1 u w Vu APPw) as [x [WTx [LEx ERx]]].
      exists x.
      split. auto.
      split. auto.
      eapply IHM2; eauto.
      eapply valid_cons. eapply wt_valid_tm. eauto. eauto.
      rewrite -APP. eapply (@valid_app f' u); eauto.
  - (* mkpair M1 M2: componentwise, as [tid] *)
    destruct u as [ | | | | | | | | | | x y | | ]; try done.
    + apply le_bot_inv in LE. subst u'. done.
    + destruct u' as [ | | | | | | | | | | x' y' | | ]; try done.
      move: ER1 => [_ [E1 E2]].
      autorewrite with le in LE.
      move: LE => /andP. move=> [Lx Ly].
      have Vu'c := Vu'. cbn in Vu'c.
      move: Vu'c => /andP. move=> [Vxy _]. move: Vxy => /andP. move=> [Vx' Vy'].
      split; [ exact Vu' | ].
      split; [ eapply IHM1; eauto | eapply IHM2; eauto ].
  - (* pfst M: shrink the FIRST component inside the pair code.  The pair
       stays valid because [u'] is not [bot], which is what discharges the
       "not both bot" conjunct. *)
    destruct (is_bot u') eqn:Hu'.
    + destruct u'; done.
    + destruct (is_bot u) eqn:Hu.
      ++ destruct u; try done. apply le_bot_inv in LE. subst u'.
         cbn in Hu'. done.
      ++ destruct ER1 as [y H].
         have Vp : valid (mkpair u y) by (eapply EvalRel_valid; exact H).
         have Vy : valid y by (eapply valid_mkpair2; exact Vp).
         exists y.
         eapply (IHM ρ (mkpair u y) (mkpair u' y));
           [ exact Vρ
           | apply /andP; split;
               [ apply /andP; split; [ exact Vu' | exact Vy ]
               | by rewrite Hu' ]
           | exact H
           | apply le_mkpair_intro; [ exact LE | exact (le_refl Vy) ] ].
  - (* psnd M: ... and the SECOND *)
    destruct (is_bot u') eqn:Hu'.
    + destruct u'; done.
    + destruct (is_bot u) eqn:Hu.
      ++ destruct u; try done. apply le_bot_inv in LE. subst u'.
         cbn in Hu'. done.
      ++ destruct ER1 as [x H].
         have Vp : valid (mkpair x u) by (eapply EvalRel_valid; exact H).
         have Vx : valid x by (eapply valid_mkpair1; exact Vp).
         exists x.
         eapply (IHM ρ (mkpair x u) (mkpair x u'));
           [ exact Vρ
           | apply /andP; split;
               [ apply /andP; split; [ exact Vx | exact Vu' ]
               | by rewrite Hu' andbF ]
           | exact H
           | apply le_mkpair_intro; [ exact (le_refl Vx) | exact LE ] ].
  - (* tprop: a code leaf, like [tuniv] *)
    have Vt: valid tuniv by done.
    eapply (le_trans (v := u)); eauto.
  - (* tunit: the unit type code, a leaf like [tuniv] *)
    have Vt: valid tuniv by done.
    eapply (le_trans (v := u)); eauto.
  - (* tstar: the unit element: [le b bot] forces [b = bot] *)
    have Vt: valid tuniv by done.
    eapply (le_trans (v := u)); eauto.
Qed.

(** Index-preserving down-closure of the Kleene approximants of [fix_ M]
    (Agda: the [yArgVal] clauses of [NAT/Adequacy/YCore.agda], which obtain
    the same effect by case-splitting the target so that [EvalRel-down] on
    [Y gg] reduces and re-exposes the *same* index).  Using [Approx_down]
    directly is what makes the Coq version a one-liner: the existential index
    of [EvalRel (fix_ M)] is never opened, so it cannot be lost. *)
Lemma Approx_EvalRel_down {n} (M : Tm n) (ρ : Env n) :
  valid_env ρ ->
  forall k u u', Approx (fun p w => EvalRel M ρ (p ↦ w)) k u ->
    valid u' -> le u' u ->
    Approx (fun p w => EvalRel M ρ (p ↦ w)) k u'.
Proof.
  move=> Vρ. apply Approx_down.
  move=> q w w' Hst Vw' Lw.
  have Vsing : valid (q ↦ w) := EvalRel_valid Hst.
  destruct (is_bot w) eqn:Hw.
  - have Ew' : is_bot w' = true.
    { destruct w; try done. move: Lw => /le_bot_inv ->. done. }
    unfold singleton in Hst |- *. rewrite Hw in Hst. rewrite Ew'. exact Hst.
  - have Vq : valid q := valid_singleton_key Vsing Hw.
    eapply EvalRel_down;
      [ exact Vρ | apply valid_singleton; [ exact Vq | exact Vw' ]
      | exact Hst | apply le_singleton_val; [ exact Vq | exact Vw' | exact Lw ] ].
Qed.


(** The function-table half of compatibility: two sound tables [l], [l0] for
    body [M] (at domains [a], [b]) are compatible, and their concatenation is a
    sound table at the join [lub a b].  This is the key lemma motivating the
    "approximation below [u]" formulation of [EvalRel] on functions. *)
Lemma EvalRel_fun_compatible {n} (M : Tm (S n)) ρ a l b l0
  (Vρ : valid_env ρ)
  (IHM : forall (ρ : Env (S n)) (a b : elt),
      valid_env ρ -> EvalRel M ρ a -> EvalRel M ρ b -> compatible a b
 /\ forall c, lub a b = c -> EvalRel M ρ c
)
  (Cab : compatible a b)
  (Va : valid a)
  (Vl : valid_fun l)
  (h1 : EvalRel_fun M ρ a l)
  (Vb : valid b)
  (Vl0 : valid_fun l0)
  (h2 : EvalRel_fun M ρ b l0) :
  forall c, lub a b = c ->
  compatible_fun l l0 /\ EvalRel_fun M ρ c (l ++ l0).
Proof.
  move=> c LUB.
  have COMP: compatible_fun l l0.
  { unfold compatible_fun.
  apply /forallb_forall.
  move=> [u1 v1] Inl.
  apply /forallb_forall.
  move=> [u2 v2] Inl0.
  apply /implyP.
  move=> Cu.

  unfold EvalRel_fun in h1, h2.
  move: (valid_elt Vl Inl) => [Vu1 _].
  move: (valid_elt Vl0 Inl0) => [Vu2 _].
  destruct (valid_app_compatible Vl Vu1) as
    [w [APPl [Vw Cui]]].


  have Cv1w: compatible v1 w.
  { eapply (Cui _ _ Inl). rewrite compatible_refl; eauto.
    rewrite le_refl; eauto. } clear Cui.

  destruct (h1 _ _ Vu1 APPl) as [x1 [WTx1 [LEx1 ERx1]]].
  destruct (valid_app_compatible Vl0 Vu2) as
    [w0 [APPl0 [Vw0 Cui0]]].
  have Cv2w0: compatible v2 w0.
  { eapply (Cui0 _ _ Inl0). rewrite compatible_refl; eauto.
    rewrite le_refl; eauto. } clear Cui0.


  destruct (h2 _ _ Vu2 APPl0) as [x0 [WTx0 [LEx0 ERx0]]].
  have Vx1 : valid x1 by eapply wt_valid_tm; eauto.
  have Vx0 : valid x0 by eapply wt_valid_tm; eauto.

  have Cx: compatible x1 x0.
  { move: (comp_down LEx1 Cu) => C1.
      move: (compatible_sym C1) => C2.
      move: (comp_down LEx0 C2) => C3.
      eapply compatible_sym. auto. }

  have [x LUBx] : { x & lub x1 x0 = x}
    by exists (lub x1 x0).
  have LEE1: le_env (x1 .: ρ) (x .: ρ).
  { unfold le_env. auto_case. eapply le_refl. eapply Vρ.
    rewrite -LUBx. eapply le_lub_left; eauto.
  }
  have LEE0: le_env (x0 .: ρ) (x .: ρ).
  { unfold le_env. auto_case. eapply le_refl. eapply Vρ.
    rewrite -LUBx. eapply le_lub_right; eauto.
  }

  have Vx : valid x. rewrite -LUBx. eapply (@valid_lub x1 x0); eauto.
  have Vx1ρ : valid_env (x1 .: ρ). eapply valid_cons; eauto.
  have Vx0ρ : valid_env (x0 .: ρ). eapply valid_cons; eauto.
  have Vxρ : valid_env (x .: ρ). eapply valid_cons; eauto.

  move: (EvalRel_mono_env ERx1 Vx1ρ Vxρ LEE1) => hR1.
  move: (EvalRel_mono_env ERx0 Vx0ρ Vxρ LEE0) => hR0.
  have Cww0: compatible w w0.
  { eapply IHM; eauto. }

  move: (le_app Vl Vu1 Inl (le_refl Vu1)) => LEv1. rewrite APPl in LEv1.
  move: (le_app Vl0 Vu2 Inl0 (le_refl Vu2)) => LEv2. rewrite APPl0 in LEv2.

  move: (comp_down LEv1 Cww0) => C1.
  move: (comp_down LEv2 (compatible_sym C1)) => C2.
  eapply compatible_sym; eauto. }
  (* EvalRel_fun_app *)
  split. auto.
  unfold EvalRel_fun.
  move=> u v Vu APP.
  destruct (compatible_app_inv Vl Vl0 Vu COMP) as
    [v1 [v0 [APPl [APPl0 LUBv]]]].

  destruct (h1 u v1 Vu APPl) as [x1 [WTx [LEx Ex]]].
  destruct (h2 u v0 Vu APPl0) as [x0 [WTx0 [LEx0 Ex0]]].

  have Cxx0 : compatible x1 x0 by eapply le_valid_compatible_pair; eauto.

  have Vx1 : valid x1 by eapply wt_valid_tm; eauto.
  have Vx0 : valid x0 by eapply wt_valid_tm; eauto.

  have [x LUBx] : { x & lub x1 x0 = x}
    by exists (lub x1 x0).

  have LEE1: le_env (x1 .: ρ) (x .: ρ).
  { unfold le_env. auto_case. eapply le_refl. eapply Vρ.
    rewrite -LUBx. eapply le_lub_left; eauto.
  }
  have LEE0: le_env (x0 .: ρ) (x .: ρ).
  { unfold le_env. auto_case. eapply le_refl. eapply Vρ.
    rewrite -LUBx. eapply le_lub_right; eauto.
  }

  have Vx : valid x. rewrite -LUBx. eapply (@valid_lub x1 x0); eauto.
  have Vx1ρ : valid_env (x1 .: ρ). eapply valid_cons; eauto.
  have Vx0ρ : valid_env (x0 .: ρ). eapply valid_cons; eauto.
  have Vxρ : valid_env (x .: ρ). eapply valid_cons; eauto.

  move: (EvalRel_mono_env Ex Vx1ρ Vxρ LEE1) => hR1.
  move: (EvalRel_mono_env Ex0 Vx0ρ Vxρ LEE0) => hR0.

  move: (IHM _ _ _ Vxρ hR1 hR0) => [CC ih].
  specialize (ih _ LUBv).

  have WTc: wt c tuniv.
  { rewrite -LUB. eapply wt_lub. eapply (wt_ty_tuniv WTx). exact Cab. eapply (wt_ty_tuniv WTx0). }
  have WTx1c: wt x1 c.
  { eapply wt_le. exact WTx. rewrite -LUB. eapply le_lub_left; eauto.
    eapply wt_ty_tuniv; exact WTx. exact WTc.
  }
  have WTx0c: wt x0 c.
  { eapply wt_le. exact WTx0. rewrite -LUB. eapply le_lub_right; eauto.
    eapply wt_ty_tuniv; exact WTx0. exact WTc.
  }
  have WTxc: wt x c.
  { rewrite -LUBx. eapply wt_lub. exact WTx1c. exact Cxx0. exact WTx0c. }
  exists x.
  exists WTxc.
  split.
  - rewrite -LUBx. apply le_sup_lub; eauto.
  - rewrite -APP. exact ih.
Qed.



(** Core ideal property (proven by induction on [M]): any two approximations
    [a], [b] of a term are compatible, and their join is again an
    approximation.  [EvalRel_compatible] and [EvalRel_sup] are the two
    projections of this statement. *)
Lemma EvalRel_compatible_lub {n} (M : Tm n) :
  forall (ρ : Env n) (a b : elt), valid_env ρ ->
  EvalRel M ρ a -> EvalRel M ρ b ->
  compatible a b /\
    forall c, lub a b = c -> EvalRel M ρ c.
Proof.
  dependent induction M.
  all: cbn [EvalRel].
  all: move=> ρ a b Vρ.
  - (* var *) 
    split.
    + move: H => [C1 L1].
      move: H0 => [C2 L2].
      specialize (Vρ f).
      eapply (Raw.le_valid_compatible_pair Vρ); eauto. 
    + move: H => [C1 L1].
      move: H0 => [C2 L2].
      move=> c LUB. subst c.
      have Cab : compatible a b by eapply (le_compatible_pair (Vρ f)); eauto.
      split.
      eapply (@valid_lub a b); eauto.
      eapply (@le_sup_lub a b); eauto.
  - (* abs M1 M2 *)
    destruct a; try done; destruct b; try done.
    + move=> _ _. split; try done.
      move=> c LUB. cbn in LUB. inversion LUB. done.
    + move=> _ h1. split; try done.
      move=> c LUB. cbn in LUB. inversion LUB. subst. eapply h1.
    + move=> h1 _. split; try done.
      move=> c LUB. cbn in LUB. inversion LUB. subst. eapply h1.
    + move=> [Vl [Nl [a [WT1 [E1  h1]]]]].
      move=> [Vl0 [Nl0 [b [WT2 [E2  h2]]]]].
      have Va: valid a. eapply EvalRel_valid; eauto.
      have Vb: valid b. eapply EvalRel_valid; eauto.
      move: (IHM1 _ _ _ Vρ E1 E2) => [Cab h3].
      have [c LUB] : { c & lub a b = c } by exists (lub a b).
      have Vc: valid c. rewrite -LUB. eapply (@valid_lub a b); eauto.
      have WTc: wt c tuniv. rewrite -LUB. eapply (@wt_lub a tuniv WT1 b Cab WT2); eauto.
      destruct (EvalRel_fun_compatible Vρ IHM2 Cab Va Vl h1 Vb Vl0 h2 LUB)
        as [Cll0 EAPP].
      split. 
      eapply Cll0.
      move=> l' LUBl. cbn in LUBl. rewrite Cll0 in LUBl. inversion LUBl.
      repeat split.
      eapply valid_append; eauto.
      destruct l; try done.
      specialize (h3 c LUB).
      exists c. exists WTc. split.
      eapply (IHM1 ρ a b); eauto.
      eauto.
  - (* app M1 M2 *)
    rename M1 into M.
    rename M2 into N.
    destruct (is_bot a) eqn:IBa; try done;
    destruct (is_bot b) eqn:IBb; try done.
    destruct a; try done.
    destruct b; try done.
    { move=> _ _ .   split; try done. 
    move=> c h. inversion h; subst. cbn. done. } 
    { move=> _. move=> [va[Ea1 Ea2]]. 
    destruct a; try done.
    split. destruct b; done.
    move=> c h. inversion h; subst. 
    rewrite IBb. eauto.
    } 
    { move=> [va[Ea1 Ea2]] _.
    destruct b; try done.
    split. destruct a; done.
    move=> c h. rewrite lub_bot_r in h.
    inversion h; subst. 
    rewrite IBa. eauto. } 
    move=> [v1 [evM1 evN1]].
    move=> [v2 [evM2 evN2]].
    have cv1: valid v1. eapply EvalRel_valid; eauto.
    have cv2: valid v2. eapply EvalRel_valid; eauto.
    
    move: (IHM1 _ _ _ Vρ evM1 evM2) => C1.
    move: (IHM2 _ _ _ Vρ evN1 evN2) => C2.
    unfold singleton in C1.
    rewrite IBa IBb in C1.
    move: C1 => [C1 LUB1].
    cbn in C1.
    move: C1 => /andP. move=> [C1 _].
    move: C1 => /andP. move=> [C1 _].
    have COMP: compatible a b.
    { 
      move: C1 => /implyP. move=> C1.
     eapply C1. eapply C2.
    } 
    split. auto.
    
    move=> c LUBab.
    destruct (is_bot c) eqn:IBc; try done.
    destruct C2 as [C2 LUB2].
    have [vc LUBres] : { vc & lub v1 v2 = vc } by exists (lub v1 v2).
    specialize (LUB2 _ LUBres).
    have Va: valid a. { eapply EvalRel_valid in evM1.
                        unfold singleton in evM1. rewrite IBa in evM1.
                        apply valid_abs in evM1.
                        eauto with valid. } 
    have Vb: valid b. { eapply EvalRel_valid in evM2.
                        unfold singleton in evM2. rewrite IBb in evM2.
                        apply valid_abs in evM2.
                        eauto with valid. } 

    have Vc: valid c. rewrite -LUBab. eapply (@valid_lub a b); eauto.
    have Vvc: valid vc. eapply EvalRel_valid; eauto.
    have EQ: lub (abs ((v1, a) :: nil)) (abs ((v2, b) :: nil)) 
          = (abs ((v1, a) :: (v2, b) :: nil)).
    { cbn. rewrite C1. cbn. done. } 
    specialize (LUB1 _ EQ). clear EQ.
    
    have LE1: le v1 vc by (rewrite -LUBres; eapply le_lub_left; eauto).
    have LE2: le v2 vc by (rewrite -LUBres; eapply le_lub_right; eauto).
    have LES: le (vc ↦ c) (abs ((v1, a) :: (v2, b) :: nil)).
    { unfold singleton. rewrite IBc le_abs le_fun_cons.
      have APPeq : app ((v1,a)::(v2,b)::nil) vc = c.
      { rewrite !app_cons_eq.
        case: ifP => [_|H1]; last by rewrite LE1 in H1.
        case: ifP => [_|H2]; last by rewrite LE2 in H2.
        by rewrite app_nil_eq lub_bot_r LUBab. }
      rewrite APPeq. apply /andP; split; [ by apply le_refl | by [] ]. }
    have NBc : ~~ le c bot.
    { apply /negP => H. move/le_bot_inv: H => H. rewrite H /= in IBc. discriminate IBc. }
    have VS:  valid (vc ↦ c).
    { rewrite /singleton IBc /= /_valid_fun /= !Bool.andb_true_r.
      apply /andP; split.
      2: by rewrite Vvc Vc.
      apply /andP; split.
      2: exact NBc.
      apply /implyP => _. by apply compatible_refl. }

    exists vc. split.
    eapply EvalRel_down; eauto. 
    auto.

  - (* zero *)
    move=> L1 L2.
    destruct a; try done; destruct b; try done.
    all: cbn.
    all: split; auto.
    all: move=>c h; inversion h; subst; done.
  - (* succ M *)
    move=> H1 H2.
    destruct (is_bot a) eqn:IBa.
    { destruct a; try done.
      split.
      - destruct b; done.
      - move=> c LUB. rewrite lub_bot_l in LUB. inversion LUB. subst c.
        destruct (is_bot b); done. }
    destruct (is_bot b) eqn:IBb.
    { destruct b; try done.
      split.
      - destruct a; done.
      - move=> c LUB. rewrite lub_bot_r in LUB. inversion LUB. subst c.
        rewrite IBa. done. }
    move: H1 => [Va [a0 [LEa Ea0]]].
    move: H2 => [Vb [b0 [LEb Eb0]]].
    specialize (IHM ρ a0 b0 Vρ Ea0 Eb0). destruct IHM as [C0 IH0].
    destruct a; try solve [cbn in LEa; done].
    rewrite le_succ in LEa.
    destruct b; try solve [cbn in LEb; done].
    rewrite le_succ in LEb.
    split.
    + cbn. eapply comp_down_pair; eauto.
    + move=> c LUB. cbn in LUB. clear IBa IBb. subst c.
      have Cab : compatible a b by eapply comp_down_pair; eauto.
      cbn in Va, Vb.
      have Ve : valid (lub a b) by eapply (valid_lub Cab); eauto.
      have [w EQ] : { w & lub a0 b0 = w } by exists (lub a0 b0).
      specialize (IH0 _ EQ).
      have Va0 : valid a0. eapply EvalRel_valid; eauto. 
      have Vb0 : valid b0. eapply EvalRel_valid; eauto.
      move: (lub_up Va Vb Va0 Vb0 C0 LEa LEb (erefl : lub a b = lub a b) EQ) => LEw.
      cbn. split.
      by rewrite Ve.
      exists w. rewrite le_succ. split; eauto.
  - (* ncase — compatibility + lub of two case-approximations.  The scrutinee
       approximations combine via [IHM1]; the zero/zero and succ/succ branches
       via [IHM2]/[IHM3], the succ/succ case first joining the two predecessor
       environments with [EvalRel_mono_env]. *)
    move=> H1 H2.
    move: H1 => [wa [EMa Hba]].
    move: H2 => [wb [EMb Hbb]].
    move: (IHM1 _ _ _ Vρ EMa EMb) => [Cw hlubw].
    destruct wa as [ | | | | va | | | | | | | | ], wb as [ | | | | vb | | | | | | | | ];
      cbn in Hba, Hbb, Cw; try contradiction; try done.
    + (* bot, bot *)
      move: Hba => [_ La]; move: Hbb => [_ Lb].
      apply le_bot_inv in La; apply le_bot_inv in Lb; subst a b.
      split; first done.
      move=> c LUB; rewrite lub_bot_l in LUB; subst c.
      exists bot; split; [ apply EvalRel_bot | cbn; split; [ done | apply le_bot' ] ].
    + (* bot, zero *)
      move: Hba => [_ La]; apply le_bot_inv in La; subst a.
      split; first done.
      move=> c LUB; rewrite lub_bot_l in LUB; subst c.
      exists zero; split; [ exact EMb | exact Hbb ].
    + (* bot, succ *)
      move: Hba => [_ La]; apply le_bot_inv in La; subst a.
      split; first done.
      move=> c LUB; rewrite lub_bot_l in LUB; subst c.
      exists (succ vb); split; [ exact EMb | exact Hbb ].
    + (* zero, bot *)
      move: Hbb => [_ Lb]; apply le_bot_inv in Lb; subst b.
      split; first by apply compatible_bot.
      move=> c LUB; rewrite lub_bot_r in LUB; subst c.
      exists zero; split; [ exact EMa | exact Hba ].
    + (* zero, zero *)
      move: (IHM2 _ _ _ Vρ Hba Hbb) => [Cab hlub].
      split; [ exact Cab | ].
      move=> c LUB; subst c.
      exists zero; split; [ exact EMa | exact (hlub _ erefl) ].
    + (* succ, bot *)
      move: Hbb => [_ Lb]; apply le_bot_inv in Lb; subst b.
      split; first by apply compatible_bot.
      move=> c LUB; rewrite lub_bot_r in LUB; subst c.
      exists (succ va); split; [ exact EMa | exact Hba ].
    + (* succ, succ — join the two predecessor environments *)
      have Vva : valid va := EvalRel_valid EMa.
      have Vvb : valid vb := EvalRel_valid EMb.
      have Vlub : valid (lub va vb) := valid_lub Cw Vva Vvb.
      have Va' : valid_env ((lub va vb) .: ρ) := valid_cons Vlub Vρ.
      have LEρ : le_env ρ ρ by (unfold le_env; move=> x; apply le_refl; apply Vρ).
      have Ea : EvalRel M3 ((lub va vb) .: ρ) a.
      { eapply EvalRel_mono_env;
          [ exact Hba
          | apply valid_cons; [ exact Vva | exact Vρ ]
          | exact Va'
          | apply le_env_cons; [ apply le_lub_left; assumption | exact LEρ ] ]. }
      have Eb : EvalRel M3 ((lub va vb) .: ρ) b.
      { eapply EvalRel_mono_env;
          [ exact Hbb
          | apply valid_cons; [ exact Vvb | exact Vρ ]
          | exact Va'
          | apply le_env_cons; [ apply le_lub_right; assumption | exact LEρ ] ]. }
      move: (IHM3 _ _ _ Va' Ea Eb) => [Cab hlub].
      split; [ exact Cab | ].
      move=> c LUB; subst c.
      exists (succ (lub va vb)); split.
      * exact (hlubw _ erefl).
      * exact (hlub _ erefl).
  - (* tnat *)
    move=> L1 L2.
    destruct a; try done; destruct b; try done.
    all: cbn.
    all: split; auto.
    all: move=> c h; inversion h; subst c; done.
  - (* tpi A B : mirrors the abs case, plus the domain [a] ([compatible a1 a2]
       in [compatible], [lub a1 a2] in the lub of the two [tpi] values) *)
    rename M1 into A. rename M2 into B.
    destruct a; try done; destruct b; try done.
    + (* bot, bot *)
      move=> _ _. split; try done.
      move=> c LUB. cbn in LUB. inversion LUB. done.
    + (* bot, tpi *)
      move=> _ h1. split; try done.
      move=> c LUB. cbn in LUB. inversion LUB. subst. eapply h1.
    + (* tpi, bot *)
      move=> h1 _. split; try done.
      move=> c LUB. cbn in LUB. inversion LUB. subst. eapply h1.
    + (* tpi, tpi *)
      move=> [Va1 [Vg1 [EA1 [a1' [EA1' h1]]]]].
      move=> [Va2 [Vg2 [EA2 [a2' [EA2' h2]]]]].
      have Va1' : valid a1' by (eapply EvalRel_valid; eauto).
      have Va2' : valid a2' by (eapply EvalRel_valid; eauto).
      move: (IHM1 _ _ _ Vρ EA1 EA2) => [Ca1a2 h3].
      move: (IHM1 _ _ _ Vρ EA1' EA2') => [Ca1'a2' h3'].
      have [c' LUB'] : { c' & lub a1' a2' = c' } by exists (lub a1' a2').
      destruct (EvalRel_fun_compatible Vρ IHM2 Ca1'a2' Va1' Vg1 h1 Va2' Vg2 h2 LUB')
        as [Cgg EAPP].
      split.
      * cbn. apply /andP. split; [ exact Ca1a2 | exact Cgg ].
      * move=> c LUB. cbn in LUB. rewrite Cgg in LUB. cbn in LUB. subst c.
        split; [ by eapply valid_lub; eauto | ].
        split; [ by eapply valid_append; eauto | ].
        split; [ exact (h3 _ erefl) | ].
        exists c'. split; [ exact (h3' _ LUB') | exact EAPP ].
  - (* tuniv *)
    move=> L1 L2.
    destruct a; try done; destruct b; try done.
    all: cbn.
    all: split; auto.
    all: move=> c h; inversion h; subst c; done.
  - (* fix_: the Kleene approximants are join-closed.  Two single edges of the
       step function merge into one edge at the joined key and joined value,
       and that merged edge is *below* the join of the two tables -- so
       [EvalRel_down] on [M] delivers it (Agda [YSup] / [singletonSup]). *)
    move=> H1 H2.
    have HM : forall p1 w1 p2 w2,
        EvalRel M ρ (p1 ↦ w1) -> EvalRel M ρ (p2 ↦ w2) ->
        is_bot w1 = false -> is_bot w2 = false -> compatible p1 p2 ->
        compatible w1 w2 /\ EvalRel M ρ ((lub p1 p2) ↦ (lub w1 w2)).
    { move=> p1 w1 p2 w2 Hs1 Hs2 Hw1 Hw2 Cp.
      have Vs1 : valid (p1 ↦ w1) := EvalRel_valid Hs1.
      have Vs2 : valid (p2 ↦ w2) := EvalRel_valid Hs2.
      have Vp1 : valid p1 := valid_singleton_key Vs1 Hw1.
      have Vp2 : valid p2 := valid_singleton_key Vs2 Hw2.
      have Vw1 : valid w1 := valid_singleton_val Vs1.
      have Vw2 : valid w2 := valid_singleton_val Vs2.
      move: (IHM ρ _ _ Vρ Hs1 Hs2) => [Cs Hlub].
      have Cf : compatible_fun ((p1,w1) :: nil) ((p2,w2) :: nil).
      { move: Cs. unfold singleton. rewrite Hw1 Hw2. by cbn. }
      have Cw : compatible w1 w2.
      { move: Cf. cbn. move=> H.
        move: H => /andP. move=> [H _]. move: H => /andP. move=> [H _].
        move: H => /implyP. move=> H. exact (H Cp). }
      split; [ exact Cw | ].
      have Vlp : valid (lub p1 p2) := valid_lub Cp Vp1 Vp2.
      have Vlw : valid (lub w1 w2) := valid_lub Cw Vw1 Vw2.
      have Nlw : is_bot (lub w1 w2) = false.
      { destruct (lub w1 w2) eqn:E; try done.
        exfalso. move: (lub_bot_inv _ _ Cw E) => [E1 _]. subst w1. done. }
      have Big : EvalRel M ρ (abs ((p1,w1) :: (p2,w2) :: nil)).
      { move: (Hlub _ erefl). unfold singleton. rewrite Hw1 Hw2.
        rewrite lub_abs Cf. by cbn. }
      eapply EvalRel_down;
        [ exact Vρ
        | apply valid_singleton; [ exact Vlp | exact Vlw ]
        | exact Big
        | ].
      unfold singleton. rewrite Nlw.
      rewrite le_abs le_fun_cons. apply /andP. split; [ | apply le_fun_nil ].
      rewrite !app_cons_eq app_nil_eq lub_bot_r.
      rewrite (le_lub_left Cp Vp1 Vp2) (le_lub_right Cp Vp1 Vp2) /=.
      apply le_refl; exact Vlw. }
    move: H1 => [k1 HA]. move: H2 => [k2 HB].
    move: (Approx_sup HM HA HB) => [Cab [k Hk]].
    split; [ exact Cab | ].
    move=> c LUB. subst c. exists k. exact Hk.
  - (* tid: componentwise, like [tpi] but with no function table *)
    move=> H1 H2.
    destruct a as [ | | | | | | | ta ua wa | | | | | ]; try done;
      destruct b as [ | | | | | | | tb ub wb | | | | | ]; try done.
    + split; [ done | move=> c LUB; cbn in LUB; subst c; done ].
    + split; [ done | move=> c LUB; rewrite lub_bot_l in LUB; subst c; exact H2 ].
    + split; [ apply compatible_bot
             | move=> c LUB; rewrite lub_bot_r in LUB; subst c; exact H1 ].
    + move: H1 => [Va [EA1 [E01 E11]]].
      move: H2 => [Vb [EA2 [E02 E12]]].
      move: (IHM1 _ _ _ Vρ EA1 EA2) => [Ct hlt].
      move: (IHM2 _ _ _ Vρ E01 E02) => [Cu hlu].
      move: (IHM3 _ _ _ Vρ E11 E12) => [Cw hlw].
      have Vac := Va. cbn in Vac.
      move: Vac => /andP. move=> [V12a Vwa]. move: V12a => /andP. move=> [Vta Vua].
      have Vbc := Vb. cbn in Vbc.
      move: Vbc => /andP. move=> [V12b Vwb]. move: V12b => /andP. move=> [Vtb Vub].
      split.
      * cbn. apply /andP. split; [ apply /andP; split | ];
          [ exact Ct | exact Cu | exact Cw ].
      * move=> c LUB. cbn in LUB. subst c.
        split.
        { cbn. apply /andP. split; [ apply /andP; split | ].
          - eapply valid_lub; [ exact Ct | exact Vta | exact Vtb ].
          - eapply valid_lub; [ exact Cu | exact Vua | exact Vub ].
          - eapply valid_lub; [ exact Cw | exact Vwa | exact Vwb ]. }
        split; [ exact (hlt _ erefl) | ].
        split; [ exact (hlu _ erefl) | exact (hlw _ erefl) ].
  - (* rfl: the witnesses join *)
    move=> H1 H2.
    destruct a as [ | | | | | | | | wa | | | | ]; try done;
      destruct b as [ | | | | | | | | wb | | | | ]; try done.
    + split; [ done | move=> c LUB; cbn in LUB; subst c; done ].
    + split; [ done | move=> c LUB; rewrite lub_bot_l in LUB; subst c; exact H2 ].
    + split; [ apply compatible_bot
             | move=> c LUB; rewrite lub_bot_r in LUB; subst c; exact H1 ].
    + move: (IHM _ _ _ Vρ H1 H2) => [Cw hlw].
      split; [ exact Cw | ].
      move=> c LUB. cbn in LUB. subst c. exact (hlw _ erefl).
  - (* jcase: like [ncase] for the scrutinee, but the proof branch is an [app]
       edge, so the two edges must be *merged* exactly as in the [fix_] case:
       [va ↦ a] and [vb ↦ b] join to [(va ⊔ vb) ↦ (a ⊔ b)], which is below the
       join of the two tables, so [EvalRel_down] on the base [M2] delivers it. *)
    move=> H1 H2.
    move: H1 => [wa [EMa Hba]].
    move: H2 => [wb [EMb Hbb]].
    move: (IHM3 _ _ _ Vρ EMa EMb) => [Cw hlubw].
    destruct wa as [ | | | | | | | | va | | | | ], wb as [ | | | | | | | | vb | | | | ];
      cbn in Hba, Hbb, Cw; try contradiction; try done.
    + (* bot, bot *)
      move: Hba => [_ La]; move: Hbb => [_ Lb].
      apply le_bot_inv in La; apply le_bot_inv in Lb; subst a b.
      split; first done.
      move=> c LUB; rewrite lub_bot_l in LUB; subst c.
      exists bot; split; [ apply EvalRel_bot | cbn; split; [ done | apply le_bot' ] ].
    + (* bot, rfl *)
      move: Hba => [_ La]; apply le_bot_inv in La; subst a.
      split; first done.
      move=> c LUB; rewrite lub_bot_l in LUB; subst c.
      exists (rfl vb); split; [ exact EMb | exact Hbb ].
    + (* rfl, bot *)
      move: Hbb => [_ Lb]; apply le_bot_inv in Lb; subst b.
      split; first by apply compatible_bot.
      move=> c LUB; rewrite lub_bot_r in LUB; subst c.
      exists (rfl va); split; [ exact EMa | exact Hba ].
    + (* rfl, rfl: merge the two edges of the base *)
      have Vsa : valid (va ↦ a) := EvalRel_valid Hba.
      have Vsb : valid (vb ↦ b) := EvalRel_valid Hbb.
      move: (IHM2 _ _ _ Vρ Hba Hbb) => [Cs Hlub].
      destruct (is_bot a) eqn:Ha.
      { (* [a] is [bot]: the join is [b] *)
        destruct a; try done.
        split; [ done | ].
        move=> c LUB; rewrite lub_bot_l in LUB; subst c.
        exists (rfl vb); split; [ exact EMb | exact Hbb ]. }
      destruct (is_bot b) eqn:Hb.
      { destruct b; try done.
        split; [ apply compatible_bot | ].
        move=> c LUB; rewrite lub_bot_r in LUB; subst c.
        exists (rfl va); split; [ exact EMa | exact Hba ]. }
      have Vva : valid va := valid_singleton_key Vsa Ha.
      have Vvb : valid vb := valid_singleton_key Vsb Hb.
      have Va : valid a := valid_singleton_val Vsa.
      have Vb : valid b := valid_singleton_val Vsb.
      have Cf : compatible_fun ((va,a) :: nil) ((vb,b) :: nil).
      { move: Cs. unfold singleton. rewrite Ha Hb. by cbn. }
      have Cab : compatible a b.
      { move: Cf. cbn. move=> H.
        move: H => /andP. move=> [H _]. move: H => /andP. move=> [H _].
        move: H => /implyP. move=> H. exact (H Cw). }
      split; [ exact Cab | ].
      move=> c LUB; subst c.
      have Vlv : valid (lub va vb) := valid_lub Cw Vva Vvb.
      have Vla : valid (lub a b) := valid_lub Cab Va Vb.
      have Nla : is_bot (lub a b) = false.
      { destruct (lub a b) eqn:E; try done.
        exfalso. move: (lub_bot_inv _ _ Cab E) => [E1 _]. subst a. done. }
      exists (rfl (lub va vb)). split; [ exact (hlubw _ erefl) | ].
      have Big : EvalRel M2 ρ (abs ((va,a) :: (vb,b) :: nil)).
      { move: (Hlub _ erefl). unfold singleton. rewrite Ha Hb.
        rewrite lub_abs Cf. by cbn. }
      eapply EvalRel_down;
        [ exact Vρ
        | apply valid_singleton; [ exact Vlv | exact Vla ]
        | exact Big
        | ].
      unfold singleton. rewrite Nla.
      rewrite le_abs le_fun_cons. apply /andP. split; [ | apply le_fun_nil ].
      rewrite !app_cons_eq app_nil_eq lub_bot_r.
      rewrite (le_lub_left Cw Vva Vvb) (le_lub_right Cw Vva Vvb) /=.
      apply le_refl; exact Vla.
  - (* tsig A B: the [tpi] case verbatim -- [compatible] and [lub] treat
       [tsig] exactly as [tpi], guard included *)
    rename M1 into A. rename M2 into B.
    destruct a; try done; destruct b; try done.
    + move=> _ _. split; try done.
      move=> c LUB. cbn in LUB. inversion LUB. done.
    + move=> _ h1. split; try done.
      move=> c LUB. cbn in LUB. inversion LUB. subst. eapply h1.
    + move=> h1 _. split; try done.
      move=> c LUB. cbn in LUB. inversion LUB. subst. eapply h1.
    + move=> [Va1 [Vg1 [EA1 [a1' [EA1' h1]]]]].
      move=> [Va2 [Vg2 [EA2 [a2' [EA2' h2]]]]].
      have Va1' : valid a1' by (eapply EvalRel_valid; eauto).
      have Va2' : valid a2' by (eapply EvalRel_valid; eauto).
      move: (IHM1 _ _ _ Vρ EA1 EA2) => [Ca1a2 h3].
      move: (IHM1 _ _ _ Vρ EA1' EA2') => [Ca1'a2' h3'].
      have [c' LUB'] : { c' & lub a1' a2' = c' } by exists (lub a1' a2').
      destruct (EvalRel_fun_compatible Vρ IHM2 Ca1'a2' Va1' Vg1 h1 Va2' Vg2 h2 LUB')
        as [Cgg EAPP].
      split.
      * cbn. apply /andP. split; [ exact Ca1a2 | exact Cgg ].
      * move=> c LUB. cbn in LUB. rewrite Cgg in LUB. cbn in LUB. subst c.
        split; [ by eapply valid_lub; eauto | ].
        split; [ by eapply valid_append; eauto | ].
        split; [ exact (h3 _ erefl) | ].
        exists c'. split; [ exact (h3' _ LUB') | exact EAPP ].
  - (* mkpair: componentwise, like [tid].  The join's "not both bot" conjunct
       is exactly [lub_pair_nonbot]. *)
    move=> H1 H2.
    destruct a as [ | | | | | | | | | | xa ya | | ]; try done;
      destruct b as [ | | | | | | | | | | xb yb | | ]; try done.
    + split; [ done | move=> c LUB; cbn in LUB; subst c; done ].
    + split; [ done | move=> c LUB; rewrite lub_bot_l in LUB; subst c; exact H2 ].
    + split; [ apply compatible_bot
             | move=> c LUB; rewrite lub_bot_r in LUB; subst c; exact H1 ].
    + move: H1 => [Va [EX1 EY1]].
      move: H2 => [Vb [EX2 EY2]].
      move: (IHM1 _ _ _ Vρ EX1 EX2) => [Cx hlx].
      move: (IHM2 _ _ _ Vρ EY1 EY2) => [Cy hly].
      have Vac := Va. cbn in Vac.
      move: Vac => /andP. move=> [Vxya NBa]. move: Vxya => /andP. move=> [Vxa Vya].
      have Vbc := Vb. cbn in Vbc.
      move: Vbc => /andP. move=> [Vxyb _]. move: Vxyb => /andP. move=> [Vxb Vyb].
      split.
      * cbn. apply /andP. split; [ exact Cx | exact Cy ].
      * move=> c LUB. cbn in LUB. subst c.
        split.
        { cbn. apply /andP. split.
          - apply /andP. split.
            + eapply valid_lub; [ exact Cx | exact Vxa | exact Vxb ].
            + eapply valid_lub; [ exact Cy | exact Vya | exact Vyb ].
          - eapply lub_pair_nonbot; [ exact Cx | exact Cy | exact NBa ]. }
        split; [ exact (hlx _ erefl) | exact (hly _ erefl) ].
  - (* pfst: the two pair codes join, and their first components join with
       them.  [compatible] of the pairs *is* the componentwise conjunction, so
       [compatible a b] falls straight out. *)
    move=> H1 H2.
    destruct (is_bot a) eqn:Ha.
    { destruct a; try done.
      split; [ done | move=> c LUB; rewrite lub_bot_l in LUB; subst c; exact H2 ]. }
    destruct (is_bot b) eqn:Hb.
    { destruct b; try done.
      split; [ apply compatible_bot
             | move=> c LUB; rewrite lub_bot_r in LUB; subst c;
               rewrite Ha; exact H1 ]. }
    move: H1 => [ya EPa]. move: H2 => [yb EPb].
    move: (IHM _ _ _ Vρ EPa EPb) => [Cp hlp].
    have Cpc := Cp. cbn in Cpc.
    have Cab : compatible a b.
    { move: Cpc => /andP. move=> [h _]. exact h. }
    split; [ exact Cab | ].
    move=> c LUB. subst c.
    have Nab : is_bot (lub a b) = false by (eapply lub_not_bot_l; eauto).
    rewrite Nab.
    have E : lub (mkpair a ya) (mkpair b yb)
             = mkpair (lub a b) (lub ya yb) by (cbn; reflexivity).
    exists (lub ya yb). exact (hlp _ E).
  - (* psnd: symmetric *)
    move=> H1 H2.
    destruct (is_bot a) eqn:Ha.
    { destruct a; try done.
      split; [ done | move=> c LUB; rewrite lub_bot_l in LUB; subst c; exact H2 ]. }
    destruct (is_bot b) eqn:Hb.
    { destruct b; try done.
      split; [ apply compatible_bot
             | move=> c LUB; rewrite lub_bot_r in LUB; subst c;
               rewrite Ha; exact H1 ]. }
    move: H1 => [xa EPa]. move: H2 => [xb EPb].
    move: (IHM _ _ _ Vρ EPa EPb) => [Cp hlp].
    have Cpc := Cp. cbn in Cpc.
    have Cab : compatible a b.
    { move: Cpc => /andP. move=> [_ h]. exact h. }
    split; [ exact Cab | ].
    move=> c LUB. subst c.
    have Nab : is_bot (lub a b) = false by (eapply lub_not_bot_l; eauto).
    rewrite Nab.
    have E : lub (mkpair xa a) (mkpair xb b)
             = mkpair (lub xa xb) (lub a b) by (cbn; reflexivity).
    exists (lub xa xb). exact (hlp _ E).
  - (* tprop: a code leaf, like [tuniv] *)
    move=> L1 L2.
    destruct a; try done; destruct b; try done.
    all: cbn.
    all: split; auto.
    all: move=> c h; inversion h; subst c; done.
  - (* tunit: the unit type code, a leaf like [tuniv] *)
    move=> L1 L2.
    destruct a; try done; destruct b; try done.
    all: cbn.
    all: split; auto.
    all: move=> c h; inversion h; subst c; done.
  - (* tstar: the unit element: [le b bot] forces [b = bot] *)
    move=> L1 L2.
    destruct a; try done; destruct b; try done.
    all: cbn.
    all: split; auto.
    all: move=> c h; inversion h; subst c; done.
Qed.

(** Any two approximations of a term are compatible. *)
Lemma EvalRel_compatible {n} (M : Tm n) :
  forall (ρ : Env n) (a b : elt), valid_env ρ ->
  EvalRel M ρ a -> EvalRel M ρ b ->
  compatible a b.
Proof.
  intros.
  eapply  EvalRel_compatible_lub; eauto.
Qed.

(** Join closure: the join of two compatible approximations is an
    approximation. *)
Lemma EvalRel_sup n (M : Tm n) (ρ : Env n) u u' v :
  valid_env ρ -> valid u -> valid u' -> compatible u u' ->
  lub u u' = v ->
  EvalRel M ρ u -> EvalRel M ρ u' -> EvalRel M ρ v.
Proof.
  intros Vr Vu Vu' C L E1 E2.
  move: (EvalRel_compatible_lub Vr E1 E2) => [_ h].
  eapply h; eauto.
Qed.


(** Extensional compatibility under a binder: evaluating a body [M] in two
    environments that differ only in a compatible head value gives compatible
    results.  (Used for the function/abs cases downstream.) *)
Lemma EvalRel_compatible_ext {n} (M : Tm (S n)) ρ x1 x2 y1 y2 :
  valid_env ρ -> compatible x1 x2 -> valid x1 -> valid x2 ->
  EvalRel M (x1 .: ρ) y1 ->
  EvalRel M (x2 .: ρ) y2 ->
  compatible y1 y2.
Proof.
  move=> Vρ CC Vx1 Vx2 E1 E2.
  have [x EQ] : { x & lub x1 x2 = x}
    by exists (lub x1 x2).
  have Vx : valid x. rewrite -EQ. eapply (valid_lub CC); eauto.
  have Vext : valid_env (x .: ρ). eauto with valid.
  have E1': EvalRel M (x .: ρ) y1.
  eapply EvalRel_mono_env; eauto with valid.
  { unfold le_env. auto_case. eapply le_refl.
    eapply Vρ. rewrite -EQ. eapply le_lub_left; eauto. }
  have E2': EvalRel M (x .: ρ) y2.
  eapply EvalRel_mono_env; eauto with valid.
  { unfold le_env. auto_case. eapply le_refl.
    eapply Vρ. rewrite -EQ. eapply le_lub_right; eauto. }

  eapply (EvalRel_compatible Vext); eauto.
Qed.  

(** Directedness package under a binder: from compatible head values [x1],[x2]
    with body results [y1],[y2], the joined head [lub x1 x2] yields the joined
    result [lub y1 y2].  This is the form consumed by the function/abs cases of
    the validity and substitution lemmas. *)
Lemma EvalRel_ideal {n} (M : Tm (S n)) ρ x1 x2 y1 y2 :
  valid_env ρ -> compatible x1 x2 -> valid x1 -> valid x2 ->
  EvalRel M (x1 .: ρ) y1 ->
  EvalRel M (x2 .: ρ) y2 ->
  exists x y, lub x1 x2 = x /\ lub y1 y2 = y
         /\ EvalRel M (x .: ρ) y.
  move=> Vρ CC Vx1 Vx2 E1 E2.
  have [x EQ] : { x & lub x1 x2 = x}
    by exists (lub x1 x2).
  have Vx : valid x. rewrite -EQ. eapply (valid_lub CC); eauto.
  have Vext : valid_env (x .: ρ). eauto with valid.
  have E1': EvalRel M (x .: ρ) y1.
  eapply EvalRel_mono_env; eauto with valid.
  { unfold le_env. auto_case. eapply le_refl.
    eapply Vρ. rewrite -EQ. eapply le_lub_left; eauto. }
  have E2': EvalRel M (x .: ρ) y2.
  eapply EvalRel_mono_env; eauto with valid.
  { unfold le_env. auto_case. eapply le_refl.
    eapply Vρ. rewrite -EQ. eapply le_lub_right; eauto. }
  have [y EQy] : { y & lub y1 y2 = y }
    by exists (lub y1 y2).
  exists x. exists y.
  repeat split; auto.
  eapply EvalRel_sup with (u := y1)(u':=y2); eauto.
  eapply EvalRel_valid; eauto.
  eapply EvalRel_valid; eauto.
  eapply EvalRel_compatible; eauto.
Qed.



