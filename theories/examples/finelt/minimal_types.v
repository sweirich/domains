(** * minimal_types.v: a minimal presentation of the typing relation [wt]

    [types.v] defines [wt u a] ("the finite element [u] inhabits the type
    [a]").  Several of its rules carry preconditions that are *admissible*:
    they follow from the remaining preconditions of the same rule, so dropping
    them does not enlarge the relation.  This file isolates the minimal set of
    preconditions as a second inductive relation [mwt] and proves

      [mwt_iff_wt : mwt u a <-> wt u a]

    so that the two are the same specification.

    ** What is admissible, and why

    1. [wt_tid]'s domain premise [wt c tuniv] is admissible: the endpoint
       premise [wt x c] already gives it, by regularity ([wt_ty_tuniv]).
       [mwt_tid] omits it outright.  (The same redundancy sits *inside*
       [wt_rfl]'s premise [wt (tid c x y) tuniv]; once [mwt_tid] is minimized
       that premise costs exactly [mwt x c] and [mwt y c], which is what is
       actually needed there.)

    2. The [valid] premises of [wt_tpi], [wt_tsig], [wt_tpi_prop], [wt_abs]
       and [wt_mkpair] are admissible *in part*.  [valid] is a conjunction, and
       exactly the conjuncts saying "every subterm is valid" are recovered from
       the typing premises via [wt_valid_tm].  What is left over is the genuine
       content: the *minimality* side conditions on the representation.

         - [valid (tpi a g)] is [valid a && valid_fun g], and [valid_fun g] is
           [compatible_fun g g && no_bot_result g && (every key/value of [g]
           valid)].  [valid a] comes from [wt a tuniv] and the last conjunct
           from the two table premises, so only [min_fun g] survives (below).
           Likewise for [tsig] and for the Prop-valued [tpi].

         - [valid (abs f)] is [valid_fun f && ~~ is_nil f]; the subterm
           conjunct comes from the table premises, so [min_fun f] and
           [~~ is_nil f] survive.

         - [valid (mkpair x y)] is
           [valid x && valid y && ~~ (is_bot x && is_bot y)]; the first two
           conjuncts come from the component premises, so only the "not both
           [bot]" condition survives.

    ** What is NOT admissible

    Every remaining precondition is load-bearing; here is a witness for each.

    - [wt_bot]'s [wt a tuniv]: without it [wt bot zero] would hold.
    - [wt_tpi]/[wt_tsig]/[wt_tpi_prop]'s [wt a tuniv]: the key premise supplies
      it only when [g] is non-empty, and [tpi a nil] is a legal (valid) code,
      so [wt (tpi zero nil) tuniv] would hold.
    - the key and value premises of every table rule: [f] and [g] are otherwise
      unconstrained.
    - [min_fun]: with [a = tnat] the table
      [g = (zero, tnat) :: (zero, tuniv) :: nil] satisfies every typing premise
      but is not self-compatible, and [g = (zero, bot) :: nil] satisfies every
      typing premise but records a [bot] result.
    - [~~ is_nil f] in [wt_abs]: for [f = nil] both table premises are vacuous.
    - the "not both bot" conjunct in [wt_mkpair]: [wt bot a] and
      [wt bot (app g bot)] are both derivable whenever [a] is a type, so
      [mkpair bot bot] would be admitted.
    - [wt_abs]'s [wt (tpi a g) tuniv]: [g] is constrained only through
      [app g ui] for the keys [ui] of [f], and [app] ignores entries whose key
      is not below the argument.  With [a = tnat], [f = (zero, zero) :: nil]
      and [g = (zero, tnat) :: (succ zero, zero) :: nil] every other premise
      holds, yet [tpi a g] is not a type (because [zero] is not).
      [wt_mkpair]'s [wt (tsig a g) tuniv] is the same situation.
    - [wt_rfl]'s [wt (tid c x y) tuniv]: with [c = tnat], [w = bot],
      [x = zero], [y = tuniv] the other three premises hold, but
      [tid tnat zero tuniv] is not a type.
    - [wt_rfl]'s [wt w c] is *not* recoverable from [le w x] and [wt x c]:
      [wt] is downward closed only among [valid] elements
      ([le (mkpair bot bot) (mkpair x y)] holds while [mkpair bot bot] is not
      valid), so trading it for [valid w] would be no simplification. *)

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

(** ** Missing [valid] introduction forms

    [findom.v] exports [valid_tpi_intro] and [valid_tsig_intro]; the other
    constructors need the same service here. *)

Lemma valid_abs_intro f :
  valid_fun f -> ~~ is_nil f -> valid (abs f).
Proof. move=> h1 h2. by apply /andP. Qed.

Lemma valid_mkpair_intro x y :
  valid x -> valid y -> ~~ (is_bot x && is_bot y) -> valid (mkpair x y).
Proof.
  move=> h1 h2 h3. apply /andP; split; last exact h3.
  apply /andP; by split.
Qed.

Lemma valid_tid_intro c x y :
  valid c -> valid x -> valid y -> valid (tid c x y).
Proof.
  move=> h1 h2 h3. apply /andP; split; last exact h3.
  apply /andP; by split.
Qed.

(** ** The minimality core of [valid_fun]

    [valid_fun f] asks for three things: that [f] be self-compatible (hence
    functional), that it record no [bot] result, and that all of its keys and
    values be [valid].  The third conjunct is what the typing premises supply,
    so [min_fun] is the remainder — and it is exactly the part of the [valid]
    premises of the table rules that is not admissible. *)
Definition min_fun (f : list (elt * elt)) : bool :=
  compatible_fun f f && no_bot_result f.

Lemma min_fun_intro f :
  compatible_fun f f -> no_bot_result f -> min_fun f.
Proof. move=> h1 h2. by apply /andP. Qed.

Lemma valid_fun_min_fun f : valid_fun f -> min_fun f.
Proof.
  move=> h.
  apply min_fun_intro;
    [ exact (@valid_fun_compatible _ h) | exact (@valid_fun_no_bot _ h) ].
Qed.

(** Conversely: [min_fun] together with validity of every key and value is
    exactly [valid_fun].  This is the lemma that makes the subterm part of the
    [valid] premises admissible. *)
Lemma min_fun_valid_fun f :
  min_fun f ->
  (forall ui vi, In (ui, vi) f -> valid ui) ->
  (forall ui vi, In (ui, vi) f -> valid vi) ->
  valid_fun f.
Proof.
  move=> /andP [C N] Hk Hv.
  rewrite /_valid_fun.
  apply /andP; split; first (apply /andP; split; assumption).
  apply /forallb_forall.
  move=> [ui vi] Hin.
  apply /andP; split; [ eapply Hk | eapply Hv ]; exact Hin.
Qed.

(** ** The minimal typing relation

    Rule for rule the same as [wt], with the admissible preconditions removed:
    [mwt_tid] has lost [wt c tuniv] entirely, and each [valid] premise has been
    replaced by its non-derivable core. *)
Inductive mwt : elt -> elt -> Prop :=
  | mwt_bot a :
    mwt a tuniv ->
    mwt bot a

  | mwt_tuniv :
    mwt tuniv tuniv

  | mwt_tnat :
    mwt tnat tuniv

  | mwt_zero :
    mwt zero tnat

  | mwt_succ u :
    mwt u tnat ->
    mwt (succ u) tnat

  (* [valid (tpi a g)] weakened to [min_fun g]: [valid a] follows from
     [mwt a tuniv], and the subterm conjunct of [valid_fun g] from the two
     table premises. *)
  | mwt_tpi a g :
    mwt a tuniv ->
    (forall ui vi, In (ui, vi) g -> mwt ui a) ->
    (forall ui vi, In (ui, vi) g -> mwt vi tuniv) ->
    min_fun g ->
    mwt (tpi a g) tuniv

  (* [valid (abs f)] weakened to [min_fun f] and [~~ is_nil f]. *)
  | mwt_abs a f g :
    (forall ui vi, In (ui, vi) f -> mwt ui a) ->
    (forall ui vi, In (ui, vi) f -> mwt vi (app g ui)) ->
    min_fun f ->
    ~~ is_nil f ->
    mwt (tpi a g) tuniv ->
    mwt (abs f) (tpi a g)

  (* [wt_tid]'s [wt c tuniv] is gone: [mwt x c] gives it by regularity. *)
  | mwt_tid c x y :
    mwt x c ->
    mwt y c ->
    mwt (tid c x y) tuniv

  | mwt_rfl w c x y :
    mwt w c ->
    le w x ->
    le w y ->
    mwt (tid c x y) tuniv ->
    mwt (rfl w) (tid c x y)

  | mwt_tsig a g :
    mwt a tuniv ->
    (forall ui vi, In (ui, vi) g -> mwt ui a) ->
    (forall ui vi, In (ui, vi) g -> mwt vi tuniv) ->
    min_fun g ->
    mwt (tsig a g) tuniv

  (* [valid (mkpair x y)] weakened to the "not both bot" side condition. *)
  | mwt_mkpair x y a g :
    mwt x a ->
    mwt y (app g x) ->
    ~~ (is_bot x && is_bot y) ->
    mwt (tsig a g) tuniv ->
    mwt (mkpair x y) (tsig a g)

  | mwt_tprop :
    mwt tprop tuniv

  | mwt_tpi_prop a g :
    mwt a tuniv ->
    (forall ui vi, In (ui, vi) g -> mwt ui a) ->
    (forall ui vi, In (ui, vi) g -> mwt vi tprop) ->
    min_fun g ->
    mwt (tpi a g) tprop

  | mwt_tunit :
    mwt tunit tuniv.

(** ** The omitted preconditions, recovered inside the minimal system

    The next two lemmas are proved by induction on [mwt] alone — they do not go
    through [wt] — and together they are the admissibility statement: each
    precondition dropped above is a consequence of the ones that were kept. *)

(** Validity of element and type at once.  This is what reconstructs the
    [valid] premises of [wt_tpi], [wt_tsig], [wt_tpi_prop], [wt_abs] and
    [wt_mkpair].  Note that the two halves must be proved *simultaneously*:
    in the [mwt_tid] case [valid c] is available only as the type half of the
    induction hypothesis for [mwt x c] — precisely because the [wt c tuniv]
    premise that used to supply it has been dropped. *)
Lemma mwt_valid u0 a0 : mwt u0 a0 -> valid u0 /\ valid a0.
Proof.
  induction 1 as
    [ a Ha IHa
    |
    |
    |
    | u Hu IHu
    | a g Ha IHa Hk IHk Hv IHv Mg
    | a f g Hk IHk Hv IHv Mf Nf Ht IHt
    | c x y Hx IHx Hy IHy
    | w c x y Hw IHw Lx Ly Ht IHt
    | a g Ha IHa Hk IHk Hv IHv Mg
    | x y a g Hx IHx Hy IHy NB Ht IHt
    |
    | a g Ha IHa Hk IHk Hv IHv Mg
    |
    ].
  - (* bot *) split; [ done | exact (proj1 IHa) ].
  - (* tuniv *) by split.
  - (* tnat *) by split.
  - (* zero *) by split.
  - (* succ *) split; [ exact (proj1 IHu) | done ].
  - (* tpi *)
    split; last done.
    apply valid_tpi_intro; first exact (proj1 IHa).
    eapply min_fun_valid_fun; first exact Mg.
    + move=> ui vi Hin. exact (proj1 (IHk ui vi Hin)).
    + move=> ui vi Hin. exact (proj1 (IHv ui vi Hin)).
  - (* abs *)
    split; last exact (proj1 IHt).
    apply valid_abs_intro; last exact Nf.
    eapply min_fun_valid_fun; first exact Mf.
    + move=> ui vi Hin. exact (proj1 (IHk ui vi Hin)).
    + move=> ui vi Hin. exact (proj1 (IHv ui vi Hin)).
  - (* tid: [valid c] is the TYPE half of the hypothesis for [mwt x c] *)
    split; last done.
    apply valid_tid_intro;
      [ exact (proj2 IHx) | exact (proj1 IHx) | exact (proj1 IHy) ].
  - (* rfl *) split; [ exact (proj1 IHw) | exact (proj1 IHt) ].
  - (* tsig *)
    split; last done.
    apply valid_tsig_intro; first exact (proj1 IHa).
    eapply min_fun_valid_fun; first exact Mg.
    + move=> ui vi Hin. exact (proj1 (IHk ui vi Hin)).
    + move=> ui vi Hin. exact (proj1 (IHv ui vi Hin)).
  - (* mkpair *)
    split; last exact (proj1 IHt).
    apply valid_mkpair_intro;
      [ exact (proj1 IHx) | exact (proj1 IHy) | exact NB ].
  - (* tprop *) by split.
  - (* tpi_prop *)
    split; last done.
    apply valid_tpi_intro; first exact (proj1 IHa).
    eapply min_fun_valid_fun; first exact Mg.
    + move=> ui vi Hin. exact (proj1 (IHk ui vi Hin)).
    + move=> ui vi Hin. exact (proj1 (IHv ui vi Hin)).
  - (* tunit *) by split.
Qed.

Definition mwt_valid_tm u a (h : mwt u a) : valid u := proj1 (mwt_valid h).
Definition mwt_valid_ty u a (h : mwt u a) : valid a := proj2 (mwt_valid h).

(** Regularity: this is [wt_tid]'s omitted [wt c tuniv] premise (instantiate at
    [mwt x c]).  It needs no validity bookkeeping at all. *)
Lemma mwt_ty_tuniv u a : mwt u a -> mwt a tuniv.
Proof.
  induction 1;
    eauto using mwt_tuniv, mwt_tnat, mwt_tprop, mwt_tunit.
Qed.

(** ** Equivalence with [wt] *)

(** The interesting direction: the dropped preconditions are rebuilt from the
    ones that were kept. *)
Lemma mwt_wt u0 a0 : mwt u0 a0 -> wt u0 a0.
Proof.
  induction 1 as
    [ a Ha IHa
    |
    |
    |
    | u Hu IHu
    | a g Ha IHa Hk IHk Hv IHv Mg
    | a f g Hk IHk Hv IHv Mf Nf Ht IHt
    | c x y Hx IHx Hy IHy
    | w c x y Hw IHw Lx Ly Ht IHt
    | a g Ha IHa Hk IHk Hv IHv Mg
    | x y a g Hx IHx Hy IHy NB Ht IHt
    |
    | a g Ha IHa Hk IHk Hv IHv Mg
    |
    ].
  - (* bot *) by apply: wt_bot.
  - (* tuniv *) by apply: wt_tuniv.
  - (* tnat *) by apply: wt_tnat.
  - (* zero *) by apply: wt_zero.
  - (* succ *) by apply: wt_succ.
  - (* tpi: rebuild [valid (tpi a g)] *)
    apply: wt_tpi; [ exact IHa | exact IHk | exact IHv | ].
    apply valid_tpi_intro; first exact (wt_valid_tm IHa).
    eapply min_fun_valid_fun; first exact Mg.
    + move=> ui vi Hin. exact (wt_valid_tm (IHk ui vi Hin)).
    + move=> ui vi Hin. exact (wt_valid_tm (IHv ui vi Hin)).
  - (* abs: rebuild [valid (abs f)] *)
    apply: wt_abs; [ exact IHk | exact IHv | | exact IHt ].
    apply valid_abs_intro; last exact Nf.
    eapply min_fun_valid_fun; first exact Mf.
    + move=> ui vi Hin. exact (wt_valid_tm (IHk ui vi Hin)).
    + move=> ui vi Hin. exact (wt_valid_tm (IHv ui vi Hin)).
  - (* tid: rebuild the omitted [wt c tuniv] by regularity *)
    apply: wt_tid; [ exact (wt_ty_tuniv IHx) | exact IHx | exact IHy ].
  - (* rfl *) by apply: wt_rfl.
  - (* tsig *)
    apply: wt_tsig; [ exact IHa | exact IHk | exact IHv | ].
    apply valid_tsig_intro; first exact (wt_valid_tm IHa).
    eapply min_fun_valid_fun; first exact Mg.
    + move=> ui vi Hin. exact (wt_valid_tm (IHk ui vi Hin)).
    + move=> ui vi Hin. exact (wt_valid_tm (IHv ui vi Hin)).
  - (* mkpair: rebuild [valid (mkpair x y)] *)
    apply: wt_mkpair; [ exact IHx | exact IHy | | exact IHt ].
    apply valid_mkpair_intro;
      [ exact (wt_valid_tm IHx) | exact (wt_valid_tm IHy) | exact NB ].
  - (* tprop *) by apply: wt_tprop.
  - (* tpi_prop *)
    apply: wt_tpi_prop; [ exact IHa | exact IHk | exact IHv | ].
    apply valid_tpi_intro; first exact (wt_valid_tm IHa).
    eapply min_fun_valid_fun; first exact Mg.
    + move=> ui vi Hin. exact (wt_valid_tm (IHk ui vi Hin)).
    + move=> ui vi Hin. exact (wt_valid_tm (IHv ui vi Hin)).
  - (* tunit *) by apply: wt_tunit.
Qed.

(** The easy direction: [mwt]'s preconditions are weaker. *)
Lemma wt_mwt u0 a0 : wt u0 a0 -> mwt u0 a0.
Proof.
  induction 1 as
    [ a Ha IHa
    |
    |
    |
    | u Hu IHu
    | a g Ha IHa Hk IHk Hv IHv Vg
    | a f g Hk IHk Hv IHv Vf Ht IHt
    | c x y Hc IHc Hx IHx Hy IHy
    | w c x y Hw IHw Lx Ly Ht IHt
    | a g Ha IHa Hk IHk Hv IHv Vg
    | x y a g Hx IHx Hy IHy Vp Ht IHt
    |
    | a g Ha IHa Hk IHk Hv IHv Vg
    |
    ].
  - (* bot *) by apply: mwt_bot.
  - (* tuniv *) by apply: mwt_tuniv.
  - (* tnat *) by apply: mwt_tnat.
  - (* zero *) by apply: mwt_zero.
  - (* succ *) by apply: mwt_succ.
  - (* tpi *)
    apply: mwt_tpi; [ exact IHa | exact IHk | exact IHv | ].
    exact (valid_fun_min_fun (@valid_tpi2 _ _ Vg)).
  - (* abs *)
    apply: mwt_abs; [ exact IHk | exact IHv | | | exact IHt ].
    + exact (valid_fun_min_fun (@valid_abs _ Vf)).
    + exact (@valid_abs_nonnil _ Vf).
  - (* tid: the [wt c tuniv] premise is simply discarded *)
    by apply: mwt_tid.
  - (* rfl *) by apply: mwt_rfl.
  - (* tsig *)
    apply: mwt_tsig; [ exact IHa | exact IHk | exact IHv | ].
    exact (valid_fun_min_fun (@valid_tsig2 _ _ Vg)).
  - (* mkpair *)
    apply: mwt_mkpair; [ exact IHx | exact IHy | | exact IHt ].
    exact (@valid_mkpair3 _ _ Vp).
  - (* tprop *) by apply: mwt_tprop.
  - (* tpi_prop *)
    apply: mwt_tpi_prop; [ exact IHa | exact IHk | exact IHv | ].
    exact (valid_fun_min_fun (@valid_tpi2 _ _ Vg)).
  - (* tunit *) by apply: mwt_tunit.
Qed.

(** The two presentations specify the same relation. *)
Theorem mwt_iff_wt u a : mwt u a <-> wt u a.
Proof. split; [ exact: mwt_wt | exact: wt_mwt ]. Qed.

(** ** Sharpness: every remaining precondition is needed

    Each group below exhibits a concrete instance in which all the *other*
    preconditions of a rule hold ([..._premises]) while the rule's conclusion
    is not derivable ([..._not_wt]).  So none of the preconditions kept in
    [mwt] can be dropped, and together with [mwt_iff_wt] that makes [mwt] a
    minimal presentation of [wt].

    All the boolean side conditions here ([min_fun], [is_nil], [le], [app])
    are decided by computation, hence the [reflexivity]s. *)
Module Sharpness.

(** Two leaves that are not types / not naturals: the engine of every
    counterexample below. *)
Lemma not_wt_zero_tuniv : ~ wt zero tuniv.
Proof. move=> h. by inversion h. Qed.

Lemma not_wt_tuniv_tnat : ~ wt tuniv tnat.
Proof. move=> h. by inversion h. Qed.

(** *** [wt_bot]'s [wt a tuniv] (the rule's only precondition) *)
Lemma sharp_wt_bot_not_wt : ~ wt bot zero.
Proof. move=> h. inversion h; subst. by apply not_wt_zero_tuniv. Qed.

(** *** [wt_tpi]'s [wt a tuniv]

    At the empty table the two table premises say nothing, so nothing else
    forces the domain to be a type. *)
Lemma sharp_wt_tpi_dom_premises :
  min_fun (@nil (elt * elt))
  /\ (forall ui vi, In (ui, vi) (@nil (elt * elt)) -> wt ui zero)
  /\ (forall ui vi, In (ui, vi) (@nil (elt * elt)) -> wt vi tuniv).
Proof. split; first reflexivity. split; move=> ui vi []. Qed.

Lemma sharp_wt_tpi_dom_not_wt : ~ wt (tpi zero nil) tuniv.
Proof.
  move=> h.
  inversion h as [| | | | | a' g' Ha' Hk' Hv' V' | | | | | | | | ]; subst.
  by apply not_wt_zero_tuniv.
Qed.

(** *** [wt_tpi]'s key premise *)
Definition g_badkey : list (elt * elt) := (tuniv, tnat) :: nil.

Lemma sharp_wt_tpi_keys_premises :
  wt tnat tuniv
  /\ (forall ui vi, In (ui, vi) g_badkey -> wt vi tuniv)
  /\ min_fun g_badkey.
Proof.
  split; first exact wt_tnat.
  split; last reflexivity.
  move=> ui vi [E|[]]. case: E => _ <-. exact wt_tnat.
Qed.

Lemma sharp_wt_tpi_keys_not_wt : ~ wt (tpi tnat g_badkey) tuniv.
Proof.
  move=> h.
  inversion h as [| | | | | a' g' Ha' Hk' Hv' V' | | | | | | | | ]; subst.
  have hz : wt tuniv tnat by (eapply Hk'; left; reflexivity).
  by apply not_wt_tuniv_tnat.
Qed.

(** *** [wt_tpi]'s value premise *)
Definition g_badval : list (elt * elt) := (zero, zero) :: nil.

Lemma sharp_wt_tpi_vals_premises :
  wt tnat tuniv
  /\ (forall ui vi, In (ui, vi) g_badval -> wt ui tnat)
  /\ min_fun g_badval.
Proof.
  split; first exact wt_tnat.
  split; last reflexivity.
  move=> ui vi [E|[]]. case: E => <- _. exact wt_zero.
Qed.

Lemma sharp_wt_tpi_vals_not_wt : ~ wt (tpi tnat g_badval) tuniv.
Proof.
  move=> h.
  inversion h as [| | | | | a' g' Ha' Hk' Hv' V' | | | | | | | | ]; subst.
  have hz : wt zero tuniv by (eapply Hv'; left; reflexivity).
  by apply not_wt_zero_tuniv.
Qed.

(** *** [min_fun], self-compatibility half

    Two entries with the same key and incompatible values: every typing
    premise holds, but the table is not functional. *)
Definition g_incoh : list (elt * elt) := (zero, tnat) :: (zero, tuniv) :: nil.

Lemma g_incoh_not_min : min_fun g_incoh = false.
Proof. reflexivity. Qed.

Lemma sharp_min_fun_compat_premises :
  wt tnat tuniv
  /\ (forall ui vi, In (ui, vi) g_incoh -> wt ui tnat)
  /\ (forall ui vi, In (ui, vi) g_incoh -> wt vi tuniv).
Proof.
  split; first exact wt_tnat.
  split.
  - move=> ui vi [E|[E|[]]]; case: E => <- _; exact wt_zero.
  - move=> ui vi [E|[E|[]]]; case: E => _ <-; [ exact wt_tnat | exact wt_tuniv ].
Qed.

Lemma sharp_min_fun_compat_not_wt : ~ wt (tpi tnat g_incoh) tuniv.
Proof.
  move=> h.
  move: (valid_fun_min_fun (@valid_tpi2 _ _ (@wt_valid_tm _ _ h))).
  by rewrite g_incoh_not_min.
Qed.

(** *** [min_fun], no-[bot]-result half

    A [bot] value is well typed at every type, so only minimality rules it
    out of a table. *)
Definition g_botres : list (elt * elt) := (zero, bot) :: nil.

Lemma g_botres_not_min : min_fun g_botres = false.
Proof. reflexivity. Qed.

Lemma sharp_min_fun_nbot_premises :
  wt tnat tuniv
  /\ (forall ui vi, In (ui, vi) g_botres -> wt ui tnat)
  /\ (forall ui vi, In (ui, vi) g_botres -> wt vi tuniv).
Proof.
  split; first exact wt_tnat.
  split.
  - move=> ui vi [E|[]]. case: E => <- _. exact wt_zero.
  - move=> ui vi [E|[]]. case: E => _ <-. by apply wt_bot, wt_tuniv.
Qed.

Lemma sharp_min_fun_nbot_not_wt : ~ wt (tpi tnat g_botres) tuniv.
Proof.
  move=> h.
  move: (valid_fun_min_fun (@valid_tpi2 _ _ (@wt_valid_tm _ _ h))).
  by rewrite g_botres_not_min.
Qed.

(** *** [wt_abs]'s [~~ is_nil f]

    Both table premises are vacuous at [f = nil], for every type whatever. *)
Lemma sharp_wt_abs_nonnil_premises a g :
  (forall ui vi, In (ui, vi) (@nil (elt * elt)) -> wt ui a)
  /\ (forall ui vi, In (ui, vi) (@nil (elt * elt)) -> wt vi (app g ui))
  /\ min_fun (@nil (elt * elt)).
Proof. split; last (split; last reflexivity); move=> ui vi []. Qed.

Lemma sharp_wt_abs_nonnil_not_wt a : ~ wt (abs nil) a.
Proof. move=> h. by move: (@wt_valid_tm _ _ h). Qed.

(** *** [wt_mkpair]'s "not both bot"

    [bot] inhabits every type, so both component premises hold for
    [mkpair bot bot] as soon as the Sigma code is well formed. *)
Lemma sharp_wt_mkpair_nonbot_premises a g :
  wt (tsig a g) tuniv -> wt bot a /\ wt bot (app g bot).
Proof.
  move=> Ht. split; first by apply wt_bot, (@wt_tsig_dom _ _ Ht).
  apply wt_bot.
  apply (@all_app_is_tuniv a g (@wt_tsig_tpi _ _ Ht)).
  reflexivity.
Qed.

Lemma sharp_wt_mkpair_nonbot_not_wt a : ~ wt (mkpair bot bot) a.
Proof. move=> h. by move: (@wt_valid_tm _ _ h). Qed.

(** *** [wt_abs]'s and [wt_mkpair]'s "the type is a type" premise

    [app g ui] only sees the entries of [g] whose key is [le] the argument, so
    a table can be ill-formed at an entry that the element never reaches.
    Here [g_eg]'s second entry has a non-type value, and [succ zero] is not
    below [f_eg]'s only key [zero]. *)
Definition f_eg : list (elt * elt) := (zero, zero) :: nil.
Definition g_eg : list (elt * elt) := (zero, tnat) :: (succ zero, zero) :: nil.

Lemma app_g_eg_zero : app g_eg zero = tnat.
Proof. reflexivity. Qed.

Lemma sharp_wt_abs_ty_premises :
  (forall ui vi, In (ui, vi) f_eg -> wt ui tnat)
  /\ (forall ui vi, In (ui, vi) f_eg -> wt vi (app g_eg ui))
  /\ min_fun f_eg /\ ~~ is_nil f_eg.
Proof.
  split; first (move=> ui vi [E|[]]; case: E => <- _; exact wt_zero).
  split; first (move=> ui vi [E|[]]; case: E => <- <-; exact wt_zero).
  by split.
Qed.

Lemma sharp_tpi_g_eg_not_wt : ~ wt (tpi tnat g_eg) tuniv.
Proof.
  move=> h.
  inversion h as [| | | | | a' g' Ha' Hk' Hv' V' | | | | | | | | ]; subst.
  have hz : wt zero tuniv by (eapply Hv'; right; left; reflexivity).
  by apply not_wt_zero_tuniv.
Qed.

Lemma sharp_wt_abs_ty_not_wt : ~ wt (abs f_eg) (tpi tnat g_eg).
Proof.
  move=> h. by apply sharp_tpi_g_eg_not_wt, (@wt_abs_ty _ _ _ h).
Qed.

Lemma sharp_wt_mkpair_ty_premises :
  wt zero tnat /\ wt zero (app g_eg zero) /\ ~~ (is_bot zero && is_bot zero).
Proof.
  split; first exact wt_zero.
  split; last reflexivity.
  exact wt_zero.
Qed.

Lemma sharp_wt_mkpair_ty_not_wt : ~ wt (mkpair zero zero) (tsig tnat g_eg).
Proof.
  move=> h.
  by apply sharp_tpi_g_eg_not_wt,
     (@wt_tsig_tpi _ _ (@wt_mkpair_ty _ _ _ _ h)).
Qed.

(** *** [wt_rfl]'s "the type is a type" premise

    [bot] sits below everything, so the witness premises are free; only the
    type premise rules out bogus endpoints. *)
Lemma sharp_wt_rfl_ty_premises :
  wt bot tnat /\ le bot zero /\ le bot tuniv.
Proof.
  split; first by apply wt_bot, wt_tnat.
  split; apply le_bot'.
Qed.

Lemma sharp_tid_not_wt : ~ wt (tid tnat zero tuniv) tuniv.
Proof. move=> h. by apply not_wt_tuniv_tnat, (@wt_tid_rhs _ _ _ h). Qed.

Lemma sharp_wt_rfl_ty_not_wt : ~ wt (rfl bot) (tid tnat zero tuniv).
Proof. move=> h. by apply sharp_tid_not_wt, (@wt_rfl_ty _ _ _ _ h). Qed.

End Sharpness.
