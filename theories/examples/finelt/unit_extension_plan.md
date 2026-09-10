# `Unit` — port plan

Adds a unit type to the finelt dev: `Unit : U`, `star : Unit`, and **η**
(`M ≡ N : Unit` for any two members).  Continues the `Prop` port
(`prop_extension_plan.md`), whose machinery this reuses almost wholesale.

## The design decision, recorded

In this model these are *not* independent choices:

> **η for unit holds iff `Unit`'s only realizer is `bot`.**

Both directions matter.  If `star` gets an informative element code `tstar` —
the `zero`-at-`tnat` treatment, where `Val` at `(tstar, tunit)` carries
`HeadRed M star /\ conv Γ M star A` — then η is *not validated*: a divergent
`M : Unit` cannot satisfy `HeadRed M star`, and weakening the arm to let it
lands you back at the bot-only design.  Conversely, once `bot` is the only
realizer, η is free, because `Val`/`EqVal` at a `bot` **element** code are
already total (`Val_Bot`/`EqVal_Bot`).

**Chosen: bot-only, `Unit : U`, with η.**  The price is stated plainly: the
model cannot separate `star` from a diverging term at `Unit`.  That is exactly
what η asserts, so the theory is coherent — but `Unit` is a proof-irrelevant
type, semantically a `Prop` that happens to live in `U`.

(A variant was considered and rejected: also giving `Unit : Prop`, which would
make `c_prop` subsume the η rule and need no new conversion rule at all.  It
costs an extra case in `wt_prop_univ` and puts `Unit` in the second sort, which
is a bigger commitment than the type itself.  If it is ever wanted, the only
additions are `wt_tunit_prop : wt tunit tprop`, that `wt_prop_univ` case, and
`t_unit_prop`; the η rule can then be deleted.)

## Why it is cheap: three facts

1. **No element code.** `elt` gains only the *type* code `tunit`, a leaf like
   `tuniv`/`tnat`/`tprop`.  Nothing is added to `wt` that inhabits it, and
   `wt_bot` is the only `wt` constructor with a *variable* type index, so

       Lemma wt_unit_bot u : wt u tunit -> u = bot.
       Proof. dependent destruction h; reflexivity. Qed.

   is a one-liner — no rank recursion, unlike `wt_prop_bot`.
2. **`Val`/`EqVal` do not change.** `tunit` as a type code falls in the inert
   catch-all (`| _ => fun h => True`), and its only element is `bot`, where
   both relations are already total.  As a *element* code at `tuniv` it lands in
   `ValTy`'s catch-all, exactly like `tnat` (`| tnat => fun h1 => True`).
   Contrast the `Prop` port, where this assumption was wrong and cost 15 cases;
   here it is right, because the sort-subtyping rule `t_prop_u` has no unit
   analogue — nothing has to *reconstruct* a `Unit` type record.
3. **The mechanical pass needs no new sprinkling.** `raw_validity.v` already
   carries `try prop_only` at 108 sites.  Extend that tactic with `tunit` arms
   rather than adding a second one, and the new `wt_tunit` case is absorbed at
   every site with no textual change:

       Ltac prop_only :=
         match goal with
         | [ |- context [ tprop ] ] => solve [ prop_inert | prop_le_absurd ]
         | [ |- context [ tunit ] ] => solve [ prop_inert | unit_le_absurd ]   (* new *)
         | ...

   `unit_le_absurd` is new but is `prop_le_absurd` with `le_tunit_inv`/
   `le_tunit_inv_r` in place of the `tprop` pair; `prop_inert` is reused as is.
   The five `prop_only` sites in `adequacy.v` are covered the same way.

## The rules

    t_unit  n (Γ : Ctx n) : ctx Γ -> typing Γ tunit tuniv
    t_star  n (Γ : Ctx n) : ctx Γ -> typing Γ tstar tunit
    c_unit_eta n (Γ : Ctx n) M N :
      typing Γ M tunit -> typing Γ N tunit -> conv Γ M N tunit

`c_unit_eta` is `c_prop` specialised to `A := tunit`; its two premises are
literally the two typings `conv_typing` has to return, so that case is `eauto`.
There is **no eliminator** — nothing consumes a `Unit`, which is why no
canonical-forms lemma at `Unit` is needed for progress (see stage 8).

## Sizes

| | new constructors / rules |
| --- | --- |
| `elt` | 12 → 13 (`tunit`) |
| `wt` | 13 → 14 (`wt_tunit`) |
| `Tm` | 18 → 20 (`tunit`, `tstar`) |
| `typing` | 21 → 23 |
| `conv` | 33 → 34 |

Expect ~250 lines added, of which ~150 are the positional pattern pass.

## Stages

### 1. `findom.v` — the domain

`tunit` appended last (so the 13 positional `elt` patterns in the dev take one
more empty slot, 12 → 13, exactly as in the Σ and `Prop` passes):

    | tprop  : elt
    | tunit  : elt          (* the unit TYPE code; no element code -- see above *)

with `rk tunit = 1`; `valid` falls through to `| _ => true`; `compatible`
gains `| tunit , tunit => true`; `lub` gains `| tunit, tunit => tunit`; `le`
gains `le tunit tunit => true`; `le_inv_view` gains `| tunit => u' = tunit`.
Then the two inversion lemmas, copied from `le_tprop_inv`/`le_tprop_inv_r`:

    Lemma le_tunit_inv   u : le tunit u -> u = tunit.
    Lemma le_tunit_inv_r u : le u tunit -> u = bot \/ u = tunit.

### 2. `types.v` — membership

    | wt_tunit : wt tunit tuniv

and nothing else — that is the whole point.  Then `wt_unit_bot` (above), and
the two `WTLE` bullets copied from `wt_tuniv`'s (`wt_le`: `apply le_tuniv_inv
in LE; subst; eapply wt_tunit`; `wt_lub`: the `wt_tuniv` script).  No new
`WTLE` measure work: `tunit` is a leaf.

### 3. `syntax.sig` / `syntax.v`

    tunit : Tm
    tstar : Tm

appended, regenerated with autosubst (see [[autosubst-regeneration]]: `rm -f
syntax.v` first, and mind the binary on `PATH`).  Purely additive.

### 4. `syntax/typing.v`

The three rules, then:

* `wt_ty_tuniv`-style hint lists gain `t_unit`;
* `renaming_typing`, `substitution_tm`, `substitution_conv`: one bullet each
  for `t_unit`/`t_star` (closed formers — `eapply t_unit; eassumption`) and
  `c_unit_eta` (`eapply c_unit_eta; eauto`).  **No** guard-check hazard here:
  unlike `t_prop_u`, neither rule's conclusion matches an open goal shape, so
  the existing catch-alls stay as they are;
* `conv_typing`: `c_unit_eta` needs no bullet (its premises are the goals);
* inversion lemmas — two new, and note the `Prop` ripple applies:

      typing_unit_inv : Γ ⊢ tunit ∈ T -> Γ ⊢ tuniv ≡ T ∈ tuniv
      typing_star_inv : Γ ⊢ star ∈ T -> Γ ⊢ tunit ≡ T ∈ tuniv
                                      \/ Γ ⊢ tuniv ≡ T ∈ tuniv

  `typing_unit_inv` is single-conclusion (its principal type *is* `tuniv`, so
  `t_prop_u`'s case is `c_refl`), `typing_star_inv` is not (`star`'s principal
  type is `tunit`), exactly per `prop_extension_plan.md`'s correction 2.

### 5. `syntax/reduction.v`

Nothing.  `HeadRed1` lists redexes only, and neither `tunit` nor `tstar` is
one — both are normal forms by construction.

### 6. `raw_semantics.v`

    | Core.tunit => fun ρ b => le b tunit
    | Core.tstar => fun ρ b => le b bot

The second clause is the design decision in one line: `le b bot` is `b = bot`.
`EvalRel_bot` still holds (`le bot bot`), and the four closure lemmas
(`EvalRel_valid`, `EvalRel_mono_env`, `EvalRel_down`,
`EvalRel_compatible_lub`) plus `eval_substitution.v`'s
`EvalRel_subst_forward_wit` each gain two cases — `destruct u; try done` for
`tunit` (the `tuniv` script) and `move: (le_bot_inv _ H) => ->` for `tstar`.
This is the compiler-driven pass; the `Prop` port's script for it is in the job
notes.

### 7. `typing_semantics.v`

    Lemma InvTyped_unit_bot {n} (Γ : Ctx n) (M : Tm n) ρ :
      InvTyped Γ M Core.tunit ρ -> forall u, EvalRel M ρ u -> u = bot.

Simpler than `InvTyped_prop_bot`: the type code is *known* to be below
`tunit`, so `le_tunit_inv_r` + `wt_unit_bot` finishes it — no need to route
through the type's own `Typed` witness, and no `wt_le`.  Then

* `t_unit`: the `t_univ` case verbatim (`exists tunit, tuniv, wt_tunit`);
* `t_star`: `EvalRel star ρ u` forces `u = bot`, so `Typed_bot`;
* `c_unit_eta`: `InvConv_prop_irrel`'s script with `InvTyped_unit_bot`, i.e.
  both transfer directions are `EvalRel_bot`.

### 8. `adequacy.v`

* `st_unit` — `st_univ` verbatim; `st_star` — `u = bot`, then
  `Val_Bot`/`EqVal_Bot` (~5 lines); `sc_unit_eta` — `sc_prop`'s script with
  `InvTyped_unit_bot` (~6 lines).  Three dispatch cases in
  `adequacySub`/`adequacyEqSub`.
* Non-confusion.  Four new facts, needed by the canonical-forms lemmas'
  `v_star` cases: `tunit_not_tpi`, `tunit_not_tsig`, `tunit_not_tid` (via
  `piConv`/`sigmaConv`/`idConv` + the `HeadRed1 Core.tunit` inversion — `tunit`
  is head-normal, so these are the `tprop_not_*` scripts verbatim) and
  `tunit_not_tnat` (the semantic `bot_env` route, as `tprop_not_tnat`).  The
  `v_unit` cases need nothing new: `typing_unit_inv` lands in `tuniv`, where
  `tuniv_not_*` already applies.
* `value` gains `v_unit` and `v_star` (both appended, to keep the existing
  bullet order); `canonical_pi`/`canonical_nat`/`canonical_id`/
  `canonical_sigma` gain two bullets each — `inv_alt` kills
  `typing_star_inv`'s second alternative, then the `tunit_not_*` fact closes
  the first.
* `red1_conv`, `subject_red1`: two new pattern slots each, both closed by the
  existing `all: try solve [ inversion hr ]`.  `progress_gen`: two new
  branches, both `left; constructor`.
* `subst_conv_cross`: `t_unit`/`t_star` are closed, so `cbn; apply c_refl;
  apply t_unit` (resp. `t_star`).
* **Optional** `canonical_unit : value M -> typing Γ M tunit -> M = star`.
  Nothing needs it (Unit has no eliminator, so `progress` never asks), and it
  costs six more non-confusion facts of the form `~ conv Γ X tunit tuniv`, one
  per other head-normal former, each by the `bot_env` route.  Skip unless
  something downstream wants it.

## What this does *not* give

* No `Unit` eliminator, and none is needed — η makes any eliminator definable
  as a constant.
* No separation of `star` from a diverging `M : Unit`; see the design decision.
* `Unit` stays in `U`.  It is *not* a `Prop` unless the rejected variant above
  is adopted, so `c_prop` does not apply to it and the η rule carries its own
  weight.

---

# As built

Done; the whole dev compiles, no admits, no new axioms.  `Val`/`EqVal` really
did not change — the one prediction the `Prop` port got wrong is the one that
held here, and for the stated reason (no sort-subtyping rule to invert).
Deviations worth keeping:

* **The pattern pass is 147 sites, not 13.**  The estimate came from a grep
  that only matched one spacing convention.  `elt`'s 12-slot patterns were
  widened mechanically (a script that finds balanced bracket groups with
  exactly 12 top-level slots and appends one, skipping any group whose body
  contains a tactic keyword — `adequacy.v`'s `[ exact TA | … ]` has 12 branches
  too, and `syntax/reduction.v`'s `HeadRed1` list has exactly 12 constructors).
  The two `wt` patterns (13 → 14) are indistinguishable from `elt`'s new 13-slot
  ones by shape, so those went through a compiler-driven loop keyed on
  "Expects a disjunctive pattern with N branches" — the same split the `Prop`
  port needed.
* **Bullet order in the new inversion lemmas is not the `Prop` one.**
  `t_prop_u` is declared *before* `t_unit`/`t_star`, and `dependent induction`
  follows declaration order, so in `typing_unit_inv`/`typing_star_inv` the
  `t_prop_u` case comes **before** the subject's own rule.  (In
  `typing_prop_inv` it came after, because `t_prop` precedes `t_prop_u`.)
* `t_unit`/`t_star` were absorbed by the existing `econstructor` catch-alls in
  `renaming_typing`/`substitution_tm`, and `c_unit_eta` by `conv_typing`'s
  leading `eauto` — only three explicit bullets were needed there.  No
  guard-check hazard, as predicted.
* In `raw_validity.v` the extended `prop_only` absorbed ~105 of the 108 sites;
  four needed real bullets (`restrictVal_step`, `restrictEqVal_step`, and one
  `DOWN`/`DOWNe` conjunct each in `up_down_restrict`), every one of them the
  sibling `wt_tprop` script.
* `canonical_unit` was skipped, as the plan allows — nothing asks for it.

Smoke-tested off-tree (`$CLAUDE_JOB_DIR/tmp/unit_smoke.v`, not part of the
dev): the three rules are usable; `progress` applies to `star`;
`tunit_not_tnat` gives non-degeneracy (`Unit` is not `Nat`); and — the design
decision in action — `Y (λx:Unit. x) ≡ star : Unit` is derivable, i.e. a
*diverging* term is convertible to `star`.

