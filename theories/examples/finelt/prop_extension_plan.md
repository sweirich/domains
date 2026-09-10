# `Prop` (Agda `SigmaProp/`) — port plan

Adds the second sort `Prop` to the finelt dev: `Prop : U`, `Prop`-to-`U`
subtyping, Π-into-`Prop`, and **proof irrelevance**.  Continues the Σ port
(`sigma_extension_plan.md`), which deliberately deferred this.

## The headline finding: proof irrelevance is *free*

`sigma_extension_plan.md`'s "Why `Prop` is deferred" says

> `conv-Prop` is full proof irrelevance … That changes `Val`/`EqVal` at
> *every* code rather than adding an arm.

**That is wrong**, and reading the Agda settles it.  The mechanism is entirely
at the level of *codes*:

    FinMem-Prop-Bot : FinMem u a -> FinMem a PropCode -> u ≡ Bot
                        (PaperSemanticsSigma.agda:3061)

A type in `Prop` has **only `bot` as a member**.  So for `M, N : A` with
`A : Prop`, the realizer of `M` at the code of `A` is forced to `bot`, and
`Val`/`EqVal` at a `bot` *element* code is already total — `Val_Bot` /
`EqVal_Bot`, both of which the dev has had since the beginning.  Agda's
`adequacyEqSub2 (conv-Prop …)` (`Adequacy5.agda:892-985`) is exactly this: for
each code shape, either the shape is impossible or the code collapses to `Bot`
and the answer is `tt`.

**Consequence: `Val`/`EqVal` do not change at all.**  `tprop` gets a `True`
arm as a type code, like `tnat`, and the whole content of proof irrelevance is
one code-level lemma in `types.v`.

The one non-trivial corner of that lemma is `abs` at a Π-into-`Prop`
(`FinMem-Prop-Bot-FunEl`, `PaperSemanticsSigma.agda:3108`): if every edge value
of the type's graph is a member of `tprop`, every edge value is `bot`, so a
*valid* (hence non-nil, information-carrying) function value cannot inhabit it.
The case is therefore vacuous rather than collapsing.

Σ needs none of this — `FinMem (SigmaCode a f) PropCode = Empty`, i.e. a Σ type
is never a `Prop` — which is why the two ports split cleanly.

## The one real ripple: sort inversion

`t_prop_u` (`A : Prop ⟹ A : U`) is a second non-syntax-directed rule alongside
`t_conv`, and `t_tpi_prop` makes `typing Γ (tpi A B) tprop` derivable.  So the
`typing_*_inv` family in `syntax/typing.v` — which currently concludes
`Γ ⊢ <natural type> ≡ T ∈ tuniv` — must offer the second sort as an
alternative:

    typing_nat_inv : Γ ⊢ tnat ∈ T -> Γ ⊢ tuniv ≡ T ∈ tuniv
                                   \/ Γ ⊢ tuniv ≡ tprop ∈ tuniv

The disjunction is stable under both rules, which is what makes it work:

| rule | case |
| --- | --- |
| the subject's own rule | left disjunct, `c_refl` |
| `t_conv` | `c_trans` onto the left disjunct; the right one is about `tprop`, so it passes through unchanged |
| `t_prop_u` | its conclusion type is *literally* `tuniv`, and its premise's IH is about `tprop` — so take the right disjunct |

Each downstream user then discharges the extra disjunct with a **semantic**
non-confusion fact (`tuniv_not_tprop`, `tpi_not_tprop`, …), proved the way
`tuniv_not_tnat` already is: evaluate at `bot_env` and observe the codes are
incomparable.  Those live in `adequacy.v`, after adequacy, which is where the
existing non-confusion facts live too.

## Stages

1. **`findom.v`** — `elt` gains `tprop` (a leaf, `rk tprop = 1`, like
   `tuniv`), with its `valid`/`le`/`compatible`/`lub` clauses and the
   `le`-inversion characterisation.  Appended last, so the ~100 positional
   `destruct`/`inversion` patterns downstream take one more empty slot
   (11 → 12), exactly as in the Σ port.
2. **`types.v`** — `wt` gains `wt_tprop : wt tprop tuniv` and
   `wt_tpi_prop`, the `tpi` rule with its codomain memberships at `tprop`
   instead of `tuniv`.  Then the two `WTLE` measures, and the payload lemma
   **`wt_prop_bot : wt u a -> wt a tprop -> u = bot`**.
3. **`syntax.sig` / `syntax.v`** — `Tm` gains `tprop` (18 constructors),
   regenerated (see [[autosubst-regeneration]]).
4. **`syntax/typing.v`** — `t_prop`, `t_prop_u`, `t_tpi_prop`; `c_prop`
   (irrelevance), `c_prop_u`, `c_tpi_prop`; the renaming/substitution/
   `conv_typing` cases; and the sort-inversion rework above.
5. **`syntax/reduction.v`** — `tprop` is a normal form; no new reductions.
6. **`raw_semantics.v`** — `EvalRel Core.tprop ρ c := le c tprop`, like
   `tuniv`; the closure lemmas' new case.
7. **`typing_semantics.v`** — `InvTyp_*` / `InvConv_*` for the six rules.
8. **`raw_validity.v`** — `tprop` is inert in `Val`/`EqVal`/`ValTy`/`EqValTy`
   (a `True` arm), so this stage is the mechanical pattern pass plus the
   `sigma_inert`-style tactic.
9. **`adequacy.v`** — six dispatch cases; `sc_prop` is where `wt_prop_bot`
   is spent.  Then the tail: non-confusion facts, `value`/`neutral`,
   canonical forms, `red1_conv`, `subject_red1`, `progress_gen`.

---

# As built

All nine stages are done and the whole dev compiles.  No `Admitted`, no
`admit`, no new `Axiom`: the only axioms used are the ones the dev already
rested on (`proof_irrelevance` through `Val_irr`/`ValTy_irr`, plus what
`dependent destruction`/Equations pull in).  Two of the predictions above were
wrong, and both corrections are worth keeping.

## Correction 1: `Val`/`EqVal` do NOT stay inert at `tprop`

Stage 8 above says `tprop` can be a `True` arm.  That is true for the *element*
side (proof irrelevance really is free — the headline finding stands) but
**false for the type side**: with `Val` inert at `tprop`, the adequacy case for
`t_prop_u` is *unprovable*.

Why: `st_prop_u` must produce `Val RB Δ A[σ] tuniv WT` where `WT : wt u tuniv`
and `u` may be a Π *code* (`A : Prop` is a type, e.g. `Π x:N. P`).  At
`(tpi …, tuniv)` `Val` is the real Π-type record (`HeadRed A[σ] (tpi A' B')`,
domain `Val`, the two `PiEdge`s) — and nothing in the hypotheses can build the
`HeadRed` without a canonical-forms argument.  Agda gets it from its own IH at
`PropCode`: `adequacySub2-Prop-U-PiCode`'s last clause is

    val_bg = mkSigma vtU (snd val_bg_prop)      -- Adequacy5.agda:466-475

i.e. `Val2` at `(PiCode b g, PropCode)` carries the *same* Π data as at
`UCode`, and the rule just swaps the `Red3` leaf.

So the arm is, in `raw_validity.v`:

    | tprop => fun (h : wt u tprop) =>
        Rec.ValTy (@Val k) (@EqVal k) Γ M (wt_prop_univ h)

— the `tuniv` content at the code lifted by
**`wt_prop_univ : wt v tprop -> wt v tuniv`** (`types.v`, rank recursion via
`strong_ind` + `In_rk_fun2`; Agda's "Part 5b: FinMem PropCode-to-UCode").
Neither arm looks at the type *expression*, which is what makes the two
interchangeable:

    Val_prop_to_univ / Val_univ_to_prop / EqVal_prop_to_univ / EqVal_univ_to_prop
      : Val (S k) Γ M T h  <->  Val (S k) Γ M T' h'      (h : wt u tprop, h' : wt u tuniv)

proved by `reflexivity` + `ValTy_irr`.

**Cost of the non-inert arm: 15 new cases in `raw_validity.v`**, and *every one
of them is the `wt_tpi` case's script with `Val_tuniv`/`EqVal_tuniv` replaced by
`Val_tprop`/`EqVal_tprop`* — `Val_EqVal`, `EqVal_Val1`, `EqVal_Val2`, the four
`HeadRedVE` expand/contract conjuncts, `restrictVal_step`,
`restrictEqVal_step`, the four fuel-stability lemmas, and `SYM`/`TRANS` in
`FwdPER`.  In the two `restrict*_step` cases the two lifted `wt` derivations are
rebuilt by hand (`eapply wt_prop_univ; eapply wt_tpi_prop; eauto`) and the
inner case analysis has only two cases, since `bot` and a Prop-valued `tpi` are
the only inhabitants of `tprop`.  Nothing else in `raw_validity.v` or
`adequacy.v` broke.

With the arm in place the six adequacy rules are cheap:

| rule | proof |
| --- | --- |
| `t_prop` | `st_univ` verbatim |
| `t_prop_u` | typed enlargement `u' ≥ u` from `typing_EvalRel` (Agda's `theorem1`), IH there, `Val_prop_to_univ`, `restrictVal` back down to `u`, `Val_fuel_down_to` |
| `t_tpi_prop` | `st_tpi` with the codomain lifted by `st_prop_u`, then `Val_univ_to_prop` |
| `c_prop` | `InvTyped_prop_bot` gives `u = bot`, then `EqVal_Bot` |
| `c_prop_u` | `sc_prop_u` = `st_prop_u`'s binary half |
| `c_tpi_prop` | `sc_tpi` with the codomain conversion lifted by `c_prop_u`/`sc_prop_u`, then `EqVal_univ_to_prop` |

`InvTyp_Pi` is now proved **once for both sorts**: `Section PiFormation` in
`typing_semantics.v` abstracts `Typed_pi_edge_gen`/`Typed_pi_append_gen`/
`InvTyp_Pi_gen` over a sort code `sc : elt` and a sort term `st : forall m, Tm m`
(`Hsort_le`/`Hsort_ER`/`Hsc`/`Hform`); `InvTyp_Pi` and `InvTyp_Pi_prop` are the
two instances (`wt_tpi` / `wt_tpi_prop`).

## Correction 2: the shape of the sort-inversion disjunction

The table above predicted a right disjunct `Γ ⊢ tuniv ≡ tprop ∈ tuniv`.  That
is *not* provable — and not needed.  What `t_prop_u` actually gives is that the
**given type is literally `tuniv`**, so the alternative is about `T`:

    typing_zero_inv : Γ ⊢ zero ∈ T -> Γ ⊢ tnat ≡ T ∈ tuniv \/ Γ ⊢ tuniv ≡ T ∈ tuniv

Both disjuncts have the same shape (`X ≡ T ∈ tuniv`), which is what makes the
disjunction stable under `t_conv` (`c_trans` on either side) and lets every use
site kill the extra one with the *existing* non-confusion facts.  Which lemmas
change:

* unchanged (their principal type *is* `tuniv`, so `t_prop_u`'s case is
  `c_refl`): `typing_univ_inv`, `typing_nat_inv`, `typing_tsig_inv`,
  `typing_tid_inv`, and the new `typing_prop_inv`;
* gain `\/ Γ ⊢ tuniv ≡ T ∈ tuniv`: `typing_zero_inv`, `typing_succ_inv`,
  `typing_rfl_inv`, `typing_abs_inv`, `typing_app_inv`, and `typing_mkpair_inv`
  (which lives in `adequacy.v`);
* `typing_tpi_inv` becomes `Γ ⊢ tuniv ≡ T ∈ tuniv \/ Γ ⊢ tprop ≡ T ∈ tuniv` —
  a `tpi` code genuinely inhabits both sorts.

Use sites go through one tactic, `inv_alt H` (`adequacy.v`), which case-splits
and closes the second alternative with `tuniv_not_*`/`tprop_not_*`.  Four new
non-confusion facts were needed (`tprop_not_tpi`, `tprop_not_tsig`,
`tprop_not_tid` via `piConv`/`sigmaConv`/`idConv`; `tprop_not_tnat` via
`conv_EvalRel` at `bot_env`), plus `tuniv_not_tid`; and `tnat_not_tpi`,
`tpi_not_tnat`, `tuniv_not_tpi`, `tuniv_not_tsig` had to move earlier in the
file, since `red1_conv`/`subject_red1` now need them.

## Two Coq gotchas worth remembering

* `t_prop_u`'s conclusion matches *every* `_ ∈ tuniv` goal, so an
  `econstructor`/`eauto` catch-all will pick it and close its premise with an
  **unguarded** recursive call ("Cannot guess decreasing argument of fix" in
  `substitution_tm`).  Dispatch the two Prop sort rules with explicit
  `match goal` blocks *before* the catch-all.
* There is **no value-downward closure for `wt`** (`le v u -> wt u a -> wt v a`
  looks false: the keys of a smaller graph are unconstrained).  `wt_le` moves
  the *type* code **up**.  Wherever the Agda argument seems to need the former,
  it is really the latter plus `restrictVal` — as in `InvTyped_prop_bot` and
  `st_prop_u`.

