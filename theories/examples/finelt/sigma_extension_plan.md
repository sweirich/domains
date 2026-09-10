# Σ-types (Agda `SigmaProp/`) — port plan

Ported from `~/github/agda/domain-semantics/SigmaProp/`, which is the Agda
variant adding **Σ-types** *and* a proof-irrelevant impredicative `Prop` sort.
**Only Σ is in scope here**; `Prop` is deferred (see "Why Prop is deferred").

The ID port (`id_extension_plan.md`) is the template: same file order, same
kinds of lemma, and its `spine_*` / transport machinery is reusable.

## Why this should be much cheaper than J

`Fst`/`Snd` are **binder-free projections, not motive-driven eliminators**.
The whole cost of the J driver was `jcase_motive_EqVal`: three nested
application levels, two selections per level, a per-level type transport
through `PiEdgeEqTy`, and fuel that needed `EqVal_fuel_any` to close.  A
projection has none of that — the `EvalRel` clauses are one line each:

    EvalRel (Fst M) ρ c = if is_bot c then True else exists v, EvalRel M ρ (pair c v)
    EvalRel (Snd M) ρ c = if is_bot c then True else exists u, EvalRel M ρ (pair u c)

(Agda spells one case out per code shape; they are all the same clause.)

The genuinely new pieces are `SelectionSigma.agda` (does the value-graph
selection machinery need a pair analogue?) and `conv-pair-eta` — surjective
pairing, for which `sc_eta` at Π is the model.

## Value domain

`SigmaProp/BasicSigma.agda` adds `SigmaCode : FinEl -> FinFun -> FinEl` and
`PairCode : FinEl -> FinEl -> FinEl` (plus `PropCode`, out of scope).  In Coq
`elt` gains, mirroring `tpi`/`abs`:

    | tsig   : elt -> list (elt * elt) -> elt
    | mkpair : elt -> elt -> elt

- `rk (tsig a f) = 1 + max (rk a) (rk_fun f)` — same as `tpi`.
- `rk (mkpair u v) = 1 + max (rk u) (rk v)`.
- `valid (tsig a f) = valid a && valid_fun f` — same as `tpi`.
- `valid (mkpair u v) = valid u && valid v && ~~ (is_bot u && is_bot v)`.
  **Note the disjunction**: Agda's `Coherent (PairCode u v)` carries
  `Or (NotBot u) (NotBot v)` — a pair of two `bot`s is not a valid element, it
  collapses to `bot`.  This is the `~~ is_nil g` side condition of
  `valid (abs g)` in another guise, and it is the one place Σ is *not* a
  transcription of `tpi`/`tid`, where `valid (rfl w) = valid w` outright.
- `le (tsig a f) (tsig a' f') := le a a' && le_fun f f'` (as `tpi`);
  `le (mkpair u v) (mkpair u' v') := le u u' && le v v'` (as `tid`).

### The `rk` warning does not apply

`SigmaProp/RankCounterexamplesSigma.agda` warns that Agda's `rk` is a *size*
measure (a `suc` per cons in `rkFun`) rather than the iterative-stage RANK its
termination arguments need.  **Coq's `_rk_fun` is already a plain `max` over
the list with no per-cons `suc`** (`findom.v:81`), i.e. it already *is* the
iterative-stage RANK.  So the counterexamples are about a defect of the Agda
definition that this development does not share, and the well-founded
recursions on `rk` (`le`, `app`, `wt_le`/`wt_lub`) need no rethinking.

## Membership (`wt`, types.v)

From `PaperSemanticsSigma.agda`'s `FinMem`:

- `wt (tsig a f) tuniv` — the `tpi` rule verbatim: `wt a tuniv`, every key of
  `f` at `a` and every value at `tuniv`, plus the coherent tail.
- `wt (mkpair u v) (tsig a f)` — `wt u a`, **`wt v (app f u)`**,
  `valid (mkpair u v)`, and `wt (tsig a f) tuniv`.

The second component's type code is the function table applied to the first,
`app f u`.  That is the dependency, and it is exactly the `app f u_sel` shape
the Π machinery already uses, so `wt_app`/`all_app_is_tuniv` should carry over.

Also worth recording: `FinMem (SigmaCode a f) PropCode = Empty` — Σ-types live
only in `U`, never in `Prop`.  That is what makes deferring `Prop` sound rather
than merely convenient.

## Syntax and rules

`syntax.sig` gains (only `tsig` binds):

    tsig    : Tm -> (bind Tm in Tm) -> Tm
    mkpair  : Tm -> Tm -> Tm
    pfst    : Tm -> Tm
    psnd    : Tm -> Tm

Typing (`ty-Sigma`/`ty-MkPair`/`ty-Fst`/`ty-Snd`):

    t_tsig    Γ⊢A:U, Γ,A⊢B:U                          ⟹ Γ ⊢ tsig A B : U
    t_mkpair  … , Γ⊢M:A, Γ⊢N:B[M..]                   ⟹ Γ ⊢ mkpair M N : tsig A B
    t_pfst    … , Γ⊢M:tsig A B                        ⟹ Γ ⊢ pfst M : A
    t_psnd    … , Γ⊢M:tsig A B                        ⟹ Γ ⊢ psnd M : B[(pfst M)..]

Conversion — eight rules: `c_tsig` (congruence), `c_beta_fst`, `c_beta_snd`,
`c_pair_eta` (surjective pairing), `c_mkpair_fst`, `c_mkpair_snd`, `c_pfst`,
`c_psnd`.  Note `c_psnd`'s type is `B[(pfst M)..]`, so the congruence's two
sides sit at types differing by `pfst M` vs `pfst M'` — a type transport will
be needed there, on the model of `st_case`'s motive handling.

Head reduction: `hr_pfst (mkpair M N) → M`, `hr_psnd (mkpair M N) → N`, plus
the two congruences `hr_pfst_scrut` / `hr_psnd_scrut`, exactly as
`hr_jcase` / `hr_jcase_scrut`.

## Order of work

1. `findom.v` — `elt` constructors, `rk`, `valid`, `le`, the inversion lemmas
   (`le_tsig_inv`, `le_mkpair_inv`) and the `OTL` bundle cases.
2. `types.v` — `wt_tsig`, `wt_mkpair`, accessors, `wt_le`/`wt_lub` cases.
3. `syntax.sig` + regenerate `syntax.v` (see the command in the sig header).
4. `typing.v` — the four typing and eight conversion rules, plus renaming /
   substitution / `conv_typing` cases.
5. `reduction.v` — `HeadRed1` cases, determinism, and the `tsig`/`mkpair`
   normal-form lemmas.
6. `raw_semantics.v` — the four `EvalRel` clauses and the five closure lemmas.
7. `raw_validity.v` — `ValTySig`/`EqValTySig`/`ValPair`/`EqValPair` records and
   their restriction / fuel-stability / PER lemmas.
8. `typing_semantics.v` — `InvTyp_Sigma`, `InvTyp_MkPair`, `InvTyp_Fst`,
   `InvTyp_Snd` and the conversion cases.
9. `adequacy.v` — the formers (`st_tsig`, `st_mkpair`), the projections
   (`st_pfst`, `st_psnd`), and the congruences.
10. `sigmaInjectivity` — the payoff, on the model of `piInjectivity` /
    `idInjectivity`.

## Why `Prop` is deferred

`Prop` is not a type former but a second sort, and it is woven through the
judgments: `ty-Prop-U` and `conv-Prop-U` give Prop-to-U subtyping, `ty-Pi-Prop`
makes Π land in `Prop` when its codomain does, and `conv-Prop` is full **proof
irrelevance** —

    conv-Prop : Γ⊢A:Prop -> Γ⊢M:A -> Γ⊢N:A -> Γ ⊢ M ≡ N : A

Any two inhabitants of a `Prop` are convertible.  That changes `Val`/`EqVal`
at *every* code rather than adding an arm, and it brings an impredicative sort
and subtyping with it.  Since `FinMem (SigmaCode a f) PropCode = Empty`, Σ does
not depend on any of it, so the split is clean.  `Prop` is its own project.

---

## Progress and the one design consequence found

**Done and compiling: `findom.v`** (step 1).  `elt` has `tsig`/`mkpair` with
their `rk`, `valid`, `le`, `compatible`, `lub` clauses, the inversion and
introduction lemmas (`le_tsig_inv`, `le_mkpair_inv`, `le_mkpair_intro`,
`valid_tsig_intro`), the validity projections (`valid_tsig1/2`,
`valid_mkpair1/2/3`), and every existing lemma extended.

**Done: `types.v`'s `wt` constructors** (`wt_tsig`, `wt_mkpair`) and the
`wt_le` half of the `WTLE` bundle, plus `wt_tsig_tpi` / `wt_tpi_tsig` — the two
codes are typed by *identical* premises and their `valid`s are the same
formula, so the whole Π-table machinery (`all_app_is_tuniv` above all) is
reused for Σ rather than duplicated.

**Solved.**  For `mkpair` the `wt_lub` goal is
`wt (mkpair (lub x x') (lub y y')) (tsig a g)`, whose `wt_mkpair` premise is
`wt (lub y y') (app g (lub x x'))`.  Establishing that needs
`wt (app g (lub x x')) tuniv`, i.e. `all_app_is_tuniv`, i.e. a bound on
`rk_fun g` — and `g` lives in the *type*, which the bundle's original measure
`max (rk u) (rk v) <= k` did not mention.

Two things recorded here earlier were wrong; both are corrected below.

### What did NOT work

**Annotating the element** — giving `mkpair` a third argument carrying its type
(or just its table), so the rank is included automatically.  This breaks
`EvalRel_compatible` (`EvalRel M ρ a -> EvalRel M ρ b -> compatible a b`): the
*term* `Core.mkpair M N` has no type subterm, so nothing in the `EvalRel`
clause can pin the annotation down, and both `mkpair u v (tsig tnat nil)` and
`mkpair u v (tsig tuniv nil)` would be legitimate codes for the same term —
yet `compatible tnat tuniv = false`.  Making `le`/`compatible` ignore the
annotation dodges that at the cost of antisymmetry, and leaves `rk` depending
on a component the order cannot see.  Agda declines this too: `PairCode u v`
stays at two components.  **This one still stands.**

### Correction 1: the type in the measure does NOT break `wt_rfl`

It was recorded here that strengthening the measure to mention `rk a` breaks
`wt_rfl`, because `tid c x y`'s components are unbounded by `rk (rfl w)`.
That is backwards: once the measure *includes* the type, `wt_rfl`'s type
components are bounded by the type's own rank —
`rk c < rk (tid c x y) <= k` — so the case is *helped*, not hurt.

### Correction 2: hoisting `app_is_tuniv` out (the "Agda architecture") is circular here

`PaperSemanticsSigma.agda` does have `EvalFun-in-UCode` with no rank bound,
resting on `finMemUCode-Sup` (join-closure at the universe only).  The
tempting Coq analogue is to hoist `wt_lub_tuniv` and `app_is_tuniv` out of the
`WTLE` bundle as standalone lemmas.  **That cannot be stratified in this
development**, and the reason is `Id`, which SigmaProp does not have:

`wt_lub_tuniv`'s `tid` case must prove `wt (lub x1 x2) (lub c1 c2)` — a join at
a *non-`tuniv`* type.  Since `x1` can itself be a `mkpair`, that pulls the
general `wt_lub` (and hence `app_is_tuniv`) back into the would-be universe
block.  Agda never faces this because SigmaProp has no `Id` fragment.  So the
layering does not split, and the fix has to be inside the bundle.

(Also corrected: the reading that `finMemUCode-Sup` is "self-contained" came
from an `awk` that stopped at the first blank line.  It *does* use
upward-closure-along-a-join; what is true is only that its mutual group does
not depend on the general `FinMem-Sup-element`.)

### The fix that works

Three parts, all in `types.v`:

1. **Both measures mention the type, and both are strict:**

       wt_le  : max (rk a) (rk b) < k
       wt_lub : max (rk u) (max (rk v) (rk a)) < k

   `rk (tsig a g) = 1 + max (rk a) (rk_fun g)` then hands the `mkpair` case
   `S (rk_fun g) < m` *for free* — the `1 +` in `rk` supplies the strictness —
   and that is exactly the level at which `all_app_is_tuniv` is instantiated:

       have RKg : S (rk_fun g) < m by lia.
       have ihg := ih _ RKg.

2. **One degenerate corner, dispatched by `lub_rec`.**  Putting `rk a` in the
   measure introduces a floor: where the recursion leaves the type alone —
   which happens exactly at the unit types `tnat` and `tuniv`, of rank 1 — and
   *both* joined elements are `bot`, the element ranks are 0 and cannot pay for
   that floor (`max 0 (max 0 1) = 1` is not `< 1`).  Every other descent is
   strict; this corner needs no recursion at all, since `lub bot z = z`.  The
   `lub_rec` tactic case-splits on `is_bot` first and closes those two branches
   outright; in the surviving branch non-botness gives `1 <= rk _`, which is
   precisely what `lia` was missing.

3. **Recursive bundle levels are chosen explicitly** in the `mkpair` case
   rather than left to `eauto`, which had been unifying the level evar by
   `assumption` against the rank hypothesis and thereby picking a level one too
   small.

Two smaller fixes fell out: the second components move up by
`le_fun_mono_arg` (fixed table, growing argument), not `le_fun_mono` (fixed
argument, growing table); and `types.v` needs local copies of `rk_pos_loc` and
`is_bot_eq_loc`, since `selection.v` and `raw_validity.v` are downstream of it.

## Progress log

- **step 1, `findom.v`** — done.  `elt` has `tsig`/`mkpair` with their `rk`,
  `valid`, `le`, `compatible`, `lub` clauses, the inversion and introduction
  lemmas (`le_tsig_inv`, `le_mkpair_inv`, `le_mkpair_intro`,
  `valid_tsig_intro`), the validity projections (`valid_tsig1/2`,
  `valid_mkpair1/2/3`), and every existing lemma extended.
- **step 2, `types.v`** — done.  `wt_tsig`, `wt_mkpair`, `wt_tsig_tpi` /
  `wt_tpi_tsig` (the two codes are typed by *identical* premises and their
  `valid`s are the same formula, so the whole Π-table machinery is reused for Σ
  rather than duplicated), and both halves of `WTLE` under the new measure.
- **step 3, `syntax.v`** — done.  Regenerated from `syntax.sig`; a purely
  additive diff (`Tm` goes 13 → 17 constructors, all four appended last).
- **step 4, `typing.v`** — done.  Four typing rules and eight conversion rules,
  plus the Σ cases of `renaming_typing`/`renaming_conv`,
  `substitution_tm`/`substitution_conv` and `conv_typing`.
- **step 5, `reduction.v`** — done.  `hr_pfst`/`hr_psnd` and the two scrutinee
  congruences, `HeadRed1_det`, `HeadRed_pfst`/`HeadRed_psnd`,
  `nf_tsig`/`nf_mkpair`.
- **step 6, `raw_semantics.v` + `eval_substitution.v`** — done.  The four
  `EvalRel` clauses and every closure lemma: `EvalRel_valid`,
  `EvalRel_mono_env`, `EvalRel_down`, `EvalRel_compatible_lub`, `EvalRel_ren`,
  `EvalRel_subst`, `EvalRel_subst_forward_max`, `EvalRel_subst_forward_wit`.
- **the mechanical pass** — `elt` and `wt` both gained their constructors at
  the END, so all 97 nine-branch positional `destruct`/`inversion` patterns
  across the downstream files just needed two more empty slots.  Driven off the
  compiler; zero repairs.  `selection.v` needed no change at all.
- **Σ is inert in the logical relation for now.**  `Val`, `EqVal`, `ValTy` and
  `EqValTy` all have a catch-all arm, so `tsig` (as a type code) and `mkpair`
  (as an element) are `True` there.  `raw_validity.v` has `Val_tsig`,
  `Val_mkpair`, `EqVal_mkpair` (all `reflexivity`) plus an `sigma_inert` tactic
  for the extra trivial goals.

- **step 8, `typing_semantics.v`** — done.  All four `InvTyp_*`, all eight
  `InvConv_*`, and the twelve dispatch cases of
  `typing_EvalRel`/`conv_EvalRel`.
- **step 9, `adequacy.v`** — **DONE**.  All twelve `st_*`/`sc_*` dispatch cases
  (`st_tsig`, `st_mkpair`, `st_pfst`, `st_psnd`; `sc_tsig`, `sc_beta_fst`,
  `sc_beta_snd`, `sc_pair_eta`, `sc_mkpair1`, `sc_mkpair2`, `sc_pfst`,
  `sc_psnd`), plus the helpers `sigma_cod_eval`, `ValTy_tsig_typings` and the
  `st_*_edge` bundles.
- **step 10** — **DONE**: `sigmaConv` / `sigmaInjectivity`, the `piConv` /
  `piInjectivity` pair verbatim.
- **the syntactic-metatheory tail** — **DONE**: `red1_conv`, `subject_red1` and
  `progress_gen` have their Σ cases (`HeadRed1_pfst_inv`/`_psnd_inv`,
  `typing_mkpair_inv`, `typing_tsig_inv`, seven Σ non-confusion lemmas,
  `canonical_sigma`, `v_tsig`/`v_mkpair`, `ne_pfst`/`ne_psnd`).
- **step 7, `raw_validity.v`** — **DONE**, admit-free.  See
  "Step 7 as built" below for what the plan below got right and the one thing
  it got wrong.

## Status: the port is complete

**The whole development compiles**, admit-free, and `Print Assumptions` on
`progress` and on `sigmaInjectivity` reports only the four standard axioms the
pre-existing development already used (`prop_ext`, `proof_irrelevance`,
`functional_extensionality_dep`, `eq_rect_eq`).  `Prop` remains deferred, as
planned.

## Step 7 as built (read this before touching `EqValPair`)

The plan below is accurate for `ValTySig`, `ValPair`, and the "no rank bound"
argument.  It is **wrong about `EqValPair`**, and the correction is the one
non-obvious fact in the whole Σ port.

**`EqValPair` carries no second-component equality.**  The natural definition
("`ValPair` on both sides plus the two components related, exactly as
`EqValId` is") is *not* symmetric, and cannot be made so at this fuel:

- the first components are related at the fixed type term `A0`, which is fine;
- the second components would be related at `B0[M1..]` — and the swapped
  statement needs them at `B0[N1..]`.  Those two type terms are convertible
  (`conv_subst_arg` on `conv Γ M1 N1 A0`) but not equal, and moving an `EqVal`
  across a type conversion needs an `EqValTy`, which here would have to come
  from `ValTySig`'s `PiEdgeEq` at fuel `S k`.  `SYM`/`TRANS` in `fwd_per_all`
  have only `rk u < S k` for the *element* code `mkpair x y`; they have no
  bound at all on the *type* code `tsig a g`, and under type-in-type none is
  derivable.  So the fuel cannot be raised and the transport is unavailable.

The Agda reference resolves this the same way, and it is worth quoting.
`SigmaProp/Validity5Core.agda`'s `REqValSigma` has fields

    domA codB red htFstM htFstN cohW1 fmW1
    valFstM valSndM valFstN valSndN eqFst

— four *unary* component records and `eqFst`, and **no `eqSnd`**.  (Note also
that Agda states the record over `Fst M`/`Snd M` with `codeFst w`/`codeSnd w`,
where the Coq port pattern-matches `mkpair x y` and stores the head-reduced
`M1`/`M2`; the two are interchangeable here.)  With `eqSnd` gone,
`EqValPair_sym` and `EqValPair_trans` are three lines each: swap or compose the
unary records, `c_sym`/`c_trans` the stored `conv`s (retyping the one at
`B0[M1..]` by `conv_subst_arg`), and hand `eqFst` to `IHsym`/`IHtrans` at code
`x`.

The second-component equality is not lost, it is *relocated*: `c_psnd`'s
adequacy recovers it by enlarging the code, building the `psnd` evaluation at
the pair's own second component code, re-running adequacy there, and
sup-transporting back — Agda's `adequacyEqSub2-Snd-from-EqValPair2`
(`Adequacy5.agda:2604`).  Budget for that when writing step 9's `sc_psnd`.

**Everything actually added in step 7** (all in `raw_validity.v`):

| group | lemmas |
| --- | --- |
| records | `ValTySig`, `EqValTySig`, `ValPair`, `EqValPair` + the four `reflexivity` unfolding lemmas |
| irrelevance | `PiEdgeVal_irr`, `PiEdgeEq_irr`, `PiEdgeEqTy_irr` |
| head reduction | `ValTySig_headred_expand/_contract`, `ValPair_headred_expand/_contract`, `EqValPair_headred_expand/_contract` |
| restriction | `restrictPiEdgeVal`, `restrictPiEdgeEq`, `restrictPiEdgeEqTy`, `ValTySig_restrict`, `EqValTySig_restrict`, `ValPair_restrict`, `EqValPair_restrict` |
| type-code motion | `sig_cod_valid`, `ValPair_up`, `EqValPair_up`, `ValPair_down`, `EqValPair_down` |
| fuel | `HVPr`, `HEPr`, `fuel_ValPair_S`, `fuel_EqValPair_S`; `FuelStable` 10 → 12 conjuncts; `fuel_ValPair`/`fuel_EqValPair` projections |
| conversion | `ValTy_tsig_typings`, `ValPair_fwd`, `EqValPair_fwd` |
| PER | `EqValPair_sym`, `EqValPair_trans` |

The `tsig` arms of `fuel_ValTy_S`, `fuel_EqValTy_S`, `ETSYM` and `ETTRANS` are
the corresponding `tpi` scripts **verbatim**, with the derivation routed
through `wt_tsig_dom`/`wt_tsig_tpi` — `EqValTySig` has exactly the `tpi` shape.
`restrictPiEdgeVal`/`_Eq`/`_EqTy` were factored out of the existing `tpi`
blocks so both fragments share them.

Two small API notes that cost time:

- `le_fun_mono` (monotone in the *graph*) is the lemma for
  `le (app g' x) (app g x)`; `le_fun_mono_arg` is monotone in the *argument*
  and does not apply.
- `EqVal_tuniv`'s right-hand side is the triple
  `ValTy M /\ ValTy N /\ EqValTy M N`, not `EqValTy` alone, so the `tsig`
  type-code cases need a three-way `split` before `EqValTySig_restrict` and
  friends will unify.

### The step 7 / step 9 dependency (the thing to know)

With Σ inert in the logical relation, the twelve remaining adequacy cases split
cleanly in two:

- **Six are free.**  `st_tsig`, `st_mkpair`, `sc_tsig`, `sc_mkpair1`,
  `sc_mkpair2` and `sc_pair_eta` all conclude at a type whose *code* is
  `tuniv` (with a `tsig` element code) or is a `tsig` code.  `Val`/`EqVal`
  there is the catch-all `True` — modulo the `bot` element, where `Val_Bot` /
  `EqVal_Bot` apply.  `wt_tsig_shape` says those are the only two shapes.
- **Six need the real records.**  `st_pfst`, `st_psnd`, `sc_beta_fst`,
  `sc_beta_snd`, `sc_pfst` and `sc_psnd` conclude at `A` or `B[(pfst M)..]` —
  *arbitrary* type codes, so their goals are real `Val`/`EqVal` obligations.
  Their only hypothesis about the scrutinee is
  `Val RB Δ M[σ] (tsig A B)[σ] WT`, which is `True`.  **No amount of work on
  `adequacy.v` can close them**: the information has to come from a genuine
  `ValPair` record.  So step 7 is a prerequisite for finishing step 9, and it
  is the last substantial piece of the port.

### Step 7: the real `Val`/`EqVal` records for Σ

Model them on the identity fragment (`ValTyId`/`ValId`/`EqValTyId`/`EqValId`),
which is the closest precedent — and note one big saving.

**`ValTySig` is almost free.**  A `tsig` type code carries exactly the same
table structure as a `tpi` one, so the `tsig` arm of `ValTy` is the `tpi` arm
with `Core.tsig` for `Core.tpi`, *reusing `PiEdgeVal`/`PiEdgeEq` unchanged* by
routing the derivation through `wt_tsig_tpi`.  Likewise `EqValTySig` reuses
`PiEdgeEqTy`.

**`ValPair` is the new content.**  By analogy with `ValId`:

    Definition ValPair {n} (Γ : Ctx n) (M A : Tm n) x y a g
      (h : wt (mkpair x y) (tsig a g)) : Prop :=
      exists A0 B0,
           HeadRed A (Core.tsig A0 B0)
        /\ conv Γ A (Core.tsig A0 B0) Core.tuniv
        /\ exists M1 M2,
                HeadRed M (Core.mkpair M1 M2)
             /\ conv Γ M (Core.mkpair M1 M2) A
             /\ Val Γ M1 A0 (wt_mkpair_fst h)
             /\ Val Γ M2 B0[M1..] (wt_mkpair_snd h)

`wt_mkpair_snd h` has code `app g x`, which is the code the term-level type
`B0[M1..]` should carry — the same pairing `ValPi`'s `PiAppVal` makes between
`app g u` and `B0[P..]`.  Store the `conv`s rather than deriving them from the
`HeadRed`s, for the reason spelled out in `ValPi`: red ⊆ conv is only available
*after* adequacy.  `EqValPair` is `ValPair` on both sides plus the two
components related, exactly as `EqValId` is.

Then `st_pfst` reads `M1` and its `Val` off the record, using
`HeadRed_pfst` + `hr_pfst` to get `HeadRed (pfst M) M1`, and retypes along
`conv Γ A (tsig A0 B0) tuniv`; `st_psnd` is the same with `M2` and
`B0[M1..]`, plus a transport from `M1` to `pfst M` along `c_beta_fst`.
`sc_beta_fst`/`sc_beta_snd` fall out of the same record.

**`ValPair` needs NO rank bound — it is a `ValId`, not a `ValPi`.**  This is
the saving that makes the step affordable, and it is worth being precise about
why, because it is the one place the Π fragment is genuinely harder.

`ValPi` has to quantify over *all* argument codes (`PiEdgeVal`/`PiAppVal` are
`forall u v, Selection … -> …`), and under type-in-type that is not
rank-well-founded: for `tpi tuniv f` the argument `u` ranges over codes of
unbounded rank.  So the Π edges carry an *explicit* bound `rk u < rk (tpi b f)`
(see the design comment above `Fixpoint Val`, and the Agda dev's answer, which
is to quantify over `Selection f u v` so that `SelectionRank` supplies the
bound implicitly).

`ValPair` quantifies over nothing.  Its two components sit at fixed sub-codes,

    rk a           <  rk (tsig a g)                     (* first component *)
    rk (app g x)  <=  rk_fun g  <  rk (tsig a g)         (* second component *)

both strictly smaller with no argument quantification at all — exactly the
position `ValId`'s `w`/`c` are in.  Consequently the new fuel-stability
conjuncts look like `HVI`/`HEI`, whose only hypotheses are
`rk (rfl w) <= k -> rk (tid c x y) <= k`, and *not* like `HVP`/`HEP`.

**Concrete shape of the obligation.**  `FuelStable` gains **two** conjuncts,
`HVPr`/`HEPr` for `ValPair`/`EqValPair` (mirror `HVI`/`HEI` field for field),
plus new *cases* — not new conjuncts — in `FU`/`FD`/`FEU`/`FED` and in
`HVT`/`HET`.  The latter because `ValTySig` lives inside `ValTy`, which
`HVT`/`HET` already quantify generically over `wt u tuniv`.

**Cost.**  For calibration, the identity fragment mentions `ValTyId`/`ValId`
about 160 times in `raw_validity.v`: the arms themselves are small, but every
closure lemma needs the new case — restrict/up/down, fuel up/down,
sym/trans, fwd, head-expansion/contraction, and `Val_irr`.  Σ should come in
under that, since `ValTySig` reuses the Π edges wholesale and `ValPair` needs
no edge at all.  `raw_validity.v` will be red throughout, so start from the
current all-green-but-`adequacy.v` state rather than mixing it with anything
else.

## The `psnd` equality — resolved

`EqValPair` **does** carry a second-component equality
(`EqVal Γ M2 N2 B0[M1..] (wt_mkpair_snd h)`), reversing the Agda-faithful "no
`eqSnd`" shape.  The reason is architectural: Coq's `semantic_typing` bundles
the cross-substitution equality `EqVal M[σ] M[σ']` with the unary `Val`
statement, so `st_psnd`'s `EqVal` edge and `sc_psnd` need the two pairs' second
components related.  Agda's `adequacySub2` is purely unary (the σ/σ′ business
lives in `ValidSub2`/`EqValSub2`) and recovers `conv-Snd` by *re-running*
`adequacyEqSub2` at the pair's own component codes — a recursive call there, not
available to a universally-quantified Coq statement being proved.

**The fix, at the root:** `FwdPER`'s `SYM` and `TRANS` now bound the **type**
code as well as the element code (`rk a < k`; they used to bound only
`rk u < k`).  With that, `EqValPair_sym`/`EqValPair_trans` transport the field
between `B0[M1..]` and `B0[N1..]` using the type record's own `PiEdgeEq`
(related arguments give equal codomains) at the canonical selection below `x`,
followed by `IHEfwd` — whose guard `rk (app g x) < k` is exactly what the new
bound supplies, since `rk (app g x) <= rk_fun g < rk (tsig a g) < k`.

The bound costs almost nothing, because **`EqVal` is only ever used at
above-rank fuels** — every downstream call site already had a rank guard on
both codes.  In full:

- `EqVal_sym`/`EqVal_trans` and `Section IdFwd`'s `IHtrans` gain one
  hypothesis; `EqValId_sym`/`EqValId_trans` gain `rk c < k`;
- the `abs` cases of `SYM`/`TRANS` already needed this bound for their own
  recursive call at type code `app g uu`, and now get it;
- the `succ` cases need `rk tnat < k`, which fails at `k = 1`; there the
  predecessor's code is forced to `bot`, so they split on `le_lt_dec 2 k` and
  use the new `EqVal_rk0` (`rk u <= 0 -> EqVal k Γ M N T h`).  That is the
  **only** boundary case the change costs;
- ~10 call sites in `adequacy.v` gain one `lia`.

For the record, the shapes of `eqSnd` that do *not* work (all worked out and
rejected before settling on the rank bound):

| shape | breaks |
| --- | --- |
| both `B0[M1..]` and `B0[N1..]` | `TRANS`: the middle term introduces a third `B0[Q1..]` |
| `forall P, conv Γ P M1 A0 -> conv Γ P N1 A0 -> EqVal Γ M2 N2 B0[P..] h2` | `SYM`/`TRANS`/`restrict` fine, but `EqValPair_up` needs `Val Γ B0[P..] tuniv (wt (app g x) tuniv)` for the quantified `P`, and `sig_cod_valid` only gives it for `B0[M1..]` |
| the same, plus a `Val`/`EqVal` hypothesis on `P` at a code | now `up` works but `restrict` cannot: the hypothesis is contravariant, so shrinking the record's codes would need to *grow* a `Val`'s element code, which is not one of the six `UDR` facts |
| Selection-indexed, like `PiAppEqVal` | `PiAppEqVal`'s result is indexed by the *selection's* codes, which is what makes Π's `up`/`restrict` work; Σ's second component has a fixed element code `y`, so the result cannot be re-indexed that way |

### Step 10: `sigmaInjectivity`

Once `ValTySig` exists this is the `piInjectivity` argument verbatim, read off
`ValTySig`'s `HeadRed A (Core.tsig A0 B0)` component.
