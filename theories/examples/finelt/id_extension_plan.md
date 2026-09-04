# Porting the `ID/` (identity type) extension

Target: Agda's [`ID/`](../../../../agda/domain-semantics/ID) variant — 76 files —
which adds Martin-Löf's element-level identity type to the `MIN` core and proves
**Id-injectivity** on top of Π-injectivity and subject reduction. It is
postulate-free and pragma-free, so nothing about it is known to be hard.

## The Agda design (read off `ID/Syntax/*`, `ID/Domain/*`, `ID/Model/Eval.agda`)

The whole extension is **binder-free**, which is what makes it tractable: the
motive and the base case of `J` are ordinary terms of Π-type, not
binder-carrying expressions.

### Syntax — three constructors, no `bind`

```
Id  : Tm -> Tm -> Tm -> Tm     -- Id A a b : U
Ref : Tm -> Tm                 -- Ref a : Id A a a
J   : Tm -> Tm -> Tm -> Tm     -- J C d p
```

with the motive and base *types* spelled out as derived Π-types:

```
motiveTy A   = Pi A (Pi A⟨↑⟩ (Pi (Id A⟨↑⟩⟨↑⟩ (var 1) (var 0)) U))
baseTy A C   = Pi A (App (App (App C⟨↑⟩ (var 0)) (var 0)) (Ref (var 0)))
```

`J C d p` at `p : Id A a b` has type `App (App (App C a) b) p` — binder-free, so
it substitutes definitionally and needs no commutation lemma.

### Typing / conversion (`ID/Syntax/Typing.agda`)

`ty-Id`, `ty-Ref`, `ty-J`; `conv-Id`, `conv-Ref`, `conv-J` (congruence, with the
LHS component typings as premises, exactly as our `c_abs`/`c_fix_cong` do), and

```
conv-J-beta : J C d (Ref a₀)  ≡  App d a₀   :   App (App (App C a₀) a₀) (Ref a₀)
```

**This is the key simplification.** Because the eliminator fires only on the
*literal diagonal* `Ref a₀ : Id A a₀ a₀`, both sides of the β rule have the
**same** type, so `conv-J-beta` carries no endpoint- or motive-equality premises
and subject reduction for it needs **no Id-injectivity**. (Id-injectivity is
proved, but as an independent corollary, not as an input to subject reduction.)

Reduction: `headred-J : J C d (Ref a) ⤳ App d a` plus the scrutinee congruence
`headred-J-scrut`.

### Domain model — two new finite-element codes

```
IdCode : elt -> elt -> elt -> elt    -- code of Id A a b: type code + endpoints
RefEl  : elt -> elt                  -- a proof value: the witness
```

`rk`, `Sup`, `Comp` and `LeCode` are all **componentwise** on both, with `Bot`
elsewhere. Membership (`ID/Domain/MemStage.agda`):

* `IdCode t u v : UCode` iff `t : UCode`, `u : t`, `v : t`;
* `RefEl w : IdCode t u v` iff `w : t` **and `w ≤ u` and `w ≤ v`** — Coquand's
  rule: a proof is a witness sitting below *both* endpoints.

### Evaluation (`ID/Model/Eval.agda`)

`Id` behaves like `Pi` (a type former), `Ref` like `Lam` (a value former), and
`J` like `Case` (an eliminator that dispatches on the scrutinee's value):

```
EvalRel (Id A a b) ρ (IdCode t u v) = Coherent … ∧ ⟦A⟧t ∧ ⟦a⟧u ∧ ⟦b⟧v
EvalRel (Ref a)    ρ (RefEl w)      = EvalRel a ρ w
EvalRel (J C d p)  ρ c              = ∃ w, EvalRel p ρ w ∧ JBranch C d ρ c w
  JBranch … c Bot      = Coherent c ∧ c ≤ ⊥
  JBranch … c (RefEl w) = EvalRel d ρ (w ↦ c)        -- an App edge
  JBranch … c _         = ⊥
```

Note the `J` clause has exactly our `ncase` shape, so it stays structurally
recursive with no extra device (contrast the `Y` clause, which needed `Approx`).
The motive `C` is **irrelevant to the value** — it only constrains the type.

## Status

**Done and compiling** (`tid`/`rfl` are the Coq names for `IdCode`/`RefEl`):

| Layer | File | State |
|---|---|---|
| order, join, compatibility, validity, rank | `findom.v` | ✅ green |
| membership `wt` | `types.v` | ✅ green |
| value-graph selection | `selection.v` | ✅ green |
| `EvalRel` + closure lemmas | `raw_semantics.v` | ✅ green (codes absorbed by existing catch-alls) |
| renaming/substitution for `EvalRel` | `eval_substitution.v` | ✅ green |
| soundness `InvTyp_*` | `typing_semantics.v` | ✅ green |
| logical relation `Val`/`EqVal` | `raw_validity.v` | ✅ green |
| adequacy | `adequacy.v` | ✅ green |

The tree builds, is admit-free, and `adequacySub` / `piInjectivity` /
`subject_red` / `progress` still rest on exactly the four standard axioms. The
Id *codes* are in the model; no `Tm` constructor produces them yet, so
`Val`/`EqVal` fall through to `True` at an `tid` code and every new case in the
logical relation is either the existing `tuniv` case verbatim (`wt_tid` — an
`tid` code is a type code) or trivial (`wt_rfl`).

New in `findom.v`: `tid`/`rfl` clauses of `rk`, `compatible`, `lub`, `le`,
`valid`, `le_inv_view`, plus `le_tid_inv` and `le_rfl_inv`.
New in `types.v`: `wt_tid` and `wt_rfl` (Coquand's rule, as above).

## Remaining work, in dependency order

1. **`Val`/`EqVal` clauses for `tid`/`rfl`** (Agda `ID/Validity/Core.agda`):
   the `Red3`-style leaves, i.e. `HeadRed M (Ref M₁)` plus `conv Γ M (Ref M₁) A`
   at the `rfl` code, mirroring what we already do for `zero`/`succ`.
2. **Syntax**: add `tid`/`rfl`/`jcase` to `syntax.sig` and regenerate with
   `as2-exe` (available at `~/.local/bin/as2-exe`); define `motive_ty`/`base_ty`;
   add the typing, conversion and reduction rules above.
3. **`EvalRel` clauses** for the three new terms, then the five closure lemmas
   (`valid`, `mono_env`, `bot`, `down`, `compatible_lub`) and the substitution
   lemmas. The `J` join-closure is the `ncase` argument, not the `Y` one.
4. **Soundness**: `InvTyp_Id`, `InvTyp_Ref`, `InvTyp_J` — `InvTyp_J` should be
   as cheap as `InvTyp_Y` turned out to be, since the `JBranch` `RefEl` clause
   *is* an `App` edge and `InvTyp_App` needs nothing from its argument.
5. **Adequacy**: the `J` driver — Agda splits it over
   `JApp / JAppE / JCase / JDriver / JEndpoint / JMotive / JRef / JTypeEq`.
   This is the bulk of the work and the only genuinely new mathematics.
6. **`IdInjectivity.agda`** — the payoff, on the model of `piInjectivity`.

## Gotchas found so far

* **`all:` cannot see goals left over after a bullet block.** Extra cases must
  be added as further `-` bullets, not as a trailing `all: …`.
* **Numeric goal selectors shift.** `le_refl`, `le_lub_left`, `le_lub_right`,
  `le_trans` in the `OTL` bundle all used `2,3:` / `4,6:` / `5,6:`; the new
  constructors append goals at the end, so the *existing* indices survive, but
  the new goals must be selected explicitly. The goal lists are recorded in the
  comments there.
* **`le_trans`'s `all: erewrite ?le_trans ; cycle -2 ; eauto` is order-sensitive
  across the whole `all:` block**: with the `tid` conjunction in play the shared
  evar got mis-instantiated (producing unprovable goals like `le u₁ u₂`). It is
  now name-free and per-goal (`[> … ..]`), selecting the middle element by
  matching the context instead of leaving it to `eauto`.
* **Do not name the new constructors' arguments `u`, `v`, `a`, `f`, `g`.**
  `wt_tid`'s third argument was called `v`, which shadowed the `v` of
  `wt_lub : … forall v, …`, so `destruct v` destructed the wrong thing. They are
  `c x y` (code, endpoint, endpoint) for exactly this reason.
* `Set Implicit Arguments` makes *all* of `le_trans`'s `u v w` implicit (they
  occur in later argument types), so `with (v := …)` fails — use `@le_trans u v w`.
* `[ … | | ]` with two adjacent bars lexes `||` as one token; write `| | `.
