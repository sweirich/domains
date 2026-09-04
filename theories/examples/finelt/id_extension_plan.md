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

## Step 2 (done): syntax and evaluation

`syntax.sig` / `syntax.v` gained the three binder-free constructors

```
tid   : Tm -> Tm -> Tm -> Tm     -- Id A a b
rfl   : Tm -> Tm                 -- Ref a
jcase : Tm -> Tm -> Tm -> Tm     -- J C d p
```

`syntax.v` is generated from `syntax.sig` by

```sh
autosubst -o syntax.v -s rocq -v ge813 -no-static syntax.sig
```

(that command is also recorded as a `--` comment at the top of `syntax.sig`;
note it is `autosubst`, *not* the `as2-exe` that is also on `PATH` — `as2-exe`
rejects the `Tm(var) : Type` header these `.sig` files use). Never hand-edit
`syntax.v`: comments added there are dropped on the next regeneration.

For the record, the boilerplate for a binder-free constructor is completely
determined by analogy with `app`: every clause of `ren_Tm`, `subst_Tm`,
`idSubst_Tm`, `extRen_Tm`, `ext_Tm`, `compRenRen_Tm`, `compRenSubst_Tm`,
`compSubstRen_Tm`, `compSubstSubst_Tm` and `rinst_inst_Tm` applies the recursor
unchanged to every argument, with no `up`-lifting anywhere.

`raw_semantics.v` gained the three `EvalRel` clauses (transcribed from
`ID/Model/Eval.agda`: `tid` behaves like `tpi`, `rfl` like `abs`, `jcase` like
`ncase` with the proof branch an `app` edge) and the `tid`/`rfl`/`jcase` cases
of all five closure lemmas. `eval_substitution.v` gained the four
renaming/substitution lemmas' cases.

The `jcase` join-closure needed the same *merged-edge* argument as `fix_`: two
edges `va ↦ a`, `vb ↦ b` of the base merge to `(va ⊔ vb) ↦ (a ⊔ b)`, which is
below `abs [(va,a);(vb,b)]`, so `EvalRel_down` delivers it.

`typing_semantics.v`, `raw_validity.v` and `adequacy.v` needed *no* changes:
no typing rule mentions the new terms yet, so the derivation-recursive
`Fixpoint`s have no new cases. The tree is green and admit-free.

## The logical relation for Id (read off `ID/Validity/Stratified.agda`)

This maps cleanly onto the existing Coq structure: `Val` at `a = tuniv` already
dispatches to `Rec.ValTy` on the *value* code, so only **two new arms** are
needed — a `tid` arm in `Rec.ValTy`/`Rec.EqValTy`, and a `(rfl, tid)` arm in
`Val`/`EqVal`. There is **no Selection edge** for `Id` (it is proof-irrelevant),
so none of the `PiApp`/`PiEdge` machinery is duplicated.

`Rec.ValTy Γ M (tid t u v)` — Agda `RValTyId` — records that the *type* term
reduces to an `Id`:

* `HeadRed M (tid A₀ a₀ b₀)` and (our `Red3`) `conv Γ M (tid A₀ a₀ b₀) tuniv`;
* `typing Γ A₀ tuniv`, `typing Γ a₀ A₀`, `typing Γ b₀ A₀`;
* `ValTy Γ A₀ t` — the domain is a valid type at the domain code;
* `wt u t` and `wt v t` — the endpoints at the **membership** level; and
* `Val Γ a₀ A₀ u t`, `Val Γ b₀ A₀ v t` — the endpoints **logically**, which is
  what lets the diagonal `EqValTy` be built by reflexivity and what feeds the
  J motive edges.

`Val Γ M A (rfl w) (tid t u v)` — Agda `RValId`, paired with
`Rec.ValTy Γ A (tid t u v)` — records that the *term* reduces to a `Ref`:

* `HeadRed M (rfl w₀)` and `conv Γ M (rfl w₀) A`;
* **`conv Γ w₀ a₀ A₀` and `conv Γ w₀ b₀ A₀`** — the witness is convertible to
  *both* endpoints.  This is the heart of the fragment: it is Coquand's
  membership rule (`w ≤ u`, `w ≤ v`) lifted to the syntax, and it is what
  Id-injectivity reads back off;
* `wt (rfl w) (tid t u v)`; and
* `EqVal Γ w₀ a₀ A₀ w t`, `EqVal Γ w₀ b₀ A₀ w t` — the same two facts
  logically.

`Rec.EqValTy Γ M N (tid t u v)` is both `RValTyId`s plus `REqValTyId`: the two
`Id`-normal forms' components are convertible (`conv A₀ A₀' tuniv`,
`conv a₀ a₀' A₀`, `conv b₀ b₀' A₀`), `EqValTy A₀ A₀' t`, and the *reducible*
endpoint equalities `EqVal a₀ a₀' A₀ u t` / `EqVal b₀ b₀' A₀ v t` — needed to
forward-transport a value record's endpoint facts across a type conversion.
`EqVal` at `(rfl w, tid …)` is symmetric: both `RValId`s plus `REqValId`.

Everything at a `rfl` *type* code, and at any other value code under an `tid`
type code, is `True` — as for the existing `tnat` fragment.

## Remaining work, in dependency order

1. **`Val`/`EqVal` clauses for `tid`/`rfl`**, as just described, and the
   `tid`/`rfl` cases of `raw_validity.v`'s ~30 structural lemmas — which stop
   being trivial at that point (head expansion/contraction, up/down/restrict,
   fuel stability, and the PER).
2. **Rules**: define `motive_ty`/`base_ty` and add the typing, conversion and
   reduction rules above. This is the first step that forces new cases in
   `typing_EvalRel` / `conv_EvalRel` and in the adequacy drivers.
3. **Soundness**: `InvTyp_Id`, `InvTyp_Ref`, `InvTyp_J` — `InvTyp_J` should be
   as cheap as `InvTyp_Y` turned out to be, since the `JBranch` `RefEl` clause
   *is* an `App` edge and `InvTyp_App` needs nothing from its argument.
4. **Adequacy**: the `J` driver — Agda splits it over
   `JApp / JAppE / JCase / JDriver / JEndpoint / JMotive / JRef / JTypeEq`.
   This is the bulk of the work and the only genuinely new mathematics.
5. **`IdInjectivity.agda`** — the payoff, on the model of `piInjectivity`.

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
