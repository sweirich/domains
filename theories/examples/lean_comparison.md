# Rocq `finelt` vs Lean `Lean4Lean` — Pi injectivity

A comparison of the Pi-injectivity proof in this repository
(`theories/examples/finelt/`, Rocq) with the one in
`~/github/lean/lean4lean/Lean4Lean/Experimental/` (Lean 4).

The headline finding: **both prove Pi injectivity by the same
domain‑theoretic recipe** — interpret one Pi type at a *trivial (bottom) Pi
value* in a finite‑element / "shape" model, transport that interpretation
across the conversion via a logical‑relation **adequacy** theorem, read off a
**weak‑head reduction** of the other side to a Pi, and finish with
**determinacy of head reduction on the Pi head‑normal form**. The two
developments are close enough that the lemmas line up almost one‑to‑one.

The Lean side is part of [Lean4Lean](https://github.com/digama0/lean4lean) (a
Lean-verified Lean kernel). Its `Experimental/` folder contains several
logical-relation experiments; the "shape" logical relation
(`ShapeLogRel.lean` + `ShapeLogRelAdequacy.lean`) is the one carrying the Pi
injectivity proof.

## The two theorems, side by side

**Rocq** ([finelt/adequacy.v](finelt/adequacy.v)):

```coq
Lemma piConv {n} (Γ : Ctx n) (A0 : Tm n) (B1 : Tm n) (F1 : Tm (S n)) :
  conv Γ A0 (tpi B1 F1) tuniv ->
  exists B0 F0, HeadRed A0 (tpi B0 F0)
             /\ conv Γ B0 B1 tuniv
             /\ conv (Γ ++ B0) F0 F1 tuniv.

Lemma piInjectivity {n} (Γ : Ctx n) (A0 A1 : Tm n) (B0 B1 : Tm (S n)) :
  conv Γ (tpi A0 B0) (tpi A1 B1) tuniv ->
  conv Γ A0 A1 tuniv /\ conv (Γ ++ A0) B0 B1 tuniv.
Proof.
  move=> H. destruct (piConv H) as [B0' [F0' [HR [convD convC]]]].
  have [EQA EQB] : B0' = A0 /\ F0' = B0
    by (eapply HeadRed_tpi_det; [ exact HR | apply ms_refl ]).
  subst B0' F0'. split; auto.
Qed.
```

**Lean** (`ShapeLogRelAdequacy.lean`):

```lean
theorem forallE_whRed_l (d : Γ ⊢ A₀ ≡ SExpr.forallE B₁ F₁ : .sort s) :
    ∃ B₀ F₀, Γ ⊢ A₀ ⤳* .forallE B₀ F₀ ∧ ∃ u v,
      Γ ⊢ B₀ ≡ B₁ : .sort u ∧ B₀::Γ ⊢ F₀ ≡ F₁ : .sort v := by
  have hPi : LE_Interp .nil (WShape.T (.forallE .bot WShapeFun.bot)) (.forallE B₁ F₁) := …
  have := (LR.adequacy d ((LE_Interp.sound d .nil).1.2 hPi) … ).2 .id
  have ⟨_, _, _, _, _, _, redA₀, redPi, convB, convF, _⟩ := … this
  cases WHNF.forallE.whRedS redPi; exact ⟨_, _, redA₀, _, _, convB, convF⟩

theorem forallE_inv (H : Γ ⊢ SExpr.forallE A₀ B₀ ≡ SExpr.forallE A₁ B₁ : .sort s) :
    ∃ u v, Γ ⊢ A₀ ≡ A₁ : .sort u ∧ A₀::Γ ⊢ B₀ ≡ B₁ : .sort v := by
  have ⟨_, _, red, H⟩ := forallE_whRed_l H
  cases WHNF.forallE.whRedS red; exact H
```

`piConv` ⇔ `forallE_whRed_l` and `piInjectivity` ⇔ `forallE_inv` are the same
statements (up to Lean's universe polymorphism — Lean existentially binds the
domain/codomain levels `u`,`v`, whereas Rocq is type-in-type and works at the
single universe `tuniv`). Both `piInjectivity`/`forallE_inv` are one-liners on
top of the "reduce-to-a-Pi" lemma, closed by head-reduction **determinacy**:
Rocq `HeadRed_tpi_det`, Lean `WHNF.forallE.whRedS` (a weak-head-normal form
reduces only to itself; `WHNF.forallE : WHNF Γ (.forallE A B)`).

## The shared proof architecture

| Step | Rocq (`piConv`) | Lean (`forallE_whRed_l`) |
|------|-----------------|--------------------------|
| 1. Trivial Pi value | `evalRel_Pi_trivial : EvalRel (tpi B1 F1) ρ (tpi bot nil)` | `hPi : LE_Interp .nil (WShape.forallE .bot WShapeFun.bot).T (.forallE B₁ F₁)` |
| 2. Transport across the conversion | conversion soundness `conv_EvalRel` in the bottom env (`bot_env`) | `LE_Interp.sound d .nil` transfers the interpretation from `forallE B₁ F₁` to `A₀` |
| 3. Run adequacy | `semantic_conv2` / `adequacyEqSub` (the fundamental theorem) | `LR.adequacy d …` |
| 4. Extract a Pi reduction | the `EqValTy` component at `tpi bot nil` exposes `HeadRed A0 (tpi B0 F0)` + component convs | the `Adequate` DefEq yields `A₀ ⤳* .forallE B₀ F₀` + component convs |
| 5. Determinacy on the Pi head | `HeadRed_tpi_det` (Pi is a head-normal form) | `WHNF.forallE.whRedS` (Pi is a WHNF) |

The crucial trick is identical: **evaluate the known Pi at the least
informative Pi value** — domain `bot`, empty/`bot` function graph
(`tpi bot nil` ↔ `forallE .bot [(.bot,.bot)]`) — so the interpretation carries
no information *except* "the head is a Pi," which is exactly what survives
transport along an arbitrary conversion and forces the other side to
head-reduce to a Pi.

## The underlying model: finite-element / "shape" domains

Both proofs are powered by a **finite-element domain** in which a function is a
finite list of input→output pairs, and the logical relation is an *ideal* of
such approximations closed under head reduction. This is the same core idea on
both sides.

| Concept | Rocq [finelt/findom.v](finelt/findom.v), [types.v](finelt/types.v) | Lean `ShapeLogRel.lean` |
|---------|--------------------------------|-------------------------|
| Domain of values | `Raw.elt` (`bot`, `tuniv`, `tpi a f`, `abs f`, `tnat`, `zero`, `succ`, …) | `Shape n` / `ShapeS` (`bot`, `sort rel`, `forallE s f`, `lam f`, `ctor c l`, `indTy`) |
| Function value = graph | `abs : list (elt * elt)` | `lam : List (Shape × Shape)` (`ShapeFun n`) |
| Pi code | `tpi a (f : list (elt*elt))` | `forallE (s : Shape) (f : ShapeFun)` |
| Bottom / trivial fn | `bot`, `singleton`, `nil` | `Shape.bot`, `ShapeFun.bot = [(.bot,.bot)]` |
| Universe code | `tuniv` (single; type-in-type) | `sort (rel : Bool)` + external `SLevel` levels |
| Well-typed value (validity) | `valid : elt -> bool`; membership `wt : elt -> elt -> Prop` | `WShape n = { s : Shape n // s.WF }`; `WShape.HasType : WShape → WShape → Prop` |
| Function-table validity | `valid_fun` | `ShapeFun.WF` / `WShapeFun` |
| Value approximation (eval) | `EvalRel : Tm n -> Env n -> elt -> Prop` | `LE_Interp ρ (m.T) M` (M interpreted above shape `m`) |
| Value PER / def-eq relation | `Val` / `EqVal` (in [finelt/raw_validity.v](finelt/raw_validity.v)) | `LR … .DefEq` (with `.symm`/`.trans`/`.whr`) |
| Adequacy / soundness | `typing_EvalRel`, `conv_EvalRel`, `semantic_typing`, `semantic_conv2` | `LR.adequacy`, `LE_Interp.sound`, `LR.Adequate` |
| WHNF & head reduction | `HeadRed1`/`HeadRed` ([syntax/reduction.v](syntax/reduction.v)), determinacy `HeadRed_tpi_det` | `⤳`/`⤳*` (`WHRedS`), `WHNF`, `WHNF.whRedS` (`SExpr.lean`) |

Notably, both function representations are literally `List (X × X)`, and both
thread a well-formedness condition on values (Rocq `valid`/`wt`, Lean
`WShape.WF`/`WShape.HasType`).

## Where they differ

- **Object language.** Lean targets the **actual Lean 4 kernel** type theory:
  a full predicative universe hierarchy (`SLevel` with `imax`), inductive
  types and constructors (`ctor`, `indTy`), and sorts `Sort u`. Rocq `finelt`
  is a **minimal standalone** dependent type theory: type-in-type
  (`wt tuniv tuniv`), Π types, plus a naturals/`ncase` fragment — no universe
  levels, no general inductives.

- **Sort/universe injectivity.** Because Lean has real universe levels, it
  also proves `sort_inv` (level injectivity, `Sort u ≡ Sort v → u = v`) and
  `sort_forallE_inv` (`Sort u ≢ Π`) by the *same* adequacy machinery. Rocq
  (type-in-type) needs no sort injectivity; its analogous "no confusion"
  facts are `tnat_not_tpi` / `tuniv_not_tpi` (a base code is not a Π), proved
  by the same `piConv`-style head-reduction argument.

- **Stratification vs global fuel.** Lean's shapes are **level-stratified**:
  `Shape : Nat → Type` with `WShape.lift`/`unlift` between levels — the
  adequacy proof threads an explicit level `n`. This matches the *stratified*
  (per-stage) style. Rocq `finelt` instead uses a **single global-fuel** `elt`
  datatype with one stability lemma (`fuel_stable`); its ranks are a
  termination measure rather than a stratification index. (This is the same
  axis on which the Agda `MIN`/`NAT` port and this Rocq port differ — see
  [comparison.md](comparison.md).)

- **Richer shape constructors.** Lean's `ShapeS` carries `ctor`/`indTy` for
  inductive types and keeps `lam` and `forallE` as distinct constructors with
  their own graphs. Rocq's `elt` has `abs`/`tpi` and the primitive naturals,
  but no general inductive machinery.

- **Logical-relation packaging.** Lean's `LR … .DefEq` is presented directly
  as a heterogeneous **definitional-equality** relation closed under whnf
  (`.whr`), symmetry, and transitivity, bundled through `LR.Adequate`. Rocq
  splits this into a unary `Val` and a binary `EqVal` PER (mutually defined,
  recursion on the `wt` derivation), with the semantic layer
  (`semantic_typing`/`semantic_conv2`) on top.

## Bottom line

Modulo the object language (full Lean kernel vs a minimal type-in-type + Π
fragment) and stratified vs global-fuel bookkeeping, the two Pi-injectivity
proofs are the *same proof*: a finite-graph domain model, a logical-relation
adequacy theorem, evaluation of a Pi at the bottom Pi value, and head-reduction
determinacy on the Pi normal form.
