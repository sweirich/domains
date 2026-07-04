# Rocq vs Agda vs Lean — syntactic type system and logical relation

A three-way comparison of the dependent-type-theory metatheory developments in

- **Rocq** — this repository, `theories/examples/finelt/` + `theories/examples/syntax/`;
- **Agda** — `~/github/agda/domain-semantics/{MIN,NAT}/` (the reference this Rocq
  dev is ported from);
- **Lean** — `~/github/lean/lean4lean/Lean4Lean/Experimental/` (the "shape"
  logical relation inside [Lean4Lean](https://github.com/digama0/lean4lean)).

All three prove metatheoretic results (canonicity/normalization-style facts,
**Pi injectivity**, consistency) for a dependent type theory by building a
**finite-element / domain-theoretic logical relation**: values are finite
approximations, functions are finite input→output *graphs*, and the relation is
an ideal closed under head reduction. See [comparison.md](comparison.md) for the
detailed Rocq↔Agda map and [lean_comparison.md](lean_comparison.md) for the
Rocq↔Lean Pi-injectivity comparison; this file focuses on comparing, across all
three, (1) the **syntactic type system** and (2) the **logical relation**.

## Scope and provenance

| | Rocq `finelt` | Agda `MIN`/`NAT` | Lean `Lean4Lean` |
|--|--|--|--|
| Object theory | minimal: type-in-type (`wt tuniv tuniv`), Π, naturals (`ncase`) | minimal: Π + U (MIN); + naturals `Case`/`Y` (NAT) | the **actual Lean 4 kernel**: predicative universes, Π, inductives, definitional unfolding, proof irrelevance |
| Universes | single `tuniv` (type-in-type) | single `U` (type-in-type) | full hierarchy `SLevel` with `imax`, `Sort u` |
| Purpose | port/experiment | reference formalization | verified Lean kernel |

## File-by-file correspondence

Corresponding source files across the three developments. Roots: Rocq
`theories/examples/`, Agda `~/github/agda/domain-semantics/{MIN,NAT}/`, Lean
`~/github/lean/lean4lean/Lean4Lean/Experimental/`. The granularity differs — Agda
splits into many small modules, Lean packs the whole model into three files — so
several rows are one-to-many.

| | Rocq | Agda | Lean |
|--|--|--|--|
| Raw syntax + substitution | `syntax/syntax.v` | `Syntax/Raw.agda`, `Syntax/Substitution.agda` | `SExpr.lean` |
| Typing & conversion | `syntax/typing.v` | `Syntax/Typing.agda` | `SExpr.lean` |
| Reduction | `syntax/reduction.v`, `syntax/relations.v` | `Syntax/Reduction.agda` | `SExpr.lean` |
| Value domain | `finelt/findom.v` | `Domain/Basic.agda`, `Domain/Order*.agda`, `Domain/Rank.agda` | `ShapeLogRel.lean` |
| Membership | `finelt/types.v` | `Domain/Membership.agda`, `Domain/Mem*.agda` | `ShapeLogRel.lean` |
| Selection | `finelt/selection.v` | `Model/Selection.agda`, `Model/SelectionRank.agda` | `ShapeLogRel.lean` |
| Evaluation relation | `finelt/raw_semantics.v` | `Model/Eval.agda` | `ShapeLogRel.lean` |
| Evaluation ∘ substitution | `finelt/eval_substitution.v` | `Model/EvalSubstitution.agda` | `ShapeLogRel.lean` |
| Typed PER | `finelt/raw_validity.v` | `Validity/*.agda` | `ShapeLogRel.lean` |
| Soundness | `finelt/typing_semantics.v` | `Model/Soundness.agda`, `Model/SoundnessLemmas.agda` | `ShapeLogRelAdequacy.lean` |
| Adequacy | `finelt/adequacy.v` | `Adequacy/*.agda` (`Adequacy/Bundle.agda`) | `ShapeLogRelAdequacy.lean` |
| Pi injectivity | `finelt/adequacy.v` | `PiInjectivity.agda` | `ShapeLogRelAdequacy.lean` |
| Subject reduction | `finelt/adequacy.v` | `SubjectReduction.agda` | — |
| Utilities | `finelt/utils.v`, `theories/utils/` | `Domain/Kernel.agda` | (Lean4Lean core) |

---

# Part 1 — the syntactic type system

## 1.1 Terms

| | Rocq [syntax/syntax.v](syntax/syntax.v) `Tm` | Agda `Syntax/Raw.agda` `Expr` | Lean `SExpr.lean` `SExpr` |
|--|--|--|--|
| variables | `var : fin n → Tm n` (intrinsically scoped) | `Var : Fin n → Expr n` (intrinsically scoped) | `bvar : Nat → SExpr` (de Bruijn, extrinsic scope) |
| universe | `tuniv` | `U` | `sort : SLevel → SExpr` |
| Π | `tpi : Tm n → Tm (S n) → Tm n` | `Pi : Expr n → Expr (suc n) → Expr n` | `forallE : SExpr → SExpr → SExpr` |
| λ | `abs : Tm n → Tm (S n) → Tm n` | `Lam : Expr n → Expr (suc n) → Expr n` | `lam : SExpr → SExpr → SExpr` |
| app | `app : Tm n → Tm n → Tm n` | `App : Expr n → Expr n → Expr n` | `app : SExpr → SExpr → SExpr` |
| naturals | `tnat`, `zero`, `succ`, `ncase M M0 M1` | `NatT`, `Zero`, `Suc`, `Case M a b`, `Y g` | (inductives, general) `const c ls` |
| other | — | — | `const : Name → List SLevel → SExpr` (constants/inductives) |

- Rocq and Agda are **intrinsically scoped** (`Tm n` / `Expr n`), so terms are
  well-scoped by construction and substitution is total. Lean's `SExpr` is
  **untyped/unscoped** (`bvar : Nat`) with scoping enforced by the judgments.
- Rocq mechanizes substitution/renaming Autosubst-style ([syntax/syntax.v](syntax/syntax.v));
  Agda hand-rolls it (`Syntax/Substitution.agda`); Lean defines `inst`/`lift`/`subst`
  on the raw `SExpr` (`SExpr.lean`).
- Naturals: Rocq uses a **case combinator** `ncase` (recently migrated from a
  recursor `nrec`); Agda-`NAT` uses `Case` + a fixpoint `Y`; Lean subsumes
  naturals under **general inductive types** (`const`/`indTy`).

## 1.2 The typing and conversion judgments — the big structural split

This is where the three differ most.

**Rocq** and **Agda** keep **two separate judgments**: a typing relation and a
conversion (definitional-equality) relation, mutually defined.

```coq
(* Rocq: theories/examples/syntax/typing.v — mutual Inductive *)
Inductive typing : ∀ {n}, Ctx n → Tm n → Tm n → Prop := …   (* Γ ⊢ M ∈ A *)
with       conv   : ∀ {n}, Ctx n → Tm n → Tm n → Tm n → Prop := …   (* Γ ⊢ M ≡ N ∈ A *)
with       ctx    : ∀ {n}, Ctx n → Prop := …
```
```agda
-- Agda: Syntax/Typing.agda
data HasType : Ctx n → Expr n → Expr n → Set where …   -- Γ ⊢ M : A
data ConvTm  : Ctx n → Expr n → Expr n → Expr n → Set where …   -- Γ ⊢ M ≡ N : A
```

**Lean** uses **one** relation: *typed definitional equality* `IsDefEq Γ e e' A`,
with typing recovered as the **reflexive diagonal**:

```lean
-- Lean: SExpr.lean
notation Γ " ⊢ " e " : " A     => IsDefEq Γ e e A      -- typing = self-equality
notation Γ " ⊢ " e1 " ≡ " e2 " : " A => IsDefEq Γ e1 e2 A
inductive IsDefEq : List SExpr → SExpr → SExpr → SExpr → Prop where
  | bvar   : Lookup Γ i A → Γ ⊢ .bvar i : A
  | symm   | trans | trans'                              -- PER structure
  | sort   : Γ ⊢ .sort l : .sort (.succ l)
  | appDF  | lamDF | forallEDF                           -- congruence rules
  | defeqDF: Γ ⊢ A ≡ B : .sort u → Γ ⊢ e1 ≡ e2 : A → Γ ⊢ e1 ≡ e2 : B   -- conversion
  | beta   | eta | proofIrrel | const | extra            -- computation/unfolding
```

Consequences of the split:

| | Rocq | Agda | Lean |
|--|--|--|--|
| primitive | typing, with conversion beside it | typing, with conversion beside it | **typed equality** (one relation) |
| typing is… | its own inductive | its own inductive | `IsDefEq Γ e e A` (diagonal) |
| congruence | `c_app1`/`c_app2`, `c_abs`, `c_tpi` | `conv-App-fun`/`-arg`, `conv-Pi`, (Lam via funext) | `appDF`, `lamDF`, `forallEDF` (one rule each, both sides move) |
| β / η | `c_beta` / `c_eta` | `conv-beta` / `conv-funext` | `beta` / `eta` |
| conversion rule | `t_conv` (typing) + `c_conv` | `ty-conv` + `conv-conv` | `defeqDF` |
| extras | — | — | `proofIrrel`, `const`, `extra` (δ/defeq unfolding) |

The Lean presentation is the **"PER over syntax" / typed-equality** style
(Abel–Coquand–style), which is why its congruence rules (`lamDF`, `forallEDF`)
move *both* sides simultaneously. Rocq/Agda instead derive equality from a
typing judgment plus a separate congruence closure. A visible symptom: Rocq
keeps an explicit `c_abs` (λ-congruence) rule while Agda derives it from
`conv-funext`; Lean has `lamDF` directly.

## 1.3 Reduction

| | Rocq | Agda | Lean |
|--|--|--|--|
| head reduction | `HeadRed1`/`HeadRed` ([syntax/reduction.v](syntax/reduction.v)) | `HeadRed1`/`HeadRed` (`Syntax/Reduction.agda`) | `⤳` / `⤳*` (`WHRedS`, SExpr.lean) |
| β rule | `hr_beta` | `headred-beta` | (kernel whnf) |
| nat rules | `hr_zero`/`hr_succ`/`hr_case` | `headred-case-zero/-suc/-case`, `headred-Y` | (ι-reduction, general) |
| WHNF | Π/base are `HeadRed1`-normal | likewise | `WHNF Γ e := ∀ e', ¬ Γ ⊢ e ⤳ e'` |
| **Π determinacy** | `HeadRed_tpi_det` | `HeadRed-unique-Pi` / `HeadRed-strip-Pi` | `WHNF.forallE.whRedS` |

All three isolate the same fact used at the end of Pi injectivity: **a Π type
is a (weak-)head normal form, so a reduction sequence out of it is trivial.**

---

# Part 2 — the logical relation

Each development interprets terms into a **finite-element domain** and proves an
**adequacy/soundness** theorem connecting the syntactic judgments to the model.
The domain and the relation line up closely across all three.

## 2.1 The value domain (finite elements / shapes)

A *function value is a finite list of input→output pairs*; Π and λ carry such a
graph; there is a least element `bot`.

| | Rocq [findom.v](finelt/findom.v) `elt` | Agda `Domain/Basic.agda` `FinEl` | Lean `ShapeLogRel.lean` `Shape n` |
|--|--|--|--|
| bottom | `bot` | `Bot` | `Shape.bot` |
| universe code | `tuniv` | `UCode` | `sort (rel : Bool)` |
| Π code | `tpi a (f : list (elt*elt))` | `PiCode a (f : FinFun)` | `forallE s (f : ShapeFun n)` |
| λ value | `abs (f : list (elt*elt))` | `FunEl (f : FinFun)` | `lam (f : ShapeFun n)` |
| function graph | `list (elt * elt)` | `FinFun = List (Pair FinEl FinEl)` | `ShapeFun n = List (Shape n × Shape n)` |
| nat codes | `tnat`, `zero`, `succ` | `NatCode`, `ZeroEl`, `SucEl` (NAT) | `ctor`/`indTy` (general) |
| trivial function | `nil` / `singleton` | `[(Bot,Bot)]`-style | `ShapeFun.bot = [(.bot,.bot)]` |
| well-formed value | `valid : elt → bool` (side condition) | `Coherent`/`FinMem` side conditions | `WShape n = {s : Shape n // s.WF}` |
| membership / "wt" | `wt : elt → elt → Prop` ([types.v](finelt/types.v)) | `FinMem : FinEl → FinEl → Set` | `WShape.HasType : WShape → WShape → Prop` |
| order | `le : elt → elt → bool` | `LeCode` (Set) + `leFinEl` (Nat) | `≤` on `Shape`/`WShape` |
| join | `lub : elt → elt → elt` | `Sup : FinEl → FinEl → FinEl` | (join on shapes) |
| apply graph | `app : list(elt*elt) → elt → elt` | `EvalFun : FinFun → FinEl → FinEl` | `WShapeFun.app` |
| **stratification** | single global-fuel `elt`; rank is a *measure* | stage-indexed (`MemStage`, `Stage`) | **level-indexed** `Shape : Nat → Type` with `lift`/`unlift` |

All three represent functions the same way — as a graph `List (X × X)` — and
thread a well-formedness condition on values (Rocq `valid`, Agda
`Coherent`/`FinMem`, Lean `WShape.WF`).

The main *domain* difference is **stratification**: Agda (`Stage`) and Lean
(`Shape : Nat → Type`) index the domain by a level/stage and thread `lift`/`shift`
lemmas; Rocq uses a **single** `elt` with global fuel and one stability lemma
(`fuel_stable`). So on this axis **Rocq is the outlier**; Agda and Lean agree.

## 2.2 Evaluation / approximation relation

The heart of each LR is a relation "term `M` is approximated by value `m` in
environment `ρ`", defined by recursion on the term. Compare the clauses:

**Rocq** — `EvalRel : Tm n → Env n → elt → Prop` ([raw_semantics.v](finelt/raw_semantics.v)):
```coq
EvalRel (var i)   ρ b := valid b ∧ le b (ρ i)
EvalRel tuniv     ρ b := le b tuniv
EvalRel (app M N) ρ b := ~is_bot b → ∃ a, EvalRel M ρ (a ↦ b) ∧ EvalRel N ρ a
EvalRel (tpi A B) ρ b := match b with tpi a g => valid a ∧ valid_fun g ∧
     EvalRel A ρ a ∧ ∃ a', EvalRel A ρ a' ∧ EvalRel_fun B ρ a' g | … end
EvalRel (abs A M) ρ b := match b with abs g => … ∧ EvalRel_fun M ρ a g | … end
```

**Lean** — `LE_Interp : Valuation → TShape → SExpr → Prop` (`ShapeLogRel.lean`):
```lean
| bot     : LE_Interp ρ (WShape.bot.T) M                       -- ⊥ approximates all
| bvar    : m ≤ ρ i → LE_Interp ρ m (.bvar i)
| sort    : m ≤ .sort (l ≠ .zero) → LE_Interp ρ m (.sort l)
| app     : LE_Interp ρ f.T F → LE_Interp ρ a.T A → m ≤ (f.app a).T
          → LE_Interp ρ m (.app F A)
| lam     : LE_Interp ρ a.T A → WShape.HasDom f a
          → (∀ x, x.HasType a → LE_Interp (ρ.push x.T) (f.app x).T F)
          → m ≤ (.lam' f).T → LE_Interp ρ m (.lam A F)
| forallE : LE_Interp ρ b.T B → … → WShape.HasDom f b'
          → (∀ x, x.HasType b' → LE_Interp (ρ.push x.T) (f.app x).T F)
          → m ≤ (.forallE b f).T → LE_Interp ρ m (.forallE B F)
```

**Agda** — `EvalRel : Expr n → EnvApprox n → FinEl → Set` (`Model/Eval.agda`):
```agda
EvalRel (Var i) ρ b   = Coherent b × LeCode b (lookup i ρ)
EvalRel (App M N) ρ b = Σ v, EvalRel N ρ v × EvalRel M ρ (FunEl [(v,b)])
EvalRel (Lam A M) ρ b = Σ a, CoherentFun … × (∀ u v, Selection g u v →
     Σ x, LeCode x u × FinMem x a × EvalRel M (extend ρ x) v)
EvalRel (Pi A B)  ρ b = Coherent b × EvalRel A ρ a × (Σ a', EvalRel A ρ a' × …)
```

Clause-by-clause these are **the same relation**:

| clause | Rocq | Agda | Lean |
|--|--|--|--|
| variable | `valid b ∧ le b (ρ i)` | `Coherent b × LeCode b (ρ i)` | `m ≤ ρ i` |
| universe | `le b tuniv` | `Coherent b × LeCode b UCode` | `m ≤ .sort _` |
| application (singleton) | `∃ a, EvalRel M ρ (a ↦ b) ∧ EvalRel N ρ a` | `Σ v, EvalRel N ρ v × EvalRel M ρ (FunEl [(v,b)])` | `LE_Interp ρ f.T F ∧ … ∧ m ≤ (f.app a).T` |
| λ (edgewise over the graph) | `EvalRel_fun M ρ a g` (∀ edge, body evaluates in extended env) | `∀ u v, Selection g u v → … EvalRel M (extend ρ x) v` | `∀ x, x.HasType a → LE_Interp (ρ.push x.T) (f.app x).T F` |
| Π (domain + edgewise codomain) | `EvalRel A ρ a ∧ EvalRel_fun B ρ a' g` | `EvalRel A ρ a × …` | `LE_Interp ρ b.T B ∧ (∀ x, … LE_Interp (ρ.push x.T) (f.app x).T F)` |
| bottom | `EvalRel M ρ bot` (lemma `EvalRel_bot`) | `EvalRel-Bot` | `LE_Interp.bot` (constructor) |

The shared shape is: **application picks out a single edge** of the function
graph (`a ↦ b` / `FunEl [(v,b)]` / `f.app a`), and **λ/Π quantify over every
input `x` in the domain**, running the body in the environment extended by `x`.
The differences are cosmetic: Lean folds `bot`-approximation in as a
*constructor* (`LE_Interp.bot`) and phrases everything with an explicit order
`m ≤ …`; Rocq/Agda make `EvalRel _ ρ bot` a *derived* fact and inline the order
via `le`/`LeCode`. Agda mediates the λ-edges through an explicit `Selection`;
Rocq bundles that into `EvalRel_fun`; Lean via `WShape.HasDom`/`f.app`.

## 2.3 The typed PER (definitional-equality relation)

On top of evaluation, each builds a **partial equivalence relation on terms**
indexed by a type, closed under head reduction — the semantic counterpart of the
syntactic `≡`.

| | Rocq [raw_validity.v](finelt/raw_validity.v) | Agda `Validity/Core.agda` | Lean `ShapeLogRel.lean` |
|--|--|--|--|
| unary | `Val M A (h : wt u a)` | `Val2` | (diagonal of `LR.DefEq`) |
| binary | `EqVal M N A h` | `EqVal2` | `LR … .DefEq M N A m a` |
| type-level | `ValTy`/`EqValTy` | `ValTy2`/`EqValTy2` | `LR` at a sort |
| recursion on | the **`wt` derivation** (Fixpoint on `h`) | a **stage index** | level `n` / structural |
| closure | head-red expand/contract, sym, trans, sup, up/down/restrict | same (`Validity/*`) | `.whr` (whnf closure), `.symm`, `.trans` |
| Π-edge preds | `PiEdgeVal`/`PiAppVal`/`ValPi` | `PiEdgeVal2`/`PiAppVal2`/`ValPi2` | folded into `LR.forallE'` |

All three are PERs closed under weak-head reduction. The presentations differ in
what they recurse on: Rocq on the **membership derivation** `wt u a`, Agda on a
**stage** index, Lean on the shape **level** `n`. Lean, again like Agda, is
level-stratified; Rocq is the derivation-recursive/global-fuel outlier.

## 2.4 Adequacy and Pi injectivity

Each proves a fundamental **adequacy** theorem (the syntactic judgments imply the
LR), then reads off metatheory.

| | Rocq | Agda | Lean |
|--|--|--|--|
| soundness of typing | `typing_EvalRel` | `theorem1` (`Model/Soundness.agda`) | (typing = diagonal of `LR.adequacy`) |
| soundness of conv | `conv_EvalRel` | `convSound'` | `LR.adequacy` (on `IsDefEq`) |
| semantic judgments | `semantic_typing`/`semantic_conv2` | `AdqV2`/`AdqE2` (`Adequacy/Bundle.agda`) | `LR.Adequate` |
| "trivial Π value" | `evalRel_Pi_trivial : EvalRel (tpi B1 F1) ρ (tpi bot nil)` | `evalRel-Pi-trivial` | `LE_Interp … (forallE .bot [(.bot,.bot)]) (.forallE B₁ F₁)` |
| reduce-to-Π | `piConv` | `piConv`/`convPi2` | `forallE_whRed_l` |
| **Pi injectivity** | `piInjectivity` | `piInjectivity` | `forallE_inv` |
| finish | `HeadRed_tpi_det` | `HeadRed-unique-Pi` | `WHNF.forallE.whRedS` |

The Pi-injectivity endgame is identical in all three (see
[lean_comparison.md](lean_comparison.md) for the step-by-step): interpret the
known Π at the **bottom Π value** (domain `⊥`, graph `[(⊥,⊥)]`), transport along
the conversion via adequacy, obtain a head reduction of the other side to a Π,
and close by Π head-normal-form determinacy.

---

## Summary of the essential differences

1. **One judgment vs two.** Lean makes *typed definitional equality* (`IsDefEq`)
   primitive, with typing as its diagonal; Rocq and Agda keep *typing* and
   *conversion* as separate (mutually inductive) relations. This changes the
   shape of the congruence/β/η rules but not the models.

2. **Object theory.** Lean models the full Lean 4 kernel (universe levels,
   inductives, δ-unfolding, proof irrelevance); Rocq and Agda model a minimal
   type-in-type + Π (+ naturals) calculus. Hence Lean additionally needs
   `sort_inv` (level injectivity) and `sort_forallE_inv`; Rocq/Agda only need
   base "no-confusion" facts (`tnat_not_tpi`, `tuniv_not_tpi`).

3. **Stratification.** Agda (`Stage`) and Lean (`Shape : Nat → Type`) index the
   value domain and the PER by a level/stage and carry `lift`/`shift` lemmas.
   Rocq uses a **single** global-fuel `elt` with one stability lemma. On this
   axis Rocq is the outlier and Agda/Lean agree.

4. **Everything else is shared.** All three use a finite-graph value domain
   (`List (X × X)` for functions), the *same* evaluation relation shape
   (single-edge application, edgewise λ/Π over the domain), a whnf-closed typed
   PER, an adequacy theorem, and the identical bottom-Π trick for Pi
   injectivity.

The correspondence above is of **definitions and proof architecture**.
