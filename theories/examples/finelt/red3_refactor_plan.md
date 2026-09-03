# `st_case` / `sc_ncase` — Red3-in-`Val` refactor

Status: **DONE.**  The refactor landed, every dependent-`ncase` adequacy case
is proven, and `adequacySub`/`adequacyEqSub` now close with `Qed` (the guard
checker accepts the mutual fixpoint).  This file is kept as the design record.

## What was done

`Val`/`EqVal` now carry Agda's `Red3` (`HeadRed` + `ConvTm`):

- **nat leaves** ([raw_validity.v] `Val`/`EqVal`, `Val_zero`/`Val_succ`/
  `EqVal_zero`/`EqVal_succ`): `conv Γ M <numeral> A`, stated at the `Val`'s
  **type term `A`** (the 4th argument).  That is the whole point: the
  head-expansion step conversion also lives at `A`, so leaf conv and step conv
  `c_trans` with **no retyping**.
- **`ValPi`/`EqValPi`**: `conv Γ A (tpi A0 B0) tuniv`, the Π-code conversion.
  `ValTy`/`EqValTy` are deliberately left **conv-free** (putting it there would
  force retyping the step conv from an abstract type term to `tuniv` in the
  `a = tuniv` head-expansion case, which Coq's `Val` cannot do).
- **`HeadRedVE`/`headred_VE_all`** and its four projections
  (`Val_beta_expand`, `EqVal_headred_expand`, `Val_headred_contract`,
  `EqVal_headred_contract`) each take the step conversion `conv Γ M0 M T`
  (**same orientation for expand and contract**: new ≡ old).  The Π-edge
  transports (`ValPiExp`/`ValPiCon`/`EqValPiExp`/`EqValPiCon`) build the
  per-edge `c_app1` congruence from the domain/codomain typings read off the
  `ValTy` of the type term (new helper `ValTy_tpi_typings`, mirroring Agda's
  `ValPi2-headred-contract`) plus the step conv retyped through the stored
  `CT`.  The cross (`PiAppEq`) direction retypes the second app-conv to the
  shared codomain `B0[N1..]` via `conv_subst_arg`.

### The wall the old plan missed

`fwd_per_all`'s `FWD`/`EFWD` (type transport of `Val`/`EqVal` along
`EqValTy`) breaks at the **nat leaves**: the leaf conv is stated at the type
term, so moving `Val M A` to `Val M B` needs `conv Γ A B tuniv` — and
`EqValTy` is `True` at the `tnat` code, so it carries nothing.  Fix: the two
transport conjuncts of `FwdPER` (hence `Val_EqVal_fwd`/`EqVal_EqVal_fwd`) now
take `conv Γ A B tuniv` as an **extra hypothesis**.  Every caller already has
it (`st_conv`/`sc_conv` from `substitution_conv`; the Π-edge callers from
`subst_conv_cross`/`conv_subst1`).  Alternatives considered and rejected:
putting the conv in `EqValTy`'s base cases (breaks `ValTy_EqValTy`, which has
no typing at base codes) and stating the leaf conv at literal `Core.tnat`
(breaks head-expansion, whose step conv is at the type term).

### New reusable helpers (adequacy.v)

- `subst_dom_typing` / `subst_cod_typing` — `A[σ]` / `B[⇑σ]` typings.
- `beta_step_conv` — the `c_beta` step conv for the lambda edges, generalised
  over an annotation `Alam` only *convertible* to the Π-domain (needed by the
  off-diagonal `sc_abs` edge).
- `conv_subst1` (raw_validity.v) — instantiate a codomain conv at an argument.
- `compatible_zero_le`, `rho_subst_comm`.
- `red1_conv` — head reduction ⊆ conversion for well-typed terms (post-
  adequacy, since its β case needs Π-injectivity).  Used by `subject_red1`.

`st_abs`, `st_abs_Val_edge`, `st_abs_EqVal_edge` gained syntactic body-typing
hypotheses (`typing (Γ++A) M B`), which `c_beta` needs.

## `st_case_Val_zero` (proven) — the template

1. Scrutinee IH at value code `zero` ⇒ `HeadRed M[σ] zero` **and**
   `cvM : conv Δ M[σ] zero tnat`  ← the payoff.
2. `EvalRel_subst1_forward` on `evT : EvalRel T[M..] ρ a` gives some `v'` with
   `EvalRel M ρ v'`; `EvalRel_compatible` + `compatible_zero_le` gives
   `le v' zero`, so `EvalRel_mono_env` lands `EvalRel T (zero .: ρ) a`, and
   `EvalRel_subst1_backwards` gives `EvalRel T[zero..] ρ a`.
3. Branch IH ⇒ `Val RB Δ M0[σ] (T[zero..])[σ] WT`.
4. Motive transport: instantiate the **motive's own** `semantic_typing` at the
   two substitutions `zero .: σ` and `M[σ] .: σ` (`ValSub`/`EqValSub` heads
   built from the scrutinee's `Val` and a hand-built `zero` leaf) ⇒
   `EqValTy` between `T[zero .: σ]` and `T[M[σ] .: σ]`; the matching syntactic
   conv is `subst_conv_cross TT`.  **No `adequacyEqSub`, so no circularity.**
5. `Val_EqVal_fwd` (with that conv) retypes the branch's `Val` to the goal
   motive; `Val_beta_expand` head-expands `(ncase M M0 M1)[σ] ↠ M0[σ]` with
   step conv `c_trans (c_ncase …) (c_conv (c_ncase_Z …) …)`.

## The successor case (proven)

`st_case_Val_succ` / `st_case_EqVal_succ`.  Two things differ from the zero
branch:

- **Joining the scrutinee value.**  `compatible (succ v) w` does *not* imply
  `le w (succ v)` (`succ bot` and `succ zero` are compatible yet unordered), so
  `compatible_zero_le` has no analogue.  Instead `EvalRel_compatible_lub` gives
  `EvalRel M ρ (lub (succ vp) v')`, and `le_succ_inv` shows that join is
  `succ vpp` with `le vp vpp`; the motive is instantiated at `succ vpp .: ρ` and
  the branch's evaluation is pushed up by `EvalRel_mono_env`.  The motive at the
  `rho`-shifted branch type comes from `EvalRel_subst` along
  `SubRel rho (succ vpp .: ρ) (vpp .: ρ)`, and
  `(T[rho])[P .: σ] = T[succ P .: σ]` is `rho_subst_cons`.
- **The predecessor term.**  The substitution head is the predecessor *term*
  `P` from the scrutinee's `Val_succ`, not the image of any `Γ`-term.  Its
  `ValSub`/`EqValSub` obligations are discharged **without** `restrictVal`: at
  the code `succ u0` re-run the scrutinee's IH and identify the predecessor with
  `HeadRed_succ_det`; at `succ vpp` head-*contract* the scrutinee's own
  `Val`/`EqVal` along `HeadRed M[σ] (succ P)` (which needs the `Red3`
  conversion).

### A second gap found here, and its fix

The cross conjunct reduces its two sides to the branch at **different**
predecessor terms `P` (from `M[σ]`) and `P'` (from `M[σ']`), so the branch IH
runs at `P .: σ` / `P' .: σ'` and needs a *syntactic* `conv Δ P P' tnat` for the
`ConvSub`.  Conversion has no successor-injectivity rule, so that is **not**
derivable from `conv Δ (succ P) (succ P') tnat`.  Fix: `EqVal`'s successor leaf
now also stores `conv Γ M1 N1 Core.tnat` (the predecessors' conversion).
Constructible at every creation site: `c_refl` via `typing_succ_arg_inv` for the
diagonal `Val_EqVal`, `subst_conv_cross` in `st_succ`, `substitution_conv` in
`sc_succ`; carried, flipped or composed everywhere else.

## What it took, end to end

- `st_case_Val_zero` / `st_case_Val_succ` / `st_case_Val` — the `Val` conjunct.
- `st_case_EqVal_zero` / `st_case_EqVal_succ` / `st_case_EqVal` — the cross
  conjunct.  The σ'-side step conversion is retyped to the shared motive
  `T[⇑σ][M[σ]..]` by the cross-substitution conversion `cvTx`.
- `st_case` — the two conjuncts assembled; dispatches on the `ncase` semantics
  (`bot` / `zero` / successor).
- `sc_ncase_Z` / `sc_ncase_S` — the ι-rules, in the shape of `sc_beta`: take the
  redex's reflexive `EqVal` (via `st_case`) and contract the second side along
  `hr_zero` / `hr_succ` with the `c_ncase_Z` / `c_ncase_S` step conversion.
- `sc_ncase_zero` / `sc_ncase_succ` / `sc_ncase` — the congruence.  Both step
  conversions on the right are obtained from the *whole* congruence conversion
  rather than rebuilt: `ncase M' M0' M1' ≡ ncase M M0 M1 ≡ <branch> ≡ <branch'>`.

### A third gap: the congruence's successor case

The two sides of the congruence reduce to the successor branch at **different**
predecessor terms, `P` (from `M[σ]`) and `P'` (from `M'[σ]`).  Relating
`M1[P .: σ]` to `M1'[P' .: σ]` needs one term under two substitutions, i.e.
`semantic_typing`'s cross conjunct — but `c_ncase`'s premises were all
conversions, and the single-substitution `semantic_conv2` cannot supply it.
Going through `conv_typing` breaks guardedness of the adequacy fixpoint.

Agda sidesteps this: in `NAT/Syntax/Typing.agda`, `conv-Case-dep`'s successor
branch is a *function* `b : Π ℕ (subSucC C)`, so `Case M a b` reduces to
`App b P` and the differing arguments are absorbed by the Π-edge machinery
(`PiAppEq`).  The Coq syntax makes `M1` a binder-term in `Γ ++ tnat`, which has
no argument-variation semantics.

Fix (chosen 2026-09-03): `c_ncase` carries `typing (Γ++tnat) M1' T[rho]`.  It is
admissible (`conv_typing` derives it), so the conversion relation is unchanged,
and it mirrors `c_abs`, which already carries typings for both bodies.  The
branch relation is then composed in two steps through `M1'[P .: σ]`:

    M1[P .: σ]  ≈ M1'[P .: σ]    (branch conversion at P .: σ)
    M1'[P .: σ] ≈ M1'[P' .: σ]   (semantic_typing M1' at the two
                                  substitutions, related by conv P P')

joined by `EqVal_trans`.  The `conv Δ P P' tnat` in the second step is the
predecessor conversion stored in `EqVal`'s successor leaf.

## What `adequacySub` rests on

`prop_ext`, `functional_extensionality_dep`, `eq_rect_eq`, `proof_irrelevance`,
and six admitted lemmas *below* adequacy:

- [../syntax/typing.v]: `renaming_typing`, `renaming_conv`, `substitution_tm`,
  `substitution_conv`, `conv_typing` — 16 `admit`s, all the mechanical `ncase`
  cases (`asimpl`-wrangling `T[M..]` under a substitution).
- [typing_semantics.v]: `typing_EvalRel`, `conv_EvalRel` — tactically complete,
  blocked only on the guard checker (the `c_ncase` case calls `typing_EvalRel`
  on a locally built derivation, so a size measure is needed).

`HeadRed1_det` ([../syntax/reduction.v]) is no longer in `adequacySub`'s cone,
but `piInjectivity` and `subject_red` still use it.