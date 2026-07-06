# Red3 refactor plan — conv-carrying reductions in `Val`/`EqVal`

Status: **planned, not started.** Goal: unblock `adequacy.v` `st_case`,
`sc_ncase_Z/S/cong` (dependent `ncase` eliminator adequacy).

## Why (the blocker)

`st_case` must transport `Val`/`EqVal` for the result type `T[M..]` between the
branch type (`T[zero..]` / `T[rho]`) and `T[M..]`. `EqValTy`'s definition
([raw_validity.v](raw_validity.v) ~L231) intrinsically bundles the *syntactic*
conversions between the two pi-reducts, so the transport needs
`conv M[σ] ≡ numeral` at `tnat`.

After substitution `M[σ]` *does* head-reduce to its numeral (the scrutinee's
`Val` gives `HeadRed M[σ] zero`), but `HeadRed → conv` (`red1_conv`) has a
β-case that needs Pi-injectivity → `adequacyEqSub` → the whole adequacy
Fixpoint, of which `st_case` is a *building block*. **Circular.**

Agda escapes this because its reductions carry `Red3` = `HeadRed` **+**
`ConvTm`, bundled *everywhere*, so `motiveEqValTy2` reads the conversion off the
scrutinee's `Val`. Coq's `Val` at `tnat` is bare `HeadRed`
([raw_validity.v](raw_validity.v) ~L317).

**Confirmed empirically (2026-07-06):** bundling `conv` into only the `tnat`
leaves of `Val`/`EqVal` compiles the unfolding lemmas + `Val_EqVal` +
`EqVal_Val1/2`, but **dies at `headred_VE_all`** (~L770): Val head-*expansion*
for `zero` must produce `conv M0 zero` from `conv M zero` + `HeadRed M0 M`,
i.e. `conv M0 M` from `HeadRed M0 M` = `red⊆conv` again. So leaf-only bundling
is insufficient; conversions must thread through the whole head-expansion layer.

## Design

Introduce a conv-carrying reduction and thread it through the model's
head-reduction machinery.

```coq
(* "M reduces to N and is convertible to it at A" — Agda Red3. *)
Record Red {n} (Γ : Ctx n) (M N A : Tm n) : Prop := mkRed
  { red_hr : HeadRed M N ; red_ct : conv Γ M N A }.
```

- `Val` at `tnat`: `zero => Red Γ M Core.zero Core.tnat`;
  `succ v => exists M1, Red Γ M (succ M1) Core.tnat /\ Val k Γ M1 tnat _`.
- `EqVal` at `tnat`: both sides carry a `Red`.
- `Red` is closed under: reflexivity (`ms_refl` + `c_refl`), transitivity
  (`ms_trans` + `c_trans`), and the head-reduction *rules that are also conv
  rules* — `hr_beta`↦`c_beta`, `hr_app`↦`c_app1`, `hr_zero`↦`c_ncase_Z`,
  `hr_succ`↦`c_ncase_S`, `hr_case`↦`c_ncase`. Each such closure lemma takes the
  typing premises the conv rule needs (available locally at every use site).

The key discipline: **head-EXPANSION never manufactures a conversion generically**
— every `*_headred_expand` / `Val_beta_expand` caller *supplies* the step-`Red`
(built from local typings via the rule map above). This is what breaks the
circularity: no global `red⊆conv` is ever invoked.

## Work breakdown (ordered; each phase should re-green before the next where possible)

1. **`syntax/`-adjacent Red infrastructure** (new, in `adequacy.v` or a new
   `red3.v` to avoid touching `syntax/`):
   - `Red` record + `Red_refl`, `Red_trans`.
   - `Red_ncase` (scrutinee congruence, conv via `c_ncase`), `Red_app`
     (`c_app1`), plus `Red_beta`/`Red_zero`/`Red_succ` builders.
   - `typing_ncase_inv` (missing today) — needed by any `HeadRed→conv` and by
     `subject_red1` t_case.

2. **`raw_validity.v` definition change**: bundle `Red` into `Val`/`EqVal`
   `tnat` leaves; update `Val_zero`/`Val_succ`/`EqVal_zero`/`EqVal_succ`
   unfolding lemmas. (Done experimentally; ~4 lemmas + 2 defs.)

3. **`raw_validity.v` projections/diagonal** (mechanical, done experimentally):
   `Val_EqVal`, `EqVal_Val1`, `EqVal_Val2`.

4. **`raw_validity.v` head-expansion machinery** (the hard core):
   `headred_VE_all` (`HeadRedVE`), `Val_beta_expand`, `EqVal_headred_expand`,
   `Val_headred_contract`, `EqVal_headred_contract`, `ValTy_headred_*`,
   `EqValTy_headred_*`, `ValPi/EqValPi_headred_*`. Convert the *expansion*
   directions to take a step-`Red` argument; contract directions likewise take
   the step-`Red`. Congruence recursions (app) build the sub-step `Red` via
   `Red_app`/`c_app1`.

5. **`raw_validity.v` fuel/transport** (`fuel_stable`, `Val_fuel_down_to`,
   `EqVal_fuel_down_to`, `Val_app_transport`, `EqVal_app_transport`): the `Red`
   conjunct is fuel-independent; update the `tnat`-case match patterns only.

6. **`adequacy.v` construction sites**: `st_var`, `st_zero`, `st_succ`,
   `st_app`, `st_conv` — supply the `Red` (usually `Red_refl` or a `c_beta`
   step). `st_nat/st_univ/st_tpi/st_abs` produce non-`tnat` values → untouched.

7. **`adequacy.v` `st_case`** (the payoff): scrutinee `Red M[σ] numeral`
   (off `SM`'s `Val`) → `conv_subst_arg` → `conv (T[numeral..])[σ] ≡ (T[M..])[σ]`
   → `adequacyEqSub` → `EqValTy` → `Val_EqVal_fwd`/`EqVal_EqVal_fwd` transport;
   head-expand `ncase[σ] → branch` with the `c_ncase_*` step-`Red`
   (`Val_beta_expand` given the supplied `Red`). Succ branch instantiates `M1`
   at `(v.:ρ)` with the `rho` identity `T[rho][P..] = T[(succ P)..]`.

8. **`adequacy.v` `sc_ncase_Z/S/cong`**: same engine on the `EqVal`/cross side.

9. **Bonus once `Red3`/`typing_ncase_inv` exist**: `subject_red1` t_case
   (hr_case uses `red1_conv`/`Red`), independently.

## Risk / rollback

- Phases 2–5 leave `raw_validity.v` **red until complete** — do them on a branch
  in one focused pass; `git checkout` restores green (verified).
- Estimated 60–100 edit sites across `raw_validity.v` + `adequacy.v`.
- Guard: keep a `HeadRedVE`-style bundled statement so the four expand/contract
  facts stay proven together (single `induction k`).

## Not-yet-existing helpers to build

`Red` record + closure lemmas, `typing_ncase_inv`, `Red_ncase`, `Red_app`.
Everything else (`Val_EqVal_fwd`, `EqVal_EqValTy`, `conv_subst_arg`,
`adequacyEqSub`, `Val_fuel_down_to`, `Val_beta_expand`, `restrictVal`,
`HeadRed_ncase`) already exists.

See also memory `finelt-st-case-red3-blocker` and Agda
`~/github/agda/domain-semantics/NAT/Adequacy/NatCaseDep.agda`
(`motiveEqValTy2`, `adequacyV-ty-Case-dep`).
