# Plan: unblock `st_case` / `sc_ncase` (dependent `ncase` adequacy)

Status: **IN PROGRESS — Red3-in-`Val` refactor (the Agda-faithful path).** An
earlier note here claimed both threading approaches hit a "fundamental Pi-edge
wall"; **that was wrong** and is corrected below.

## Executive finding (corrected 2026-07-06)

The dependent `ncase`'s motive transport needs `conv M[σ] ≡ numeral` at `tnat`
for the scrutinee `M`. The fix is to make `Val`/`EqVal` **carry the conversion**
(Agda's `Red3 = HeadRed + ConvTm`), exactly as Agda does — no confluence.

**Why the earlier "wall" was a mistake.** I claimed `headred_VE_all`'s Pi-edge
recursion (`ValPiExp`) "has no typings in scope" to build the `c_app1`
congruence conv. It does: reading the Agda proof (`Validity/HeadRed.agda:236`
`ValPi2-headred-contract`) shows it builds the per-edge congruence with
`conv-App-fun htA0 htB0 ctPi htN` (= Coq `c_app1`), getting `htA0`/`htB0` from
the **`ValTy` record it carries** and `htN` from the **argument typing passed
into the edge**. Coq's `Val` carries the same: `ValTy`'s Pi case stores
`typing Γ A tuniv` / `typing (Γ++A) B tuniv` ([raw_validity.v:199-200]), and the
edge `PiEdgeVal` takes `typing Γ N A` ([raw_validity.v:113]). So `ValPiExp`'s
edge closure already has `TQ : typing Δ Q A0` in hand and can build the `c_app1`
conv — just like Agda. The Pi-edge is transportable; the refactor closes.

## How Agda threads the conversion (the recipe to mirror)

- `Val2`/`EqVal2` bundle `Red3` at nat leaves and Pi-codes (and Pi-edge
  codomain results carry `Red3` too, built at Lam/App adequacy where typings
  exist — which is why Agda's `App` case gets the result conv for free, and why
  the Coq `ConvNum`-only sweep failed at `st_app`).
- Head-expansion (`Val2-beta-expand`) takes the **step conv `cv : ConvTm G M' M T`
  as an argument**; the caller supplies it from local conv rules
  (`conv-beta`/`conv-case-*`/`conv-App-fun` = `c_beta`/`c_ncase_*`/`c_app1`).
- Whole-term leaves (numeral, `tpi`-code): thread `cv` by `conv-trans`
  (`Validity/HeadRed.agda:140–175`) — no per-edge conv.
- Function-value Pi-edge: transport the edge, building the per-edge `c_app1`
  conv from the stored `ValTy` typings (`ValPi2-headred-contract`).

## Coq refactor steps (Red3-in-`Val`) — recipe validated by execution 2026-07-06

Two design decisions were confirmed by running the refactor to the crux (then
reverting to green):

- **Bundle the numeral conv at the `Val`'s type term `A`** (the 4th `Val`
  argument). Then leaf conv `conv Γ M numeral A` and head-expansion step conv
  `cv : conv Γ M' M A` `c_trans` with **no retyping**. For the `st_case`
  scrutinee `A = tnat[σ] = tnat`, giving exactly `conv M[σ] ≡ numeral tnat`.
- **Bundle the Pi-type-code conv in `ValPi`/`EqValPi` ONLY, NOT `ValTy`/
  `EqValTy`.** Putting it in `ValTy` forces retyping the step conv from the
  abstract type-term `T` to `tuniv` in the `a=tuniv` head-expansion case, which
  Coq's `Val` cannot do (unlike Agda, whose `Val2` carries a ValTy-of-`T`). With
  it in `ValPi`, `ValTy`/`EqValTy` and their head-expansion lemmas stay
  **conv-free/unchanged**, and `ValPiExp` reads the type-code conv from `ValPi`
  and the domain/codomain typings from the (unchanged) `ValTy` it is given.

Validated fragments (compiled before the full-file revert): the `Val`/`EqVal`
nat-leaf defs + `Val_zero/succ`/`EqVal_zero/succ`, the projections
`Val_EqVal`/`EqVal_Val1/2`, and the four `ValTy_HeadRed_*` lemmas via the
**direct-rebuild** pattern (destructure input; `HeadRed` by `ms_app`, stored
conv by `c_trans`; typings/edges carry over verbatim).

1. Nat leaves: `Val`/`EqVal` add `conv Γ M numeral A`; update the 4 unfolding
   lemmas. `ValPi`/`EqValPi` add `conv Γ A (tpi A0 B0) tuniv`. `ValTy`/`EqValTy`
   **unchanged**.
2. Projections `Val_EqVal`, `EqVal_Val1/2`: thread the extra conv binders.
3. `HeadRedVE`/`headred_VE_all`: each direction takes the step conv(s). Leaves:
   `c_trans` (`ms_app` for `HeadRed`). `ValTy`/`EqValTy` cases: **unchanged**.
   `abs` cases pass `[VTd VPi]` (ValTy for typings, ValPi for the type-code conv)
   + step conv to the Pi helpers.
4. `ValPiExp`/`ValPiCon`/`EqValPiExp`/`EqValPiCon`: signature gains step conv +
   the `ValTy` (for `TA0`/`TB0`). Build edge conv:
   `cvPi := c_conv step-conv (ValPi.CT)` then `c_app1 TA0 TB0 cvPi TQ`. The
   `EqVal` (cross) direction retypes the second app-conv to the shared codomain
   `B0[N1..]` via `c_conv _ (c_sym (conv_subst_arg TA0 TB0 TN1 TN2 CN))`.
   (`nf_tpi` helper needed for the contract multi-step; `conv_typing` gives the
   argument typings `TN1`/`TN2` from the edge's `conv N1 N2 A0`.)
5. `Val_beta_expand` + all callers of the head-expansion supply the step conv
   from local conv rules.
6. Fuel/transport (`fuel_stable`, `Val_fuel_down_to`, `*_app_transport`): update
   the `tnat`-case match patterns (extra conv conjunct) + `ValPi` conv binder.
7. `st_*` construction sites supply `Red3` at leaves (`c_refl`/`c_succ`/`c_beta`/
   `c_ncase_*`); the Pi-edge results carry the conv (built at `st_abs`, which has
   the body typing for `c_beta`). This is what makes `st_app` read the result
   conv off the edge (the sole failure point of the `ConvNum`-only sweep).
8. `st_case`: read scrutinee conv off its `Val`; `conv_subst_arg` →
   `adequacyEqSub` → `EqValTy` → `Val_EqVal_fwd`; head-expand `ncase→branch`
   with the `c_ncase_*` step conv. Then `sc_ncase_*`, and `subject_red1` t_case.

Scope: ~150 careful edits across `raw_validity.v` + `adequacy.v`. All-or-nothing
per file (no intra-file green checkpoint). Multi-session.

## Superseded / partial (kept for reuse)

The `ConvNum`-on-`semantic_typing` sweep below is a real, working thread through
`st_var`/`st_conv`/`dom_transport`/`codomain_type_ValTy` but is subsumed: once
the Pi-**edge** carries `Red3`, `st_app` reads the result conv off the edge, so
the separate `ConvNum` layer is unnecessary. Kept for the recipe.

## The blocker (unchanged)

`st_case`'s dependent-motive transport needs `EqValTy ((T[num..])[σ]) ((T[M..])[σ])`,
whose definition ([raw_validity.v](raw_validity.v) ~L231) bundles *syntactic*
conversions, so it needs `conv M[σ] ≡ numeral` at `tnat`. Deriving that from
`HeadRed` (`red1_conv`) has a β-case needing Pi-injectivity → `adequacyEqSub` →
the adequacy Fixpoint, of which `st_case` is a building block. **Circular.**
Confirmed: [c_beta](../syntax/typing.v) requires the abs domain/codomain, so
`red1_conv`'s β-case genuinely needs Pi-injectivity — no early `red⊆conv`.

### `ConvNum` recipe (superseded — dies at `st_app`, see Executive finding)

Thread the numeral conversion **compositionally through the adequacy layer**, not
through `Val`. Each `st_*`/`sc_*`/`ValSub_cons` builds it from its **local**
typings via the conv rules (`c_refl`/`c_succ`/`c_beta`/`c_ncase_*`) — **no global
`red⊆conv`, no Pi-injectivity, non-circular.**

```coq
Definition ConvNum {n} (Δ : Ctx n) (M : Tm n) (u : elt) : Prop :=
  match u with
  | Raw.zero   => conv Δ M Core.zero Core.tnat
  | Raw.succ _ => exists P, HeadRed M (Core.succ P) /\ conv Δ M (Core.succ P) Core.tnat
  | _          => True   (* non-numeral values carry nothing *)
  end.
```

Add to `semantic_typing`'s conclusion: `... /\ ConvNum Δ M[σ] u /\ ConvNum Δ M[σ'] u`
(both substitutions, since the `EqVal`/cross component needs both). Add the
analogue to `semantic_conv2` (`ConvNum` for both `M[σ]` and `N[σ]`). `ValSub` /
`EqValSub` gain a `ConvNum` entry (so `st_var` can read it off the substitution).

**Key property — no `raw_validity` change.** The *result* `Val` in `st_case` is
still produced by the existing bare-`HeadRed` `Val_beta_expand` (the result
numeral-`Val` is just `HeadRed (ncase..)[σ] num` via `ms_trans`). Only the
*scrutinee's* conversion is new, and it comes from `ConvNum`.

### `st_case` recipe (zero branch; succ analogous with the `rho` identity)
1. Scrutinee `SM` gives `Val M[σ] tnat` at `zero` (⇒ `HeadRed M[σ] zero`) **and**
   `ConvNum Δ M[σ] zero = conv M[σ] zero tnat`.
2. `conv_subst_arg` on `conv M[σ] ≡ zero` ⇒ `conv (T[zero..])[σ] ≡ (T[M..])[σ]`
   (modulo `subst`-commutation).
3. `adequacyEqSub` on that conv ⇒ `EqValTy` between the two motive types.
4. Branch `SM0` gives `Val M0[σ] (T[zero..])[σ]`; `Val_beta_expand`
   (`ncase[σ] → M0[σ]`) lifts to `Val (ncase..)[σ] (T[zero..])[σ]`;
   `Val_EqVal_fwd` transports along the `EqValTy` to `(T[M..])[σ]`.
5. Succ: same, with `conv M[σ] ≡ succ P`, branch `M1[σ][P..]` at
   `T[rho][P..] = T[(succ P)..]`, predecessor `P` from `ConvNum`'s witness
   (typed via `conv_typing`), and `EqVal`/cross side mirrors it.

## Blast radius (all in `adequacy.v`, mechanical, non-circular)

- Defs: `ConvNum`, `semantic_typing`, `semantic_conv2`, `ValSub`, `EqValSub`.
- `ValSub_cons`, `EqValSub_cons`, `ValSub`/`EqValSub` bridges.
- `st_*` producers: `st_var` (from `ValSub`), `st_zero` (`c_refl`), `st_succ`
  (`c_succ`), `st_app` (`c_beta` on its *known* `F:tpi A B`, `a:A` — **no
  inversion**), `st_conv` (from `STA`). Non-numeral producers (`st_nat`,
  `st_univ`, `st_tpi`, `st_abs`) discharge `ConvNum = True` trivially.
- Consumers: most use `[valX _]` (first component) and are **unaffected** by a
  right-associated extra conjunct; only ~2 (`[valMA eqvalMA]` in `st_conv`,
  ~L722; `[valN eqvalN]`, ~L889) need `[valMA [eqvalMA _]]`.
- Payoff: `st_case`, then `sc_ncase_Z/S/cong`.
- Bonus (independent): `subject_red1` t_case once `typing_ncase_inv` +
  `red1_conv` exist (these are post-adequacy, fine there).

Estimated 60–80 sites, **all in `adequacy.v`**. Definition change ⇒ red until
the sweep completes (all-or-nothing; no green milestone mid-sweep). Fallback: a
fully-threaded build with `st_case` left `Admitted` **is** green/committable, so
the infrastructure can land before the succ case is finished.

## Why not Red3-in-`Val` (superseded)

Bundling `conv` into `Val`'s `tnat` leaves ([raw_validity.v] ~L317) compiles the
unfolding lemmas + `Val_EqVal`/`EqVal_Val1/2`, but **dies at `headred_VE_all`**
(~L770): Val head-*expansion* for `zero` must build `conv M0 zero` from
`conv M zero` + `HeadRed M0 M`, i.e. `conv M0 M` from `HeadRed M0 M` = `red⊆conv`
again — and the **generic Pi-edge head-expansion recursion has no typings in
scope** to build the needed `c_app1`/`c_beta` congruence convs. Making it work
would require threading typings through the whole `Val` machinery (Pi edges,
fuel, transport) — a much deeper change than `ConvNum`, which sidesteps `Val`
entirely. (Verified empirically 2026-07-06.)

See memory `finelt-st-case-red3-blocker`; Agda
`~/github/agda/domain-semantics/NAT/Adequacy/NatCaseDep.agda`
(`motiveEqValTy2`, `adequacyV-ty-Case-dep`).
