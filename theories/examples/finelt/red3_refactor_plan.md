# Plan: unblock `st_case` / `sc_ncase` (dependent `ncase` adequacy)

Status: **planned, definition-change prototyped & reverted (stays green).**
Approach chosen: **`ConvNum` conjunct on `semantic_typing`** (below). The earlier
**Red3-in-`Val`** idea is **superseded** — see "Why not Red3" — it hits a wall in
`raw_validity`'s Pi-edge machinery.

## The blocker (unchanged)

`st_case`'s dependent-motive transport needs `EqValTy ((T[num..])[σ]) ((T[M..])[σ])`,
whose definition ([raw_validity.v](raw_validity.v) ~L231) bundles *syntactic*
conversions, so it needs `conv M[σ] ≡ numeral` at `tnat`. Deriving that from
`HeadRed` (`red1_conv`) has a β-case needing Pi-injectivity → `adequacyEqSub` →
the adequacy Fixpoint, of which `st_case` is a building block. **Circular.**
Confirmed: [c_beta](../syntax/typing.v) requires the abs domain/codomain, so
`red1_conv`'s β-case genuinely needs Pi-injectivity — no early `red⊆conv`.

## Chosen approach: `ConvNum` conjunct on `semantic_typing`

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
