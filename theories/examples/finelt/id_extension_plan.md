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

## Step 3 (done): the logical relation

In `raw_validity.v`:

* `Rec.ValTyId` / `Rec.EqValTyId` / `Rec.ValId` / `Rec.EqValId`, the `tid` arm
  of `Rec.ValTy` / `Rec.EqValTy`, and the `(rfl, tid)` arm of `Val` / `EqVal`,
  with the rewrite lemmas `ValTy_tid`, `EqValTy_tid`, `Val_rfl`, `EqVal_rfl`.
* Head reduction: `ValTyId_headred_expand`/`_contract`,
  `ValId_headred_expand`/`_contract`, `EqValId_headred_expand`/`_contract`, and
  the `tid`/`rfl` cases of the four `ValTy`/`EqValTy` head-red lemmas and of
  all four blocks of `headred_VE_all`.
* Code transport: `ValTyId_restrict`, `EqValTyId_restrict`, `ValId_restrict`,
  `EqValId_restrict` (shrink the value code), `ValId_down`/`EqValId_down` and
  `ValId_up`/`EqValId_up` (change the type code), and the `tid`/`rfl` cases of
  `restrictVal_step`, `restrictEqVal_step` and all six fields of
  `up_down_restrict`.
* Fuel stability: two new bundle components `HVI`/`HEI` with
  `fuel_ValId_S`/`fuel_EqValId_S`, threaded through `FuelStable`,
  `Val_fuel_up_S`/`_down_S`, `EqVal_fuel_up_S`/`_down_S` and `fuel_stable`,
  plus the `tid` cases of `fuel_ValTy_S`/`fuel_EqValTy_S`.
* Forward transport across a type conversion: `ValId_fwd`, `EqValId_fwd`, and
  the `rfl` cases of `FWD`/`EFWD`.

Two design decisions came out of this:

1. **`ValTyId` stores no step conversion.** `ValTy`/`EqValTy` are deliberately
   conv-free in this port (as for `tpi`); the `Red3` conversions live in the
   term-level records. That is what lets `ValTy_HeadRed1_expand` and friends
   move a type term freely.
2. **`ValId` stores no whole-type conversion either** — only
   `HeadRed A (tid A0 a0 b0)`, with the endpoint conversions stated at the
   *recorded* `A0`. Storing `conv Γ A (tid A0 a0 b0) tuniv` would have forced a
   `tid` congruence rule (`c_tid`) to exist before the logical relation could
   be transported across a type conversion; as it is, `ValId_fwd` needs only
   `c_trans`/`c_conv`. This mirrors `piConv`, which likewise returns a
   `HeadRed` rather than a whole-type conv.
3. **`ValId` stores the witness's *unary* validity** `Val Γ M0 A0` alongside the
   two endpoint `EqVal`s. It is in principle derivable from them, but only via
   `EqVal_Val1`, which is defined after `Val_EqVal` — and `Val_EqVal` needs it
   to build the diagonal `EqValId`.

`ValId_fwd` is where Coquand's membership rule earns its keep: the endpoint
equalities in `EqValTyId` live at the *endpoint* codes `x`, `y`, and
`restrictEqVal` brings them down to the witness code `w` (legitimate exactly
because `le w x` and `le w y`) so that transitivity can compose them with the
record's own facts.

* The PER: `EqValTyId_sym`, `EqValTyId_trans`, `EqValId_sym`,
  `EqValId_trans`, and the `tid`/`rfl` cases of `ETSYM`, `ETTRANS`, `SYM` and
  `TRANS`.

Two recurring techniques are worth naming, since the rest of the port will need
them:

* **The `tid` records' components sit at fuel `S k`, while the induction
  hypotheses `IHsym`/`IHtrans` are at `k`.** Each component therefore goes down
  a fuel with `EqVal_fuel_down`, gets flipped or composed, and comes back up
  with `EqVal_fuel_up`. The ranks always permit it (`rk c`, `rk x`, `rk y` are
  all `< k`). The local `flipE`/`transE` helpers package that; `flipU`/`transU`
  are the corresponding versions at a `tuniv` type, which have to go through
  `IHTsym`/`IHTtrans` instead because `rk tuniv = 1` is not `< k` for small `k`.
* **The endpoint conversions and equalities are stated at the *first* record's
  domain.** Swapping or composing two records therefore has to move them along
  the domain conversion — `c_sym`/`c_conv` for the syntactic ones and the
  already-built fuel-`S k` `EFWD` for the semantic ones.

A third, purely mechanical point: inside `fwd_per_all` the codes and `wt`
indices come from a `dependent destruction` and so have unpredictable names.
Every non-trivial case is therefore a standalone lemma taking the fuel-`k`
induction hypotheses as parameters, applied with `eapply`; the same trick is
what makes the transport lemmas above readable.

## Step 4 (done): the rules

`typing.v` gained `motive_ty`/`base_ty` with their four renaming/substitution
commutation lemmas, the three typing rules (`t_tid`, `t_rfl`, `t_jcase`) and
the four conversion rules (`c_tid`, `c_rfl`, `c_jcase_beta`, `c_jcase`), and
`reduction.v` gained `hr_jcase`/`hr_jcase_scrut` with `HeadRed1_det`'s cases.

The substantive syntactic content is the **type of the eliminator**: `jcase C d
p` has the binder-free type `app (app (app C a) b) p`, and showing that this
*is* a type is `motive_app_typing`, built from `motive_id_typing`,
`motive_cod1_typing`, `motive_cod2_typing`, `motive_app1_typing`,
`motive_app2_typing`. Its diagonal instance `base_app_typing` is exactly the
second side of `c_jcase_beta`; `motive_app_conv` and `base_ty_conv` are the
congruences that retype the primed side of `c_jcase`. All of that is proved,
as are the renaming/substitution and `conv_typing` cases for the seven new
rules, and `subst_conv_cross`, `red1_conv`, `subject_red1`, `progress_gen`.

Two gotchas worth recording:

* `asimpl` normalises the substituted motive types into *subst* form while
  leaving hand-written `A⟨↑⟩` in *ren* form, so `reflexivity` fails. The fix is
  autosubst2's own `substify` tactic: `asimpl; substify; asimpl; reflexivity`.
* `t_jcase`/`c_jcase_beta`/`c_jcase`'s conclusions do not mention `A`, so
  `eapply` leaves it as an evar. Pin it by discharging the first premise
  explicitly (`eapply (renaming_typing _ _ A tuniv _ _ δ); eauto`) before the
  rest.
* `Γ ++ A ++ A⟨↑⟩` parses right-associated — write `(Γ ++ A) ++ A⟨↑⟩`.

## What is left: the J driver

The tree compiles and every other part of the development is verified; the
remaining gaps are exactly the identity fragment's *semantic* content, 16
`Admitted`s in three groups.

**Soundness** (`typing_semantics.v`): `InvTyp_Id`, `InvTyp_Ref`, `InvTyp_J`,
`InvConv_Id`, `InvConv_Ref`, `InvConv_J_beta`, `InvConv_J`. The formers mirror
`InvTyp_Pi`/`InvTyp_Lam`. `InvTyp_J` should be as cheap as `InvTyp_Y` turned
out to be: `EvalRel`'s `jcase` clause puts the proof's value in front, and on
the informative branch `rfl w'` the result is recorded by the edge `w' ↦ c` of
the base — which is the `app` clause, and `InvTyp_App` requires *nothing* of
its argument.

**Adequacy** (`adequacy.v`): `st_tid`, `st_rfl`, `st_jcase`, `sc_tid`,
`sc_rfl`, `sc_jcase_beta`, `sc_jcase` — Agda's eight-file J driver (`JApp`,
`JAppE`, `JCase`, `JDriver`, `JEndpoint`, `JMotive`, `JRef`, `JTypeEq`). The
`tid`/`rfl` arms of `Val`/`EqVal` are the records already built in
`raw_validity.v`, so `st_tid`/`st_rfl` are assembly; `st_jcase` is the real
driver, and `sc_jcase_beta` head-contracts along `hr_jcase` with
`c_jcase_beta` as the step conversion, in the `sc_beta` style (with no type
transport, since both sides have the same type).

**Id-injectivity is done** (step 5). `idConv` and `idInjectivity` are the
`piConv`/`piInjectivity` pair one former along: evaluate both sides at the
bottom environment, transfer the trivial identity code `tid bot bot bot`
across the conversion (`evalRel_Id_trivial`), and read the recorded `HeadRed`
and the three component conversions off the resulting `EqValTyId`. With them,
`jcase_beta_conv` (matching a J-beta redex's own type
`app (app (app C a0) a0) (rfl a0)` against the derivation's
`app (app (app C a) b) (rfl a0)`, via the new `motive_app_conv_args`) and
`canonical_id` (no non-`rfl` value inhabits an identity type) are both proved.

### A note on the assumption set

Because adequacy is one mutual fixpoint over *all* the rules, admitting the
seven `st_*`/`sc_*` cases means every theorem downstream of adequacy inherits
them. So `piInjectivity`, `subject_red` and `progress` currently depend on the
14 J admits as well as the four standard axioms — not because anything about
them broke, but because the language they are stated for now includes `J` and
its adequacy is not yet proved. Discharging the J driver restores the earlier
situation.

## Remaining work, in dependency order## Remaining work, in dependency order
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

---

## Status (final for this pass): 2 admits, both the adequacy-level J driver

Everything except `st_jcase` and `sc_jcase` in `adequacy.v` is proved.
`typing_semantics.v` is admit-free, so **subject reduction and Π-injectivity
now hold with the ID fragment in the syntax**; what is missing is only the
adequacy of the eliminator itself.

Landed in this pass (14 admits → 2):

| lemma | how |
|---|---|
| `InvTyp_Id`, `InvTyp_Ref`, `InvConv_Id`, `InvConv_Ref` | congruences of the formers, via the new `InvTyped_ty_transport` / `InvTyp_Ref_gen` |
| `InvTyp_J` (as `InvTyp_J_gen`) | `InvTyp_App`'s value argument + the code-wise spine match below |
| `InvConv_J_beta` | `InvTyp_J` / `InvTyp_App` at `base_ty`'s codomain, `asimpl` for the substitution |
| `InvConv_J` | `InvTyp_J_gen` (free term motive) + one `InvTyped_ty_transport` along `EvalRel_app_tr` |
| `st_tid`, `st_rfl` | the `*_Val_edge` / `*_EqVal_edge` split used for `tpi`/`abs` |
| `sc_tid` | primed `ValTyId` read off the component `semantic_conv2`s with `EqVal_Val2`; endpoints moved `A[σ] → A'[σ]` by `Val_EqVal_fwd`, whose `EqValTy` is `SCA` taken at fuel `S RB` |
| `sc_rfl` | `st_rfl_EqVal_edge` with the second *substitution* replaced by the second *term* |
| `sc_jcase_beta` | the `sc_ncase_Z` shape: `st_jcase` on the diagonal + `EqVal_headred_contract` |

### Why `InvTyp_J` was cheap and `st_jcase` is not

`InvTyp_J` works because the two application spines match **code-wise**.
`d : base_ty A C = tpi A (app (app (app C⟨↑⟩ 0) 0) (rfl 0))`, so `d`'s codomain
edge at the witness gives an `x ≤ w'` with

    EvalRel (app (app (app C⟨↑⟩ 0) 0) (rfl 0)) (x .: ρ) (app fa w')

— `C` applied to the *witness* three times — while the goal needs `C` applied
to `a`, `b` and `p`.  They meet by Coquand's membership rule: `p`'s enlargement
is an `rfl w''` with `wt (rfl w'') (tid tp up vp)`, hence `le w'' up` and
`le w'' vp`, and `up`/`vp` are values of `a`/`b`.  So `a` and `b` *both*
evaluate the witness, and every argument code below `x ≤ w' ≤ w''` is an
approximation of `a`, of `b`, and (wrapped in `rfl`) of `p`.  **No
motive-agreement argument is needed.**

At the adequacy level that shortcut is gone, because `Val`/`EqVal` carry
*syntactic* conversions alongside the code.  Both remaining admits hinge on the
same missing lemma, Agda's `JTypeEq`:

    EqValTy k Δ (app (app (app C[σ] P0) P0) (rfl P0))
                (app (app (app C[σ] a[σ]) b[σ]) p[σ]) h

where `P0` is the witness *term* delivered by `STp`'s `ValId` record
(`HeadRed p[σ] (rfl P0)`, `conv Δ P0 a[σ] A[σ]`, `conv Δ P0 b[σ] A[σ]`, plus
the two reducible equalities `EqVal Δ P0 a[σ] A[σ]` and `EqVal Δ P0 b[σ] A[σ]`
— this is where `idInjectivity` is really used).

### Recipe for `st_jcase` (verified: every ingredient below exists and compiles)

Stages 1–3a are **written and compiling** in `adequacy.v` under two `admit`s;
what follows describes what the `admit`s still owe.

**Stage 1 — the witness (done).** `EvalRel (jcase C d p)` records the result
`u` as the edge `w' ↦ u` of the base branch `d`, where `rfl w'` is a value of
`p`.  `typing_EvalRel Tp Fρ` enlarges that to an `rfl w''` whose `wt` at the Id
code *is* Coquand's rule, and `STp` at that code hands back a `ValId`: the
witness term `P0` with `HeadRed p[σ] (rfl P0)`, the two endpoint conversions and
the two endpoint **reducible equalities**.  Re-derived at arbitrary fuel with
`HeadRed_rfl_det` pinning `P0` down (`valPk` / `IdPk`).  `jcase_drive_conv` +
`HeadRed_jcase` give the driver's syntactic side.

**Stage 2 — `d`'s value edge at `P0` (done).**  `st_app`'s shape, except the
argument is a Δ-term with no `semantic_typing` to re-ask.  Its `Val` comes from
the proof's own `ValId`, moved from the proof's code `(w'', t)` to the
function's selection code `(u_sel, bd)` through the join `lub bd t` —
`Val_app_transport` is exactly that dance, and `Val` of `A[σ]` at the join comes
from `STA`, which is quantified over every code `A` evaluates.  Result:

    Vapp : Val RBf Δ (app d[σ] P0)
               (app (app (app C[σ] P0) P0) (rfl P0))
               (wt_Selection_abs WTd Sel)

**Stage 3a — the goal type at the edge's code (done).** `EvalRel_base_cod_spine`
turns `d`'s *type* codomain edge into an `EvalRel` of the **goal's** spine:
`EvalRel (app (app (app C a) b) p) ρ (app fd u_sel)`.  Hence `a0` and
`app fd u_sel` are compatible (`EvalRel_compatible` on one term), which is the
hypothesis `Val_app_transport` needs, and `evT_lub` gives the join.

**Stage 3b — the motive spine (`JMotive`/`JTypeEq`, the remaining work).**  One
walk of `C[σ]`'s three applications delivers *both* missing pieces, because

    EqVal (S k) Δ T1 T2[σ] Core.tuniv h
      --EqVal_Val2-->  Val k Δ T2[σ] Core.tuniv h      (the ValTy for 3c)
      --EqVal_tuniv-->  EqValTy k Δ T1 T2[σ] h          (JTypeEq itself)

where `T1 = app (app (app C[σ] P0) P0) (rfl P0)` and
`T2 = app (app (app C a) b) p`.  Run the walk at `aT := lub a0 (app fd u_sel)`
(stage 3a supplies `EvalRel T2 ρ aT`), so the result sits *above* both codes the
transports need.

Everything the walk consumes comes from **one** place, `STC`'s `Val` at the
motive's code, via `Val_abs`:

    Val (S k) Δ C[σ] (motive_ty A)[σ] WTc
      = ValTy k Δ (motive_ty A)[σ] (wt_abs_ty WTc)   /\   ValPi k Δ C[σ] … WTc

- the `ValPi` half gives `PiAppVal` / `PiAppEq` — the *term*-level steps,
  packaged as `spine_Val` / `spine_EqVal_arg` / `spine_EqVal_fun`
  (`raw_validity.v`);
- the `ValTy` half gives `PiEdgeVal` / `PiEdgeEq` — and **`PiEdgeEq` is the
  non-obvious key**: at each level the two sides' *types* differ
  (`B1'[P0..] = tpi A[σ] (tpi (tid A[σ]⟨↑⟩ P0⟨↑⟩ 0) tuniv)` on the left versus
  `B1'[a[σ]..]` on the right), and `PiEdgeEq` says related arguments give
  **equal** codomain types, which is exactly the `EqVal_EqVal_fwd` transport
  that lets `EqVal_trans` compose the function-step with the argument-step.

Per level, then: `spine_EqVal_fun` (vary the function) + `spine_EqVal_arg`
(vary the argument) + `EqVal_EqVal_fwd` along `PiEdgeEq` + `EqVal_trans`.
Level 1's function is the same on both sides, so it is just `spine_EqVal_arg`.

Choosing each level's codes: `spine_*` need the function code to be literally
`(abs g, tpi b f)`, so descend the codes from the *goal type's* own `EvalRel`.
Unfold `EvalRel T2 ρ aT` to `w1, w2, w3` with
`EvalRel C ρ (w3 ↦ (w2 ↦ (w1 ↦ aT)))`, enlarge with `typing_EvalRel TC Fρ`,
then at each level use **`spine_descend`** (`raw_validity.v`) to turn
`le (w ↦ rest) V` + `wt V aV` into `V = abs gV`, `aV = tpi bV fV`,
`le rest (app gV w)`.  It returns *equations* on purpose: `Val` matches on both
codes, so a `Val` built at unanalysed codes is a stuck match that cannot be
rewritten afterwards (the codes occur only in the type of the `wt` index, which
`rewrite` cannot abstract).  `subst` the value code and `rewrite` the type code
**before** building any `Val` at them.  The intermediate functions'
`InvTyped`s, where needed, are two cheap `InvTyp_App`s.

The arguments' `Val`s/`EqVal`s at each selection code:
`a[σ]`, `b[σ]`, `p[σ]` are Γ-terms, so just re-ask `STa`/`STb`/`STp` at that
code (they evaluate every code below the witness — stage 3a's reasoning);
`P0` and `rfl P0` are Δ-only, so use `Val_app_transport` /
`EqVal_app_transport` from the proof's own code as in stage 2, with `rfl P0`'s
record at the off-diagonal `tid A[σ] a[σ] b[σ]` built by Coquand's rule
(`rfl_offdiag_typing` for the typing, `ValId`'s two stored equalities for the
reducible part — the `sc_rfl` shape).

**Stage 3c — finish.** `Val_EqVal_fwd` moves `Vapp`'s type from `T1` to `T2[σ]`
at the edge's code (using `EqValTy` from 3b and `motive_app_conv_witness` for
the syntactic conv); `Val_app_transport` then moves the code from
`(v_sel, app fd u_sel)` to `(u, a0)` (using the `ValTy` from 3b and stage 3a's
compatibility); `Val_fuel_any` drops `RBf` to `RB`; `Val_beta_expand` with
`HeadRed_jcase` and `jcase_drive_conv` head-expands `app d[σ] P0` back to
`(jcase C d p)[σ]`.

`sc_jcase` is the same walk with `EqVal_headred_expand` and `SCd`'s edge at
`EqVal P0 P0'`, reusing 3b unchanged.  So **stage 3b is the one remaining piece
of mathematics**; it is worth landing as its own top-level lemma taking the
`semantic_typing`s plus the stage-1 witness package.
