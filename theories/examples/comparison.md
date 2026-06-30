# Rocq vs Agda Definitions

Comparison of definitions in the Rocq project (`theories/examples/finelt/`, `theories/examples/syntax`) versus the Agda project (`domain-semantics/MIN/`).

Agda file references below use the current `MIN/` paths. The
[Top-level lemma correspondence](#top-level-lemma-correspondence) section maps
the principal theorem statements on each side.

| Topic | Rocq (file:definition) | Agda (file:definition) |
|-------|------------------------|------------------------|
| **Raw Syntax** | | |
| Terms | [syntax/syntax.v](syntax/syntax.v): `Tm` | Syntax/Raw.agda: `Expr` |
| Finite indices | [syntax/fin_util.v](syntax/fin_util.v): `f0..f3` | Syntax/Raw.agda: `Fin` |
| Renaming | [syntax/syntax.v](syntax/syntax.v): `ren_Tm`, `renRen_Tm` | Syntax/Raw.agda: `liftRen`, `renExpr` |
| Weakening | [syntax/syntax.v](syntax/syntax.v): `extRen_Tm` | Syntax/Raw.agda: `wkRen`, `wkExpr` |
| Substitution | [syntax/syntax.v](syntax/syntax.v): `subst_Tm`, `substSubst_Tm` | Syntax/Raw.agda: `liftSub`, `substExpr`, `subst1` |
| **Typing** | | |
| Typing judgment | [syntax/typing.v](syntax/typing.v): `typing` | Syntax/Typing.agda: `HasType` |
| Conv. judgment | [syntax/typing.v](syntax/typing.v): `conv` | Syntax/Typing.agda: `ConvTm` |
| Eta conversion | [syntax/typing.v](syntax/typing.v): `c_eta` constructor of `conv` | Syntax/Typing.agda: `conv-funext` constructor of `ConvTm` |
| Beta conversion | [syntax/typing.v](syntax/typing.v): `c_beta` | Syntax/Typing.agda: `conv-beta` |
| Contexts | [syntax/typing.v](syntax/typing.v): `Ctx`, `ctx` | Syntax/Typing.agda: `Ctx`, `WfCtx` |
| Var lookup | [syntax/typing.v](syntax/typing.v): `lookup` | Syntax/Typing.agda: `lookup` |
| Renaming / subst | [syntax/typing.v](syntax/typing.v): `typing_renaming`, `renaming_typing`, `typing_subst` | Syntax/Substitution.agda: `RenTypes`, `WtSub` |
| **Finite Elements (Domain)** | | |
| Element datatype | [finelt/findom.v](finelt/findom.v): `Raw.elt` (7 ctors: `bot`, `tnat`, `tuniv`, `zero`, `succ`, `tpi a f`, `abs f`) | Domain/Basic.agda: `FinEl` (4 ctors: `Bot`, `UCode`, `FunEl g`, `PiCode a f`) |
| Bottom | [finelt/findom.v](finelt/findom.v): `bot` | Domain/Basic.agda: `Bot` |
| Universe code(s) | [finelt/findom.v](finelt/findom.v): `tuniv : elt` (single universe, type-in-type: `wt tuniv tuniv`) | Domain/Basic.agda: `UCode` (single universe) |
| Naturals | [finelt/findom.v](finelt/findom.v): `tnat`, `zero`, `succ` | — (no built-in Nat type) |
| Pi-type code | [finelt/findom.v](finelt/findom.v): `tpi a f` | Domain/Basic.agda: `PiCode a f` |
| Function value | [finelt/findom.v](finelt/findom.v): `abs f` | Domain/Basic.agda: `FunEl f` |
| Finite function | [finelt/findom.v](finelt/findom.v): `list (elt * elt)` | Domain/Basic.agda: `FinFun = List (Pair FinEl FinEl)` |
| Rank | [finelt/findom.v](finelt/findom.v): `rk`, `rk_fun` | Domain/Basic.agda / Domain/Rank.agda: `rk`, `rkFun` |
| Non-bottom | [finelt/findom.v](finelt/findom.v): `~~ le _ bot` (via `no_bot_result`) | Domain/Order*.agda: `NotBot` |
| **Order & Operations** | | |
| Decidable order on elts | [finelt/findom.v](finelt/findom.v): `le : elt -> elt -> bool` (boolean) | Domain/OrderEval.agda: `leFinEl : FinEl -> FinEl -> Nat` (positive = holds) |
| Decidable order on funs | [finelt/findom.v](finelt/findom.v): `le_fun` (boolean) | Domain/OrderEval.agda: `leFun` (Nat) |
| Propositional order | [finelt/findom.v](finelt/findom.v): lifted from boolean (no separate prop. version) | Domain/Order.agda: `LeCode`, `LeFunCode` (Set-valued) |
| Compatibility | [finelt/findom.v](finelt/findom.v): `compatible`, `compatible_fun` (boolean) | Domain/OrderComp.agda: `Comp`, `CompFun`, `CompStepFun`, `CompStepStep` |
| Coherent-with | [finelt/findom.v](finelt/findom.v): `coherent_with f (u,v)` | Domain/Order*.agda: `CoherentWith` |
| Validity (= coherence) | [finelt/findom.v](finelt/findom.v): `valid`, `valid_fun` (boolean; `valid_fun` does **not** include `~~ is_bot` since commit `d846fd3`) | Domain/Order*.agda: `Coherent`, `CoherentFun`, `CoherentFunTail` |
| CFT record | [finelt/findom.v](finelt/findom.v): `Record CFT u v f` (`key_valid`, `val_valid`, `val_nbot`, `compat`) | Domain/Order*.agda: `record CFTcons` (`key-coh`, `val-coh`, `val-nbot`, `compat`, `tail-coh`) |
| Sup / lub | [finelt/findom.v](finelt/findom.v): `lub : elt -> elt -> elt` (total; returns `bot` on incompat) | Domain/OrderComp.agda: `Sup : FinEl -> FinEl -> FinEl` (returns `Bot` on incompat) |
| Lub of list | [finelt/findom.v](finelt/findom.v): `lub_list : list elt -> elt` (`fold_right lub bot`) | (inlined via `Sup`/`append`) |
| Append on fns | [finelt/findom.v](finelt/findom.v): `++` (list append) | Domain/Basic.agda: `append` |
| Apply finite fn | [finelt/findom.v](finelt/findom.v): `app : list (elt*elt) -> elt -> elt` (total; `bot` when no key matches) | Domain/OrderEval.agda: `EvalFun : FinFun -> FinEl -> FinEl` |
| Apply elt as fn | [finelt/findom.v](finelt/findom.v): (via `app` after `abs`-pattern) | Domain/Order*.agda: `applyEl` |
| Refl/trans/mono | [finelt/findom.v](finelt/findom.v): `le_refl`, `le_trans`, `le_fun_mono`, `OrderTheoreticLemmas` | Domain/OrderLaws.agda / OrderProps.agda: stated as separate lemmas |
| **Well-typed elements (codes)** | | |
| Membership relation | [finelt/types.v](finelt/types.v): `wt : elt -> elt -> Prop` (inductive: `wt_bot`, `wt_tuniv`, `wt_tnat`, `wt_zero`, `wt_succ`, `wt_tpi`, `wt_abs`) | Domain/Membership.agda: `FinMem`, `FinMemU` |
| **Raw Semantics** | | |
| Environment | [finelt/raw_semantics.v](finelt/raw_semantics.v): `Env n := fin n -> elt` | Model/Eval.agda: `EnvApprox` |
| Evaluation | [finelt/raw_semantics.v](finelt/raw_semantics.v): `EvalRel`, `EvalRel_fun` | Model/Eval.agda: `EvalRel` |
| Bottom test | [finelt/findom.v](finelt/findom.v) / [finelt/raw_semantics.v](finelt/raw_semantics.v): `is_bot` | Domain/Order*.agda: `NotBot` (negation) |
| Singleton fn | [finelt/findom.v](finelt/findom.v): `singleton a b` (`= bot` if `b = bot`) | (built inline via `cons (a,b) nil`) |
| Env validity | [finelt/raw_semantics.v](finelt/raw_semantics.v): `valid_env` | Model/Eval.agda: `CoherentEnv` |
| Env order | [finelt/raw_semantics.v](finelt/raw_semantics.v): `le_env` | Model/Eval.agda: `EnvLe` |
| Eval monotonicity | [finelt/raw_semantics.v](finelt/raw_semantics.v): `EvalRel_mono_env`, `EvalRel_down`, `EvalRel_sup`, `EvalRel_valid`, `lam_edgewise`, `EvalRel_fun_compatible` | Model/Eval.agda: `EvalRel-mon-env`, `EvalRel-down`, `EvalRel-Sup`, `EvalRel-coh`, … |
| Selection (value-graph join) | [finelt/selection.v](finelt/selection.v): `Selection`, `valid_Selection`, `wt_Selection`, `Selection_le_app` | Model/Selection.agda (+ SelectionRank.agda): `Selection`, `Coherent-Selection`, `FinMem-Selection`, `Selection-le-EvalFun` |
| Eval renaming/subst | [finelt/eval_substitution.v](finelt/eval_substitution.v): `EvalRel_unwk`, `EvalRel` renaming/subst lemmas | Model/EvalSubstitution.agda: `SubRel`, `extractFinMemU` |
| **Logical relation** | | |
| Module | [finelt/raw_validity.v](finelt/raw_validity.v) | Validity/*.agda (public faces in Validity/Public.agda, Levels.agda, Props.agda) |
| Unary value relation | [finelt/raw_validity.v](finelt/raw_validity.v): `Val M A (h : wt u a)` | Validity/Core.agda: `Val2` |
| Binary equality relation | [finelt/raw_validity.v](finelt/raw_validity.v): `EqVal M N A h` (mutual Fixpoint) | Validity/Core.agda: `EqVal2` |
| Type-relations | [finelt/raw_validity.v](finelt/raw_validity.v) (`Rec.` namespace): `ValTy`, `EqValTy` | Validity/Core.agda: `ValTy2`, `EqValTy2` |
| Pi-edge predicates | [finelt/raw_validity.v](finelt/raw_validity.v): `PiEdgeVal`, `PiEdgeEq` (forall edge `(u,v)` in pi-fn) | Validity/Core.agda: `PiEdgeVal2`, `PiEdgeEq2` |
| Pi-app predicates | [finelt/raw_validity.v](finelt/raw_validity.v): `PiAppVal`, `PiAppEq`, `PiAppEqVal` (forall edge `(u,v)` in lambda-fn) | Validity/Core.agda: `PiAppVal2`, `PiAppEq2`, `PiAppEqVal2` |
| Pi value predicate | [finelt/raw_validity.v](finelt/raw_validity.v): `ValPi`, `EqValPi` (exists `(A,B)` such that `HeadRed` to `tpi A B`) | Validity/Core.agda: `ValPi2`, `EqValPi2` |
| Bot lemmas | [finelt/raw_validity.v](finelt/raw_validity.v): `Val_Bot`, `EqVal_Bot` | Validity/Props.agda: `Val2-Bot-pub`, `EqVal2-Bot-pub` |
| Val ↔ ValTy / EqVal ↔ EqValTy | [finelt/raw_validity.v](finelt/raw_validity.v): `ValTy_Val`, `Val_ValTy`, `EqValTy_EqVal`, `EqVal_EqValTy` | Validity/*.agda (named the same with `2` suffix) |
| Diagonal | [finelt/raw_validity.v](finelt/raw_validity.v): `Val_EqVal`, `ValTy_EqValTy` | Validity/Props.agda: `Val2-to-EqVal2-pub`, `ValTy2-to-EqValTy2-pub` |
| Projections | [finelt/raw_validity.v](finelt/raw_validity.v): `EqVal_Val1`, `EqVal_Val2` | Validity/*.agda |
| Symmetry/transitivity | [finelt/raw_validity.v](finelt/raw_validity.v): `EqVal_sym`, `EqVal_trans`, `EqValTy_sym`, `EqValTy_trans` | Validity/Props.agda: `EqVal2-sym-pub`, `EqVal2-trans-pub`, `EqValTy2-sym-pub`, `EqValTy2-trans-pub` |
| Forward by type-eq | [finelt/raw_validity.v](finelt/raw_validity.v): `Val_EqVal_fwd`, `EqVal_EqVal_fwd` | Validity/Props.agda: `Val2-EqValTy2-fwd-pub`, `EqVal2-EqValTy2-fwd-pub` |
| Head-red expand/contract | [finelt/raw_validity.v](finelt/raw_validity.v): `ValTy_headred_expand/contract`, `EqValTy_headred_expand/contract`, `Val_beta_expand`, `Val_headred_contract`, `EqVal_headred_expand/contract`, `ValPi_headred_expand/contract`, `EqValPi_headred_expand/contract` | Validity/HeadRed.agda (corresponding names, e.g. `Val2-beta-expand-pub`, `Val2-headred-contract`, `EqVal2-headred-expand/contract`) |
| Sup | [finelt/raw_validity.v](finelt/raw_validity.v): `ValTy_Sup`, `EqValTy_Sup` | Validity/Props.agda: `ValTy2-Sup`, `EqValTy2-Sup` |
| Up / Down | [finelt/raw_validity.v](finelt/raw_validity.v): `upVal`, `upEqVal`, `downVal`, `downEqVal`, `downValTy`, `downEqValTy` | Validity/*.agda: `upVal2-pub`, `downVal2-pub`, `upEqVal2-pub`, `downEqVal2-pub`, … |
| Restrict | [finelt/raw_validity.v](finelt/raw_validity.v): `restrictVal`, `restrictEqVal` | Validity/*.agda: `restrictVal2-pub`, `restrictEqVal2-pub` |
| Pi helpers | [finelt/raw_validity.v](finelt/raw_validity.v): `downPiAppVal/Eq/EqVal`, `upPiAppVal/Eq/EqVal`, `transportPiEdgeVal/Eq/EqTy_sel`, `restrictPiAppVal/Eq/EqVal_sel`, `restrictVal/EqVal_PiCode` | Validity/*.agda |
| Fuel stability | [finelt/raw_validity.v](finelt/raw_validity.v): `fuel_stable` | Validity/Levels.agda: `shiftVl`, `shiftVTy` |
| Forward-PER all | [finelt/raw_validity.v](finelt/raw_validity.v): `fwd_per_all` | Validity/Props.agda: `goodStageFwd` |
| **Semantic Validity (envs/contexts)** | | |
| Fits relation | [finelt/typing_semantics.v](finelt/typing_semantics.v): `fits` (env matches Ctx in `wt`) | Model/Soundness.agda / SoundnessLemmas.agda: `Fits` |
| Soundness theorem | [finelt/typing_semantics.v](finelt/typing_semantics.v): `typing_EvalRel`, `conv_EvalRel` | Model/Soundness.agda: `theorem1`, `convSound'` |
| Inversion helpers | [finelt/typing_semantics.v](finelt/typing_semantics.v): `Lam_L1`, `InvTyp_Pi`, `InvTyp_Lam`, `InvTyp_App`, `InvConv_App_fun/arg`, `InvConv_beta`, `InvConv_eta` | Model/SoundnessLemmas.agda: `Lam-L1`, `InvTyp-Pi`, `InvTyp-Lam`, `InvTyp-App`, `InvConv-App-fun/arg`, `InvConv-beta`, `InvConv-funext` |
| **Adequacy & corollaries** | | |
| Sub validity (closing) | [finelt/adequacy.v](finelt/adequacy.v): `ValSub`, `ValSub_empty`, `ValSub_cons` | Adequacy/Bundle.agda (+ Records.agda): `ValidSub2`, `ValidSub2-empty`, `ValidSub2-extend` |
| Conv-sub validity | [finelt/adequacy.v](finelt/adequacy.v): `EqValSub`, `EqValSub_empty`, `EqValSub_cons`, `ValSub_EqValSub` | Adequacy/Bundle.agda: `ValidConvSub2`, `ValidConvSub2-refl`, `ValidConvSub2-extend` |
| Semantic typing | [finelt/adequacy.v](finelt/adequacy.v): `semantic_typing` (≈ AdqV2), `semantic_conv2` (≈ AdqE2) | Adequacy/Bundle.agda: `AdqV2`, `AdqE2` |
| Sem. typing rules | [finelt/adequacy.v](finelt/adequacy.v): `st_var`, `st_univ`, `st_tpi`, `st_abs`, `st_app`, `st_conv` | Adequacy/Bundle.agda: `adequacyV2-var/-U/-ty-Pi/-ty-Lam/-ty-App/-conv` |
| Sem. conv rules | [finelt/adequacy.v](finelt/adequacy.v): `sc_conv`, `sc_refl`, `sc_sym`, `sc_trans`, `sc_app1`, `sc_app2`, `sc_beta`, `sc_eta`, `sc_tpi` | Adequacy/Bundle.agda: `adequacyE2-conv/-refl/-sym/-trans/-App-fun/-App-arg/-beta/-funext/-Pi` |
| Bot environment | [finelt/adequacy.v](finelt/adequacy.v): `bot_env_lookup/cons/null`, `fits_bot_env`, `evalRel_Pi_trivial` | PiInjectivity.agda: `botEnv-lookup`, `botEnv-fits`, `evalRel-Pi-trivial` |
| Pi conversion | [finelt/adequacy.v](finelt/adequacy.v): `piConv` | PiInjectivity.agda: `piConv` / `convPi2` |
| Pi injectivity | [finelt/adequacy.v](finelt/adequacy.v): `piInjectivity` | PiInjectivity.agda: `piInjectivity` |
| **Reduction (HeadRed)** | | |
| Single-step head reduction | [syntax/reduction.v](syntax/reduction.v): `HeadRed1` (inductive: β at head, `App`-congruence) | Syntax/Reduction.agda: `HeadRed1` (`headred-beta`, `headred-app`) |
| Multi-step head reduction | [syntax/reduction.v](syntax/reduction.v): `HeadRed` (refl–trans closure of `HeadRed1`) | Syntax/Reduction.agda: `HeadRed` (`headred-refl`, `headred-step`) |
| Determinism | [syntax/reduction.v](syntax/reduction.v): `HeadRed1_det`, `HeadRed_tpi_det`, `HeadRed_succ_det` | Syntax/Reduction.agda: `HeadRed1-det` |
| `App` congruence | [syntax/reduction.v](syntax/reduction.v): `HeadRed_app` | Syntax/Reduction.agda: `HeadRed-App` |
| Π / U strip & contraction | [syntax/reduction.v](syntax/reduction.v): `HeadRed_tpi_eq`, `HeadRed1_tpi_expand`, `HeadRed1_tpi_contract`, `HeadRed_tpi_contract` | Syntax/Reduction.agda: `HeadRed-strip-Pi`; Validity/HeadRed.agda: `HeadRed1-not-U` |
| General multi-step reduction | [syntax/relations.v](syntax/relations.v): `step_n`, `multi` | Syntax/Reduction.agda: `Red` |

## Differences in the definitions

- **Element datatype / base codes.** Rocq's `Raw.elt` has 7 constructors, including primitive naturals `tnat`/`zero`/`succ`; Agda's `FinEl` has 4 (`Bot`, `UCode`, `FunEl`, `PiCode`) and omits naturals. Function tables are `list (elt * elt)` (Rocq) vs `List (Pair FinEl FinEl)` (Agda).
- **Rank.** The rank clauses differ. Rocq: `rk bot = 0`, base codes `tnat`/`tuniv`/`zero = 1`, `rk (succ v) = 1 + rk v`, `rk (tpi a f) = 1 + max (rk a) (rk_fun f)`, `rk (abs f) = 1 + rk_fun f`. Agda: `rk Bot = rk UCode = 0`, `rk (FunEl g) = rkFun g` (**no** `+1`), `rk (PiCode a f) = suc (max (rk a) (rkFun f))`; and `rkFun (cons …) = suc (max …)` whereas Rocq's `rk_fun` and Agda's `rkFun` differ on where the successor lands. Agda additionally keeps a *second* rank `RANK`/`RANKFun` (Domain/OrderStage.agda) for the staged order; Rocq has only `rk`, reused as the well-founded measure for `le`.
- **Set-valued (Agda) vs boolean (Rocq).** Agda states the order-theoretic predicates as Set-valued **structural** definitions returning `Top`/`Empty`/records: the order `LeCode`/`LeFunCode` (Domain/Order.agda), compatibility `Comp`/`CompFun`/`CompStepFun`/`CompStepStep` (Domain/OrderComp.agda), and coherence `Coherent`/`CoherentFun`/`CoherentFunTail` (Domain/OrderStage.agda); it also keeps a parallel Nat-valued decision layer `leFinEl`/`leFun` (= `leiC`, positive = holds, Domain/OrderEval.agda). Rocq collapses each into a single `bool`-valued function that is at once decision procedure and proposition (via `is_true`): `le`/`le_fun`, `compatible`/`compatible_fun`, `valid`/`valid_fun`. So Agda's per-pair compatibility `CompStepStep s t = Comp (fst s) (fst t) -> Comp (snd s) (snd t)` becomes the boolean `coherent_with g (u,v) = forallb (fun (uj,vj) => compatible u uj ==> compatible v vj) g`.
- **Coherence / validity bundling.** The two sides put non-emptiness and non-bot in different places. Agda bakes **non-emptiness into `CoherentFun`** (`CoherentFun nil = Empty`, `CoherentFun (cons …) = CoherentFunTail (cons …)`), while `CoherentFunTail nil = Top` permits an empty tail; per entry the record `CFTcons` carries `val-nbot : NotBot (snd p)`. Rocq instead splits non-emptiness off as a **separate** conjunct — `valid (abs f) = valid_fun f && ~~ is_nil f` — and folds the no-bot requirement into `valid_fun f = compatible_fun f f && no_bot_result f && forallb (fun (ui,vi) => valid ui && valid vi) f`. Hence Rocq `valid_fun` ↔ Agda `CoherentFunTail` and Rocq `valid (abs f)` ↔ Agda `CoherentFun g`. Rocq's `valid` is the standing well-formedness predicate, which *implies* coherence; Agda keeps `Coherent` separate from membership.
- **Sup / lub guarding.** Agda `Sup` **appends unconditionally** — `Sup (FunEl g) (FunEl h) = FunEl (append g h)`, `Sup (PiCode a f) (PiCode b g) = PiCode (Sup a b) (append f g)` — returning `Bot` only on shape mismatch, and relies on coherence preconditions at call sites. Rocq's `lub` **guards inline** — `lub (abs f) (abs g) = if compatible_fun f g then abs (f ++ g) else bot` (likewise for `tpi`).
- **Application.** Agda `EvalFun (cons p ps) u = EvalFun-step (leiC (fst p) u) (snd p) ps u` folds `Sup` over entries whose key fires; Rocq `app f u = lub_list (map (fun p => if le p.1 u then p.2 else bot) f)` computes the join via `lub_list`/`map` instead.
- **Membership / well-typed codes.** Agda `FinMem = finMemC` is the stage-collapse of a stage-indexed *structural* membership (the `MemStage` family), with `FinMemFun`/`FinMemAllU` structural over `FinMem`. Rocq `wt : elt -> elt -> Prop` is a plain **inductive** relation (`wt_bot`, `wt_tuniv`, `wt_tnat`, `wt_zero`, `wt_succ`, `wt_tpi`, `wt_abs`). Rocq has no `is_type` predicate.
- **Eta / conversion rules.** Rocq's eta is the constructor `c_eta` of the mutual `conv` ([syntax/typing.v](syntax/typing.v)); Agda's is `conv-funext` of `ConvTm` (Syntax/Typing.agda). Rocq additionally keeps a `conv` Lam-congruence rule (mirrored by the semantic `sc_abs`); Agda derives Lam congruence from funext, so it has no `conv-Lam`/`adequacyE2-Lam`.
- **`c_tpi` vs `conv-Pi` (Π-congruence rule).** The two rules differ in premise count and in which context the codomains are typed. Rocq's `c_tpi` has **6** premises: `typing Γ A0`, `typing Γ A1`, `typing (Γ,A0) B0`, `typing (Γ,A1) B1`, `conv Γ A0 A1`, `conv (Γ,A0) B0 B1` — i.e. each codomain is typed under *its own* domain (`B1` under `Γ,A1`). Agda's `conv-Pi` has **5**: `HasType G A`, `HasType (G,A) B`, `HasType (G,A) B'`, `ConvTm G A A'`, `ConvTm (G,A) B B'` — it omits the second domain's typing `HasType G A'` and types *both* codomains under the *first* domain (`extend G A`, never `extend G A'`).
- **Substitution.** Rocq mechanizes substitution Autosubst-style in [syntax/syntax.v](syntax/syntax.v); Agda factors it through Selection/Substitution/EvalSubstitution.

## Differences in the proof structure

- **Mutual block.** All of the value relation's auxiliary lemmas (up/down/restrict/headred) sit in one mutual block — the Level-6 SCC (~30 lemmas, see the topology comment in [finelt/raw_validity.v](finelt/raw_validity.v)).
- **Stratification: global fuel vs per-stage bundle.** The largest structural divergence. Agda builds an inductive `Stage` bundle (Validity/Stratified.agda) with per-pack `goodStage*` builders and a family of shift/lift/lower lemmas (Validity/Levels.agda). Rocq uses a single global-fuel `Val` datatype needing only one stability lemma, `fuel_stable` (≈ Agda's `shiftVl`/`shiftVTy`). This is what produces the Agda-only / Rocq-only lemmas listed above.
- **`EvalRel`.** Both are functions defined by structural recursion on the term (not inductive relations): Rocq `Fixpoint EvalRel : Tm n -> Env n -> elt -> Prop` ([finelt/raw_semantics.v](finelt/raw_semantics.v)), Agda `EvalRel : Expr n -> EnvApprox n -> FinEl -> Set` (Model/Eval.agda). In the `App` case Rocq guards with `is_bot b` and uses a singleton `a ↦ b`, whereas Agda case-splits on the constructor of `b` and uses the singleton `FunEl (cons (v,b) nil)`. The λ/Π body uses `app`/`valid`-bounded selection (Rocq) vs `EvalFun` (Agda); Rocq's Pi clause carries `valid a /\ valid_fun g` plus an edgewise body, and its λ clause carries `valid_fun g /\ ~~ is_nil g`.
- **Order termination.** Agda founds the mutual order block structurally over a rank/stage index (via `leiC`/OrderBridge), so no `{-# TERMINATING #-}` pragma is needed; Rocq discharges termination with `Equations … by wf (max (rk u) (rk v))` and a rank-bounded `le` proxy through `_app`/`_le_fun`.
- **Selection.** The minimal value-graph join used to type `wt_abs` and soundness is [finelt/selection.v](finelt/selection.v) (Rocq) ↔ Model/Selection.agda (+ SelectionRank.agda) (Agda).
- **Adequacy & Pi injectivity.** Both sides prove these in full. Agda: `adequacy2`/`piInjectivity` under Adequacy/Bundle.agda and PiInjectivity.agda. Rocq: [finelt/adequacy.v](finelt/adequacy.v) develops the same shape (`ValSub`, `EqValSub`, `semantic_typing`, `semantic_conv2`, the semantic rules `st_*`/`sc_*`, and the `bot_env`/`piConv`/`piInjectivity` corollary chain).
- **`sc_tpi` vs `adequacyE2-Pi` (Π-congruence for conversion).** The two sides differ in how many premises the rule threads. Agda's `adequacyE2-Pi` takes only four: the two conversion derivations `ConvTm A A'`, `ConvTm B B'` and the two semantic-conversion IHs `AdqE2 A A'`, `AdqE2 B B'` — because the `AdqE2` bundle is symmetric and already packages each endpoint's validity. Rocq's `sc_tpi` takes twelve: the same two `conv`s, plus the **four component `typing` derivations** (`A0`, `A1`, `B0`, `B1`) and **four standalone `semantic_typing` facts** for those same components, plus the two `semantic_conv2` IHs. The extra typing/`semantic_typing` premises are needed because Rocq's `semantic_conv2` does not by itself re-supply each endpoint's per-side typing — they are required to rebuild the whole-Π conversion (`c_tpi`, itself a six-premise rule) and to obtain `Val` of each component type at the right rank.

## Top-level lemma correspondence

Only key results are listed; pure plumbing/helper lemmas are omitted. Agda
sources live under `~/github/agda/domain-semantics/MIN/`.

The Agda→Rocq naming conventions are those of the definition table above
(`FinMem`↔`wt`, `Coherent`/`CoherentFun`↔`valid`/`valid_fun`, `LeCode`↔`le`,
`Comp`↔`compatible`, `Sup`↔`lub`, `EvalFun`↔`app`, `HasType`/`ConvTm`↔`typing`/`conv`,
`FinEl`↔`elt`, `FinFun`↔`list (elt * elt)`).

### raw_semantics.v ↔ Model/Eval.agda (the EvalRel ideal)

| Rocq | Agda |
|------|------|
| `EvalRel_valid` | `EvalRel-coh` |
| `EvalRel_mono_env` | `EvalRel-mon-env` |
| `EvalRel_bot` | `EvalRel-Bot` |
| `EvalRel_down` | `EvalRel-down` |
| `EvalRel_compatible` | `EvalRel-Comp` |
| `EvalRel_sup` | `EvalRel-Sup` |
| `EvalRel_compatible_ext` | `EvalRel-Comp-ext` |
| `EvalRel_ideal` | `EvalRel-ideal-Comp` |

### eval_substitution.v ↔ Model/EvalSubstitution.agda

| Rocq | Agda |
|------|------|
| `EvalRel_ren` | `EvalRel-ren` |
| `EvalRel_wk` | `EvalRel-wk` |
| `EvalRel_unwk` | `EvalRel-unwk` |
| `SubRel_lift` | `SubRel-lift` |
| `EvalRel_subst` | `EvalRel-subst` |
| `EvalRel_subst1_backwards` | `EvalRel-subst1-backward` |
| `MaxSubRel_lift` | `MaxSubRel-lift` |
| `EvalRel_subst_forward_max` | `EvalRel-subst-forward-max` |
| `EvalRel_subst1_forward` | `EvalRel-subst1-forward-bounded` |
| `combine_fwd` | `combineFwd` |
| `SubRel_bot_env` | `SubRel-botEnv` |
| `SubRel_sup_env` | `SubRel-supEnv` |

### selection.v ↔ Model/Selection.agda (+ SelectionRank.agda)

| Rocq | Agda |
|------|------|
| `sel_skip_all` | `sel-skip-all` |
| `singleton_selection` | `singleton-selection` |
| `valid_Selection` | `Coherent-Selection` |
| `wt_Selection` | `FinMem-Selection` |
| `wt_Selection_cod` | `FinMem-Selection-codomain` |
| `wt_Selection_codU` | `FinMem-Selection-UCode` |
| `selectionBelow` | `selectionBelow` |
| `Selection_le_app` | `Selection-le-EvalFun` |
| `rk_Selection_key` | `Selection-RANK-u` (SelectionRank.agda) |
| `rk_Selection_val` | `Selection-RANK-v` (SelectionRank.agda) |

### raw_validity.v ↔ Validity/*.agda (the stratified value PER)

Public faces in Validity/Levels.agda and Validity/Props.agda.

| Rocq | Agda |
|------|------|
| `Val_EqVal` | `Val2-to-EqVal2-pub` |
| `ValTy_EqValTy` | `ValTy2-to-EqValTy2-pub` |
| `EqVal_sym` | `EqVal2-sym-pub` |
| `EqVal_trans` | `EqVal2-trans-pub` |
| `EqValTy_sym` | `EqValTy2-sym-pub` |
| `EqValTy_trans` | `EqValTy2-trans-pub` |
| `Val_EqVal_fwd` | `Val2-EqValTy2-fwd-pub` |
| `EqVal_EqVal_fwd` | `EqVal2-EqValTy2-fwd-pub` |
| `Val_Bot` | `Val2-Bot-pub` |
| `EqVal_Bot` | `EqVal2-Bot-pub` |
| `Val_beta_expand` | `Val2-beta-expand-pub` |
| `Val_headred_contract` | `Val2-headred-contract` |
| `EqVal_headred_expand` | `EqVal2-headred-expand` |
| `EqVal_headred_contract` | `EqVal2-headred-contract` |
| `upVal` / `downVal` / `restrictVal` | `upVal2-pub` / `downVal2-pub` / `restrictVal2-pub` |
| `upEqVal` / `downEqVal` / `restrictEqVal` | `upEqVal2-pub` / `downEqVal2-pub` / `restrictEqVal2-pub` |
| `fuel_stable` | `shiftVl` / `shiftVTy` (Validity/Levels.agda) |
| `fwd_per_all` | `goodStageFwd` (Validity/Props.agda) |

### typing_semantics.v ↔ Model/Soundness.agda (+ SoundnessLemmas.agda)

| Rocq | Agda |
|------|------|
| `typing_EvalRel` (Theorem 1) | `theorem1` |
| `conv_EvalRel` | `convSound'` |
| `fits_tail` | `Fits-tail` |
| `fits_valid_env` | `Fits-CoherentEnv` |
| `fits_var` | `Fits-var` |
| `Lam_L1` | `Lam-L1` |
| `InvTyp_Lam` | `InvTyp-Lam` |
| `InvTyp_App` | `InvTyp-App` |
| `InvTyp_Pi` | `InvTyp-Pi` |
| `InvConv_beta` | `InvConv-beta` |
| `InvConv_eta` | `InvConv-funext` |
| `InvConv_App_fun` | `InvConv-App-fun` |
| `InvConv_App_arg` | `InvConv-App-arg` |

### adequacy.v ↔ Adequacy/Bundle.agda (+ PiInjectivity.agda)

`semantic_typing` ≈ AdqV2, `semantic_conv2` ≈ AdqE2.

| Rocq | Agda |
|------|------|
| `st_var` | `adequacyV2-var` |
| `st_univ` | `adequacyV2-U` |
| `st_tpi` | `adequacyV2-ty-Pi` |
| `st_abs` | `adequacyV2-ty-Lam` |
| `st_app` | `adequacyV2-ty-App` |
| `st_conv` | `adequacyV2-conv` |
| `sc_conv` | `adequacyE2-conv` |
| `sc_refl` | `adequacyE2-refl` |
| `sc_sym` | `adequacyE2-sym` |
| `sc_trans` | `adequacyE2-trans` |
| `sc_app1` | `adequacyE2-App-fun` |
| `sc_app2` | `adequacyE2-App-arg` |
| `sc_beta` | `adequacyE2-beta` |
| `sc_eta` | `adequacyE2-funext` |
| `sc_tpi` | `adequacyE2-Pi` |
| `piConv` | `convPi2` / `piConv` (PiInjectivity.agda) |
| `piInjectivity` | `piInjectivity` (PiInjectivity.agda) |
| `evalRel_Pi_trivial` | `evalRel-Pi-trivial` (PiInjectivity.agda) |
| `bot_env_lookup` | `botEnv-lookup` (PiInjectivity.agda) |
| `fits_bot_env` | `botEnv-fits` (PiInjectivity.agda) |
| `subject_red1` / `subject_red` | `subject-red1` (SubjectReduction.agda) |
| `HeadRed1_app_inv` | (inlined in `subject-red1`) |

### Lemmas without a counterpart

**Rocq-only** (no analogous Agda lemma):

- All ℕ-related results — the MIN Agda fragment has no nat/succ/nrec:
  `st_nat`, `st_zero`, `st_succ`, `st_nrec`, `sc_succ`, `sc_nrec_Z`, `sc_nrec_S`,
  `InvTyp_succ`, `InvConv_succ`, `InvConv_nrec_Z`, `InvConv_nrec_S`,
  `EvalRel_tpi_*`, `EvalRel_succ_*`, `EvalRel_abs_*` (intro/inv helpers).
- `sc_abs` — Rocq keeps a Lam congruence conversion rule; the Agda conversion
  judgment derives it from funext (`conv-funext`), so there is no `adequacyE2-Lam`.
- `fold_edge_fwd` (eval_substitution.v) — bridges Coq's global-fuel `Val` to the
  edge-forward construction; the Agda rank-relative `Stage` makes it unnecessary.
- `SubRel_singleton_env` / `singleton_env_*` (eval_substitution.v) — Coq
  packaging with no standalone Agda lemma.
- `progress` / `progress_gen` / `canonical_pi` / `neutral_not_closed` and the
  non-confusion facts (`tnat_not_tpi`, `tuniv_not_tpi`) (adequacy.v), with the
  per-former type inversions (`typing_univ_inv`, `typing_nat_inv`,
  `typing_tpi_inv`, `typing_zero_inv`, `typing_succ_inv`) in syntax/typing.v —
  the operational progress theorem for closed terms; the Agda MIN fragment ports
  subject reduction but not progress.

**Agda-only** (no analogous Rocq lemma):

- `goodStage` / `buildStage` / `Stage` / `trivBundle` (Validity/Stratified.agda)
  and the per-pack `goodStage*` builders (`goodStageSymTrans`, `goodStageSup`,
  `goodStageRefl`, `goodStageTransport`, `goodStageBeta`, `goodStageHeadRed`) —
  these assemble the inductive `Stage` bundle; Rocq uses a single global-fuel
  `Val` datatype, so there is no per-stage bundle to build.
- shift/lift/lower families in Validity/Levels.agda (`shiftVl`, `liftVTy`, …)
  beyond `fuel_stable` — Rocq's global fuel needs only the stability lemma.
