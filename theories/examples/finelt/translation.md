 ============================================================
 Translations of theorem statements (Agda MIN/  ↔  Rocq finelt)
 ------------------------------------------------------------

Translation conventions (Agda → Rocq):
     FinMem u a              ≈  wt u a
     FinMem b UCode          ≈  wt b tuniv              (some i)
     Coherent u              ≈  valid u                 (implicit in wt)
     CoherentFun g           ≈  valid_fun g /\ g <> nil (implicit in wt (abs g) ..)
     CoherentFunTail f       ≈  valid_fun f             (implicit in wt (tpi _ f) ..)
     FinMemFun g b f         ≈  wt (abs g) (tpi b f)
     FinMemAllU f b          ≈  wt (tpi b f) tuniv (codomains in U_i)
     LeCode u v              ≈  le u v
     LeFunCode f g           ≈  le_fun f g
     Comp u v                ≈  compatible u v
     Sup u v = w             ≈  lub u v = w
     EvalFun f u = v         ≈  app f u = v
     subst1 B N              ≈  B[N..]
     HasType / ConvTm        ≈  typing / conv
     HeadRed                 ≈  HeadRed (multi reduction)
     FinEl                 elt
     FinFun                list (elt * elt)
     Bot / Sup u v         bot / lub u v
     FinMem-Sup-element     wt_lub

 ============================================================
 Top-level lemma correspondence (Rocq finelt  ↔  Agda MIN/)
 ------------------------------------------------------------

 Agda sources live under ~/github/agda/domain-semantics/MIN/.
 Only key results are listed; pure plumbing/helper lemmas are omitted.

 ## raw_semantics.v  ↔  Model/Eval.agda  (the EvalRel ideal)

 | Rocq                          | Agda                       |
 |-------------------------------|----------------------------|
 | EvalRel_valid                 | EvalRel-coh                |
 | EvalRel_mono_env              | EvalRel-mon-env            |
 | EvalRel_bot                   | EvalRel-Bot                |
 | EvalRel_down                  | EvalRel-down               |
 | EvalRel_compatible            | EvalRel-Comp               |
 | EvalRel_sup                   | EvalRel-Sup                |
 | EvalRel_compatible_ext        | EvalRel-Comp-ext           |
 | EvalRel_ideal                 | EvalRel-ideal-Comp         |

 ## eval_substitution.v  ↔  Model/EvalSubstitution.agda

 | Rocq                          | Agda                          |
 |-------------------------------|-------------------------------|
 | EvalRel_ren                   | EvalRel-ren                   |
 | EvalRel_wk                    | EvalRel-wk                    |
 | EvalRel_unwk                  | EvalRel-unwk                  |
 | SubRel_lift                   | SubRel-lift                   |
 | EvalRel_subst                 | EvalRel-subst                 |
 | EvalRel_subst1_backwards      | EvalRel-subst1-backward       |
 | MaxSubRel_lift                | MaxSubRel-lift                |
 | EvalRel_subst_forward_max     | EvalRel-subst-forward-max     |
 | EvalRel_subst1_forward        | EvalRel-subst1-forward-bounded|
 | combine_fwd                   | combineFwd                    |
 | SubRel_bot_env                | SubRel-botEnv                 |
 | SubRel_sup_env                | SubRel-supEnv                 |

 ## selection.v  ↔  Model/Selection.agda  (+ SelectionRank.agda)

 | Rocq                          | Agda                          |
 |-------------------------------|-------------------------------|
 | sel_skip_all                  | sel-skip-all                  |
 | singleton_selection           | singleton-selection           |
 | valid_Selection               | Coherent-Selection            |
 | wt_Selection                  | FinMem-Selection              |
 | wt_Selection_cod              | FinMem-Selection-codomain     |
 | wt_Selection_codU             | FinMem-Selection-UCode        |
 | selectionBelow                | selectionBelow                |
 | Selection_le_app              | Selection-le-EvalFun          |
 | rk_Selection_key              | Selection-RANK-u  (SelectionRank.agda) |
 | rk_Selection_val              | Selection-RANK-v  (SelectionRank.agda) |

 ## raw_validity.v  ↔  Validity/*.agda  (the stratified value PER)
 (public faces in Validity/Levels.agda and Validity/Props.agda)

 | Rocq                          | Agda                          |
 |-------------------------------|-------------------------------|
 | Val_EqVal                     | Val2-to-EqVal2-pub            |
 | ValTy_EqValTy                 | ValTy2-to-EqValTy2-pub        |
 | EqVal_sym                     | EqVal2-sym-pub                |
 | EqVal_trans                   | EqVal2-trans-pub              |
 | EqValTy_sym                   | EqValTy2-sym-pub              |
 | EqValTy_trans                 | EqValTy2-trans-pub            |
 | Val_EqVal_fwd                 | Val2-EqValTy2-fwd-pub         |
 | EqVal_EqVal_fwd               | EqVal2-EqValTy2-fwd-pub       |
 | Val_Bot                       | Val2-Bot-pub                  |
 | EqVal_Bot                     | EqVal2-Bot-pub                |
 | Val_beta_expand               | Val2-beta-expand-pub          |
 | Val_headred_contract          | Val2-headred-contract         |
 | EqVal_headred_expand          | EqVal2-headred-expand         |
 | EqVal_headred_contract        | EqVal2-headred-contract       |
 | upVal / downVal / restrictVal | upVal2-pub / downVal2-pub / restrictVal2-pub |
 | upEqVal / downEqVal / restrictEqVal | upEqVal2-pub / downEqVal2-pub / restrictEqVal2-pub |
 | fuel_stable                   | shiftVl / shiftVTy  (Validity/Levels.agda) |
 | fwd_per_all                   | goodStageFwd  (Validity/Props.agda) |

 ## typing_semantics.v  ↔  Model/Soundness.agda (+ Model/SoundnessLemmas.agda)

 | Rocq                          | Agda                          |
 |-------------------------------|-------------------------------|
 | typing_EvalRel  (Theorem 1)   | theorem1  (Soundness.agda)    |
 | conv_EvalRel                  | convSound'  (Soundness.agda)  |
 | fits_tail                     | Fits-tail                     |
 | fits_valid_env                | Fits-CoherentEnv              |
 | fits_var                      | Fits-var                      |
 | Lam_L1                        | Lam-L1                        |
 | InvTyp_Lam                    | InvTyp-Lam                    |
 | InvTyp_App                    | InvTyp-App                    |
 | InvTyp_Pi                     | InvTyp-Pi                     |
 | InvConv_beta                  | InvConv-beta                  |
 | InvConv_eta                   | InvConv-funext                |
 | InvConv_App_fun               | InvConv-App-fun               |
 | InvConv_App_arg               | InvConv-App-arg               |

 ## adequacy.v  ↔  Adequacy/Bundle.agda (+ PiInjectivity.agda)
 (semantic_typing ≈ AdqV2, semantic_conv2 ≈ AdqE2)

 | Rocq                          | Agda                          |
 |-------------------------------|-------------------------------|
 | st_var                        | adequacyV2-var                |
 | st_univ                       | adequacyV2-U                  |
 | st_tpi                        | adequacyV2-ty-Pi              |
 | st_abs                        | adequacyV2-ty-Lam             |
 | st_app                        | adequacyV2-ty-App             |
 | st_conv                       | adequacyV2-conv               |
 | sc_conv                       | adequacyE2-conv               |
 | sc_refl                       | adequacyE2-refl               |
 | sc_sym                        | adequacyE2-sym                |
 | sc_trans                      | adequacyE2-trans              |
 | sc_app1                       | adequacyE2-App-fun            |
 | sc_app2                       | adequacyE2-App-arg            |
 | sc_beta                       | adequacyE2-beta               |
 | sc_eta                        | adequacyE2-funext             |
 | sc_tpi                        | adequacyE2-Pi                 |
 | piConv                        | convPi2 / piConv (PiInjectivity.agda) |
 | piInjectivity                 | piInjectivity  (PiInjectivity.agda) |
 | evalRel_Pi_trivial            | evalRel-Pi-trivial  (PiInjectivity.agda) |
 | bot_env_lookup                | botEnv-lookup  (PiInjectivity.agda) |
 | fits_bot_env                  | botEnv-fits  (PiInjectivity.agda) |

 ============================================================
 Lemmas without a counterpart
 ------------------------------------------------------------

 Rocq-only (no analogous Agda lemma):
   * All ℕ-related results — the MIN Agda fragment has no nat/succ/nrec:
       st_nat, st_zero, st_succ, st_nrec,
       sc_succ, sc_nrec_Z, sc_nrec_S,
       InvTyp_succ, InvConv_succ, InvConv_nrec_Z, InvConv_nrec_S,
       EvalRel_tpi_*, EvalRel_succ_*, EvalRel_abs_* (intro/inv helpers).
   * sc_abs — Rocq keeps a Lam congruence conversion rule; the Agda
       conversion judgment derives it from funext, so there is no
       adequacyE2-Lam.
   * fold_edge_fwd  (eval_substitution.v) — bridges Coq's global-fuel Val
       to the edge-forward construction; the Agda rank-relative Stage makes
       it unnecessary.
   * SubRel_singleton_env / singleton_env_* (eval_substitution.v) — Coq
       packaging with no standalone Agda lemma.

 Agda-only (no analogous Rocq lemma):
   * goodStage / buildStage / Stage / trivBundle (Validity/Stratified.agda)
       and the per-pack goodStage* builders (goodStageSymTrans, goodStageSup,
       goodStageRefl, goodStageTransport, goodStageBeta, goodStageHeadRed) —
       these assemble the inductive Stage bundle; Rocq uses a single
       global-fuel Val datatype, so there is no per-stage bundle to build.
   * shift/lift/lower families in Validity/Levels.agda (shiftVl, liftVTy, …)
       beyond fuel_stable — Rocq's global fuel needs only the stability lemma.
