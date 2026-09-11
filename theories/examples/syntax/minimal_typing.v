(** * minimal_typing.v: a minimal presentation of the syntactic type system

    [typing.v] defines the mutually inductive judgments [typing] / [conv] /
    [ctx].  Many of their premises are *presuppositions* -- they only restate
    well-formedness facts that the other premises of the same rule already
    imply -- and are therefore admissible.  This file states the minimal
    versions [mtyping] / [mconv] / [mctx] and proves them equivalent to the
    originals.

    Three tools make premises admissible; the first has to be established
    here, the other two already exist in [typing.v].

    - (R) REGULARITY, [typing_regularity : Γ ⊢e M ∈ A -> Γ ⊢e A ∈ tuniv].
      Proved below; it is what makes every "[typing Γ A tuniv] alongside
      [typing Γ a A]" premise redundant.
    - (C) CONTEXT WELL-FORMEDNESS, [typing_ctx] / [conv_ctx] followed by
      inversion on [ctx (Γ ++ A)]: any premise judged in the extended context
      [Γ ++ A] already carries [typing Γ A tuniv].  Packaged below as
      [typing_ext_dom] / [conv_ext_dom].
    - (T) [conv_typing : Γ ⊢e M ≡ N ∈ A -> Γ ⊢e M ∈ A /\ Γ ⊢e N ∈ A]: a
      congruence rule need not also carry typings for the two sides.  Several
      comments in [typing.v] already flag their premises as admissible on
      exactly this ground ([c_ncase], [c_abs], [c_fix_cong], [c_tid], [c_rfl],
      [c_jcase]); those premises are kept there because the adequacy proof
      wants the *derivations*, not because the relation needs them.

    A fourth, used once: [ctx_conv_typing] transports a judgment from [Γ ++ A0]
    to [Γ ++ A1] along [Γ ⊢e A0 ≡ A1 ∈ tuniv], which is what makes the
    *right-hand* codomain premise of [c_tpi] / [c_tsig] / [c_tpi_prop]
    admissible.

    See [Sharpness] at the end for witnesses that the preconditions which
    remain cannot be dropped. *)

Require Import ssreflect.

From Stdlib Require Export Logic.FunctionalExtensionality.
From Stdlib Require Import Program.Equality.

Require Export autosubst.core.
Require Export autosubst.fintype.
Require Import syntax.syntax.
Require Import syntax.typing.

Import SyntaxNotations.
Import SubstNotations.
Import typing.Notations.

Open Scope syntax_scope.

(* ------------------------------------------------------------------ *)
(** * Tool (C): the domain of an extended context is a type            *)
(* ------------------------------------------------------------------ *)

Lemma ctx_extend_inv {n} {Γ : Ctx n} {A} :
  ctx (Γ ++ A) -> ctx Γ /\ Γ ⊢e A ∈ tuniv.
Proof. move=> h. dependent destruction h. by split. Qed.

(** Any judgment in an extended context already says the domain is a type. *)
Lemma typing_ext_dom {n} {Γ : Ctx n} {A M B} :
  Γ ++ A ⊢e M ∈ B -> Γ ⊢e A ∈ tuniv.
Proof.
  move=> h.
  by move: (ctx_extend_inv (@typing_ctx _ _ _ _ h)) => [_ ?].
Qed.

Lemma conv_ext_dom {n} {Γ : Ctx n} {A M N B} :
  Γ ++ A ⊢e M ≡ N ∈ B -> Γ ⊢e A ∈ tuniv.
Proof.
  move=> h.
  by move: (ctx_extend_inv (@conv_ctx _ _ _ _ _ h)) => [_ ?].
Qed.

(* ------------------------------------------------------------------ *)
(** * Tool (T): the two sides of a conversion are typed                *)
(* ------------------------------------------------------------------ *)

Lemma conv_typing1 {n} {Γ : Ctx n} {M N A} : Γ ⊢e M ≡ N ∈ A -> Γ ⊢e M ∈ A.
Proof. move=> h. by move: (conv_typing h) => [? _]. Qed.

Lemma conv_typing2 {n} {Γ : Ctx n} {M N A} : Γ ⊢e M ≡ N ∈ A -> Γ ⊢e N ∈ A.
Proof. move=> h. by move: (conv_typing h) => [_ ?]. Qed.

(* ------------------------------------------------------------------ *)
(** * Tool (R): regularity                                             *)
(* ------------------------------------------------------------------ *)

(** Instantiating the last variable of an extended context. *)
Lemma typing_subst1 {n} {Γ : Ctx n} {A : Tm n} {B C : Tm (S n)} {M : Tm n} :
  Γ ++ A ⊢e B ∈ C -> Γ ⊢e M ∈ A -> Γ ⊢e B[M..] ∈ C[M..].
Proof.
  move=> hB hM.
  have cG : ctx Γ by (eapply typing_ctx; exact hM).
  eapply (substitution_tm (Γ ++ A) B C Γ (M..)); [ exact hB | | exact cG ].
  eapply typing_subst_cons;
    [ asimpl; exact hM | apply typing_subst_id; exact cG ].
Qed.

(** The type of a well-typed term is itself a type.  This is the lemma that
    makes the [typing Γ A tuniv] premises of [t_tid], [t_rfl], [t_jcase],
    [c_rfl], [c_jcase_beta], ... admissible, and it is also what lets
    [t_abs]/[c_beta] drop their codomain premise. *)
Lemma typing_regularity {n} (Γ : Ctx n) M A :
  Γ ⊢e M ∈ A -> Γ ⊢e A ∈ tuniv.
Proof.
  induction 1.
  (* t_var *)
  all: try by (apply ctx_typing_lookup; assumption).
  (* t_conv (via Tool T), the sort-valued conclusions, and the cases whose
     type is rebuilt by a constructor from the premises at hand:
     t_abs, t_rfl, t_mkpair, t_fix, t_pfst, t_tpi_prop, t_star, ... *)
  all: try by eauto using t_univ, t_nat, t_prop, t_unit, t_tpi, t_tsig, t_tid,
                          typing_ctx, conv_typing2.
  (* t_jcase: the result type is the motive applied to the two endpoints and
     the proof; the [tid] premise is what pins down [A], [a] and [b]. *)
  all: try (match goal with
            | [ Hp : ?G ⊢e ?p ∈ tid ?A ?a ?b
                |- ?G ⊢e app (app (app ?C ?a) ?b) ?p ∈ tuniv ] =>
                by eapply (motive_app_typing G A a b C p); eassumption
            end).
  (* t_app and t_case: substitute the argument into the codomain *)
  all: try (match goal with
            | [ HB : _ ++ ?A ⊢e ?B ∈ tuniv, HM : _ ⊢e ?M ∈ ?A
                |- _ ⊢e ?B[?M..] ∈ tuniv ] =>
                by move: (typing_subst1 HB HM) => hh; asimpl in hh; exact hh
            end).
  (* t_psnd: substitute the FIRST PROJECTION into the codomain *)
  all: (match goal with
        | [ HA : ?G ⊢e ?A ∈ tuniv, HB : _ ++ ?A ⊢e ?B ∈ tuniv,
            HM : ?G ⊢e ?M ∈ tsig ?A ?B |- _ ] =>
            have hf : G ⊢e pfst M ∈ A := @t_pfst _ G A B M HA HB HM;
            by move: (typing_subst1 HB hf) => hh; asimpl in hh; exact hh
        end).
Qed.

(* ------------------------------------------------------------------ *)
(** * Premise inversion for the three type formers

    [typing.v]'s [typing_tpi_inv] / [typing_tsig_inv] / [typing_tid_inv]
    recover only the *type* of a type former.  What follows recovers its
    PREMISES, which is what makes the domain/codomain presuppositions of
    [t_app], [t_fix], [t_pfst], [t_psnd], [c_app1], [c_app2], [c_pfst],
    [c_psnd], [c_pair_eta], [c_fix], [c_fix_cong] and the endpoint
    presuppositions of [t_jcase] / [c_jcase] admissible.

    Only three rules can conclude with a type former as subject -- its own
    formation rule, [t_conv] and [t_prop_u] -- so each is a three-case
    [dependent induction].  For [tpi] the formation rule comes in two flavours
    ([t_tpi] and [t_tpi_prop]); the [Prop] one is brought up to [tuniv] by
    [t_prop_u] on the codomain. *)

Lemma typing_tpi_prem_inv {n} {Γ : Ctx n} {A B T} :
  Γ ⊢e tpi A B ∈ T -> Γ ⊢e A ∈ tuniv /\ Γ ++ A ⊢e B ∈ tuniv.
Proof.
  move=> h; dependent induction h.
  - (* t_conv *) first [ eapply IHh; reflexivity | exact IHh ].
  - (* t_tpi *) by split.
  - (* t_prop_u *) first [ eapply IHh; reflexivity | exact IHh ].
  - (* t_tpi_prop: the codomain lands in [tprop]; lift it *)
    split; [ assumption | by apply: t_prop_u ].
Qed.

Lemma typing_tsig_prem_inv {n} {Γ : Ctx n} {A B T} :
  Γ ⊢e tsig A B ∈ T -> Γ ⊢e A ∈ tuniv /\ Γ ++ A ⊢e B ∈ tuniv.
Proof.
  move=> h; dependent induction h.
  - (* t_conv *) first [ eapply IHh; reflexivity | exact IHh ].
  - (* t_tsig *) by split.
  - (* t_prop_u *) first [ eapply IHh; reflexivity | exact IHh ].
Qed.

Lemma typing_tid_prem_inv {n} {Γ : Ctx n} {A a b T} :
  Γ ⊢e tid A a b ∈ T -> Γ ⊢e A ∈ tuniv /\ Γ ⊢e a ∈ A /\ Γ ⊢e b ∈ A.
Proof.
  move=> h; dependent induction h.
  - (* t_conv *) first [ eapply IHh; reflexivity | exact IHh ].
  - (* t_tid *) by repeat split.
  - (* t_prop_u *) first [ eapply IHh; reflexivity | exact IHh ].
Qed.

(** The same three, read off a term rather than off the code: the composites
    that the reconstruction of the minimal system actually uses. *)

Lemma typing_pi_dom {n} {Γ : Ctx n} {A B N} :
  Γ ⊢e N ∈ tpi A B -> Γ ⊢e A ∈ tuniv.
Proof.
  move=> h.
  by move: (typing_tpi_prem_inv (typing_regularity _ _ _ h)) => [? _].
Qed.

Lemma typing_pi_cod {n} {Γ : Ctx n} {A B N} :
  Γ ⊢e N ∈ tpi A B -> Γ ++ A ⊢e B ∈ tuniv.
Proof.
  move=> h.
  by move: (typing_tpi_prem_inv (typing_regularity _ _ _ h)) => [_ ?].
Qed.

Lemma typing_sig_dom {n} {Γ : Ctx n} {A B M} :
  Γ ⊢e M ∈ tsig A B -> Γ ⊢e A ∈ tuniv.
Proof.
  move=> h.
  by move: (typing_tsig_prem_inv (typing_regularity _ _ _ h)) => [? _].
Qed.

Lemma typing_sig_cod {n} {Γ : Ctx n} {A B M} :
  Γ ⊢e M ∈ tsig A B -> Γ ++ A ⊢e B ∈ tuniv.
Proof.
  move=> h.
  by move: (typing_tsig_prem_inv (typing_regularity _ _ _ h)) => [_ ?].
Qed.

Lemma typing_id_dom {n} {Γ : Ctx n} {A a b p} :
  Γ ⊢e p ∈ tid A a b -> Γ ⊢e A ∈ tuniv.
Proof.
  move=> h.
  by move: (typing_tid_prem_inv (typing_regularity _ _ _ h)) => [? _].
Qed.

Lemma typing_id_lhs {n} {Γ : Ctx n} {A a b p} :
  Γ ⊢e p ∈ tid A a b -> Γ ⊢e a ∈ A.
Proof.
  move=> h.
  by move: (typing_tid_prem_inv (typing_regularity _ _ _ h)) => [_ [? _]].
Qed.

Lemma typing_id_rhs {n} {Γ : Ctx n} {A a b p} :
  Γ ⊢e p ∈ tid A a b -> Γ ⊢e b ∈ A.
Proof.
  move=> h.
  by move: (typing_tid_prem_inv (typing_regularity _ _ _ h)) => [_ [_ ?]].
Qed.

(* ================================================================== *)
(** * The minimal type system

    Same rules, same order, same names with an [m] prefix; each rule keeps
    only the premises that are not admissible.  The comment on each rule names
    what was dropped and which tool recovers it. *)
(* ================================================================== *)

Inductive mtyping : forall {n} (Γ : Ctx n), Tm n -> Tm n -> Prop :=
  | mt_var n (Γ : Ctx n) x :
    mctx Γ ->
    mtyping Γ (var x) (lookup x Γ)

  | mt_conv n (Γ : Ctx n) M A B :
    mtyping Γ M A ->
    mconv Γ A B tuniv ->
    mtyping Γ M B

  (* dropped: [Γ ⊢e A ∈ tuniv] (C), [Γ ++ A ⊢e B ∈ tuniv] (R) *)
  | mt_abs n (Γ : Ctx n) A B N :
    mtyping (ctx_extend Γ A) N B ->
    mtyping Γ (abs A N) (tpi A B)

  (* dropped: both presuppositions, from [N]'s Pi type (R + premise inv) *)
  | mt_app n (Γ : Ctx n) A B N M :
    mtyping Γ N (tpi A B) ->
    mtyping Γ M A ->
    mtyping Γ (app N M) B[M..]

  | mt_nat n (Γ : Ctx n) :
    mctx Γ ->
    mtyping Γ tnat tuniv

  | mt_zero n (Γ : Ctx n) :
    mctx Γ ->
    mtyping Γ zero tnat

  | mt_succ n (Γ : Ctx n) M :
    mtyping Γ M tnat ->
    mtyping Γ (succ M) tnat

  (* nothing dropped: the motive [T] is not recoverable from [T[zero..]] *)
  | mt_case n (Γ : Ctx n) (T : Tm (S n)) M M0 M1 :
    mtyping (ctx_extend Γ tnat) T tuniv ->
    mtyping Γ M tnat ->
    mtyping Γ M0 (T[zero..]) ->
    mtyping (ctx_extend Γ tnat) M1 T[rho] ->
    mtyping Γ (ncase M M0 M1) (T[M..])

  (* dropped: [Γ ⊢e A ∈ tuniv] (R + premise inv on the step function) *)
  | mt_fix n (Γ : Ctx n) A g :
    mtyping Γ g (tpi A A⟨↑⟩) ->
    mtyping Γ (fix_ g) A

  (* dropped: [Γ ⊢e A ∈ tuniv] (R on an endpoint) *)
  | mt_tid n (Γ : Ctx n) A a b :
    mtyping Γ a A ->
    mtyping Γ b A ->
    mtyping Γ (tid A a b) tuniv

  (* dropped: [Γ ⊢e A ∈ tuniv] (R) *)
  | mt_rfl n (Γ : Ctx n) A a :
    mtyping Γ a A ->
    mtyping Γ (rfl a) (tid A a a)

  (* dropped: [Γ ⊢e A ∈ tuniv] and both endpoint typings, all three read off
     the proof's [tid] type (R + premise inv) *)
  | mt_jcase n (Γ : Ctx n) A a b C d p :
    mtyping Γ C (motive_ty A) ->
    mtyping Γ d (base_ty A C) ->
    mtyping Γ p (tid A a b) ->
    mtyping Γ (jcase C d p) (app (app (app C a) b) p)

  (* dropped: [Γ ⊢e A ∈ tuniv] (C) *)
  | mt_tpi n (Γ : Ctx n) A B :
    mtyping (ctx_extend Γ A) B tuniv ->
    mtyping Γ (tpi A B) tuniv

  | mt_univ n (Γ : Ctx n) :
    mctx Γ ->
    mtyping Γ tuniv tuniv

  (* dropped: [Γ ⊢e A ∈ tuniv] (C) *)
  | mt_tsig n (Γ : Ctx n) A B :
    mtyping (ctx_extend Γ A) B tuniv ->
    mtyping Γ (tsig A B) tuniv

  (* dropped: [Γ ⊢e A ∈ tuniv] (C) *)
  | mt_mkpair n (Γ : Ctx n) A B M N :
    mtyping (ctx_extend Γ A) B tuniv ->
    mtyping Γ M A ->
    mtyping Γ N B[M..] ->
    mtyping Γ (mkpair M N) (tsig A B)

  (* dropped: both presuppositions (R + premise inv on the Sigma type) *)
  | mt_pfst n (Γ : Ctx n) A B M :
    mtyping Γ M (tsig A B) ->
    mtyping Γ (pfst M) A

  (* dropped: both presuppositions (R + premise inv) *)
  | mt_psnd n (Γ : Ctx n) A B M :
    mtyping Γ M (tsig A B) ->
    mtyping Γ (psnd M) B[(pfst M)..]

  | mt_prop n (Γ : Ctx n) :
    mctx Γ ->
    mtyping Γ tprop tuniv

  | mt_prop_u n (Γ : Ctx n) A :
    mtyping Γ A tprop ->
    mtyping Γ A tuniv

  (* dropped: [Γ ⊢e A ∈ tuniv] (C) *)
  | mt_tpi_prop n (Γ : Ctx n) A B :
    mtyping (ctx_extend Γ A) B tprop ->
    mtyping Γ (tpi A B) tprop

  | mt_unit n (Γ : Ctx n) :
    mctx Γ ->
    mtyping Γ tunit tuniv

  | mt_star n (Γ : Ctx n) :
    mctx Γ ->
    mtyping Γ tstar tunit

with mconv : forall {n} (Γ : Ctx n), Tm n -> Tm n -> Tm n -> Prop :=
  | mc_conv n (Γ : Ctx n) M N A B :
    mconv Γ M N A ->
    mconv Γ A B tuniv ->
    mconv Γ M N B

  | mc_refl n (Γ : Ctx n) M A :
    mtyping Γ M A ->
    mconv Γ M M A

  | mc_sym n (Γ : Ctx n) M N A :
    mconv Γ M N A ->
    mconv Γ N M A

  | mc_trans n (Γ : Ctx n) M N P A :
    mconv Γ M N A ->
    mconv Γ N P A ->
    mconv Γ M P A

  (* dropped: both presuppositions (T + R + premise inv) *)
  | mc_app1 n (Γ : Ctx n) A B N N' M :
    mconv Γ N N' (tpi A B) ->
    mtyping Γ M A ->
    mconv Γ (app N M) (app N' M) B[M..]

  (* dropped: both presuppositions (R + premise inv) *)
  | mc_app2 n (Γ : Ctx n) A B N M M' :
    mtyping Γ N (tpi A B) ->
    mconv Γ M M' A ->
    mconv Γ (app N M) (app N M') B[M..]

  (* dropped: [Γ ⊢e A ∈ tuniv] (C), [Γ ++ A ⊢e B ∈ tuniv] (R) *)
  | mc_beta n (Γ : Ctx n) A B M N :
    mtyping (ctx_extend Γ A) N B ->
    mtyping Γ M A ->
    mconv Γ (app (abs A N) M) N[M..] B[M..]

  (* dropped: [Γ ⊢e A ∈ tuniv] (C on the last premise) *)
  | mc_eta n (Γ : Ctx n) A B N N' :
    mtyping Γ N (tpi A B) ->
    mtyping Γ N' (tpi A B) ->
    mconv (ctx_extend Γ A) (app N⟨↑⟩ (var var_zero))
      (app N'⟨↑⟩ (var var_zero)) B ->
    mconv Γ N N' (tpi A B)

  | mc_ncase_Z n (Γ : Ctx n) M0 M1 (T : Tm (S n)) :
    mtyping (ctx_extend Γ tnat) T tuniv ->
    mtyping Γ M0 (T[zero..]) ->
    mtyping (ctx_extend Γ tnat) M1 T[rho] ->
    mconv Γ (ncase zero M0 M1) M0 T[zero..]

  | mc_ncase_S n (Γ : Ctx n) T M0 M1 N :
    mtyping (ctx_extend Γ tnat) T tuniv ->
    mtyping Γ N tnat ->
    mtyping Γ M0 (T[zero..]) ->
    mtyping (ctx_extend Γ tnat) M1 T[rho] ->
    mconv Γ (ncase (succ N) M0 M1) M1[N..] T[(succ N)..]

  (* dropped: [Γ ++ tnat ⊢e M1' ∈ T[rho]] (T) -- the premise [typing.v]
     already documents as admissible *)
  | mc_ncase n (Γ : Ctx n) T M M0 M1 M' M0' M1' :
    mtyping (ctx_extend Γ tnat) T tuniv ->
    mconv Γ M M' tnat ->
    mconv Γ M0 M0' T[zero..] ->
    mconv (ctx_extend Γ tnat) M1 M1' T[rho] ->
    mconv Γ (ncase M M0 M1) (ncase M' M0' M1') T[M..]

  | mc_succ n (Γ : Ctx n) M N :
    mconv Γ M N tnat ->
    mconv Γ (succ M) (succ N) tnat

  (* dropped: FIVE premises -- the two domain typings (T on the domain
     conversion), the codomain typing (R on the body conversion) and the two
     body typings (T) *)
  | mc_abs n (Γ : Ctx n) A A' B M M' :
    mconv Γ A A' tuniv ->
    mconv (ctx_extend Γ A) M M' B ->
    mconv Γ (abs A M) (abs A' M') (tpi A B)

  (* dropped: [Γ ⊢e A ∈ tuniv] (R + premise inv) *)
  | mc_fix n (Γ : Ctx n) A g :
    mtyping Γ g (tpi A A⟨↑⟩) ->
    mconv Γ (fix_ g) (app g (fix_ g)) A

  (* dropped: all three typings (T, then R + premise inv) *)
  | mc_fix_cong n (Γ : Ctx n) A g g' :
    mconv Γ g g' (tpi A A⟨↑⟩) ->
    mconv Γ (fix_ g) (fix_ g') A

  (* dropped: all three typings (T on the three conversions) *)
  | mc_tid n (Γ : Ctx n) A A' a a' b b' :
    mconv Γ A A' tuniv ->
    mconv Γ a a' A ->
    mconv Γ b b' A ->
    mconv Γ (tid A a b) (tid A' a' b') tuniv

  (* dropped: both typings (T, then R) *)
  | mc_rfl n (Γ : Ctx n) A a a' :
    mconv Γ a a' A ->
    mconv Γ (rfl a) (rfl a') (tid A a a)

  (* dropped: [Γ ⊢e A ∈ tuniv] (R) *)
  | mc_jcase_beta n (Γ : Ctx n) A a0 C d :
    mtyping Γ a0 A ->
    mtyping Γ C (motive_ty A) ->
    mtyping Γ d (base_ty A C) ->
    mconv Γ (jcase C d (rfl a0)) (app d a0)
           (app (app (app C a0) a0) (rfl a0))

  (* dropped: all six typings (T on the three conversions, then R + premise
     inv for [A] and the two endpoints) *)
  | mc_jcase n (Γ : Ctx n) A a b C C' d d' p p' :
    mconv Γ C C' (motive_ty A) ->
    mconv Γ d d' (base_ty A C) ->
    mconv Γ p p' (tid A a b) ->
    mconv Γ (jcase C d p) (jcase C' d' p') (app (app (app C a) b) p)

  (* dropped: all four typings -- the two domains by (T), the left codomain by
     (T), the RIGHT codomain by (T) followed by [ctx_conv_typing] *)
  | mc_tpi n (Γ : Ctx n) A0 A1 B0 B1 :
    mconv Γ A0 A1 tuniv ->
    mconv (ctx_extend Γ A0) B0 B1 tuniv ->
    mconv Γ (tpi A0 B0) (tpi A1 B1) tuniv

  (* dropped: all four typings, as [mc_tpi] *)
  | mc_tsig n (Γ : Ctx n) A0 A1 B0 B1 :
    mconv Γ A0 A1 tuniv ->
    mconv (ctx_extend Γ A0) B0 B1 tuniv ->
    mconv Γ (tsig A0 B0) (tsig A1 B1) tuniv

  (* dropped: [Γ ⊢e A ∈ tuniv] (C) *)
  | mc_beta_fst n (Γ : Ctx n) A B M N :
    mtyping (ctx_extend Γ A) B tuniv ->
    mtyping Γ M A ->
    mtyping Γ N B[M..] ->
    mconv Γ (pfst (mkpair M N)) M A

  (* dropped: [Γ ⊢e A ∈ tuniv] (C) *)
  | mc_beta_snd n (Γ : Ctx n) A B M N :
    mtyping (ctx_extend Γ A) B tuniv ->
    mtyping Γ M A ->
    mtyping Γ N B[M..] ->
    mconv Γ (psnd (mkpair M N)) N B[M..]

  (* dropped: both presuppositions (R + premise inv) *)
  | mc_pair_eta n (Γ : Ctx n) A B M :
    mtyping Γ M (tsig A B) ->
    mconv Γ (mkpair (pfst M) (psnd M)) M (tsig A B)

  (* dropped: [Γ ⊢e A ∈ tuniv] (C) *)
  | mc_mkpair1 n (Γ : Ctx n) A B M M' N :
    mtyping (ctx_extend Γ A) B tuniv ->
    mconv Γ M M' A ->
    mtyping Γ N B[M..] ->
    mconv Γ (mkpair M N) (mkpair M' N) (tsig A B)

  (* dropped: [Γ ⊢e A ∈ tuniv] (C) *)
  | mc_mkpair2 n (Γ : Ctx n) A B M N N' :
    mtyping (ctx_extend Γ A) B tuniv ->
    mtyping Γ M A ->
    mconv Γ N N' B[M..] ->
    mconv Γ (mkpair M N) (mkpair M N') (tsig A B)

  (* dropped: both presuppositions (T + R + premise inv) *)
  | mc_pfst n (Γ : Ctx n) A B M M' :
    mconv Γ M M' (tsig A B) ->
    mconv Γ (pfst M) (pfst M') A

  (* dropped: both presuppositions (T + R + premise inv) *)
  | mc_psnd n (Γ : Ctx n) A B M M' :
    mconv Γ M M' (tsig A B) ->
    mconv Γ (psnd M) (psnd M') B[(pfst M)..]

  | mc_prop n (Γ : Ctx n) M N A :
    mtyping Γ A tprop ->
    mtyping Γ M A ->
    mtyping Γ N A ->
    mconv Γ M N A

  | mc_prop_u n (Γ : Ctx n) M N :
    mconv Γ M N tprop ->
    mconv Γ M N tuniv

  (* dropped: all four typings, as [mc_tpi] *)
  | mc_tpi_prop n (Γ : Ctx n) A0 A1 B0 B1 :
    mconv Γ A0 A1 tuniv ->
    mconv (ctx_extend Γ A0) B0 B1 tprop ->
    mconv Γ (tpi A0 B0) (tpi A1 B1) tprop

  | mc_unit_eta n (Γ : Ctx n) M N :
    mtyping Γ M tunit ->
    mtyping Γ N tunit ->
    mconv Γ M N tunit

with mctx : forall {n}, Ctx n -> Prop :=
  | mx_empty : mctx ctx_empty
  (* dropped: [ctx Γ] -- [typing_ctx] on the second premise *)
  | mx_cons n (Γ : Ctx n) A :
    mtyping Γ A tuniv ->
    mctx (ctx_extend Γ A).

Scheme mtyping_mind := Minimality for mtyping Sort Prop
  with mconv_mind := Minimality for mconv Sort Prop
  with mctx_mind := Minimality for mctx Sort Prop.

Combined Scheme mtyping_mutind from mtyping_mind, mconv_mind, mctx_mind.

Scheme typing_mind := Minimality for typing Sort Prop
  with conv_mind := Minimality for conv Sort Prop
  with ctx_mind := Minimality for ctx Sort Prop.

Combined Scheme typing_mutind from typing_mind, conv_mind, ctx_mind.

(* ================================================================== *)
(** * Equivalence with the original system                             *)
(* ================================================================== *)

(** ** Saturation

    Rebuilding a dropped premise always means running one of the tools
    forward.  [sat] closes the hypotheses under all of them at once -- the two
    sides of a conversion (T), the type of a term (R), the domain of an
    extended context (C), and the premises of a type former -- each guarded so
    that the loop terminates. *)

Ltac notHyp P :=
  lazymatch goal with [ _ : P |- _ ] => fail | _ => idtac end.

Ltac sat :=
  repeat
    match goal with
    (* (T) both sides of a conversion are typed *)
    | [ H : ?G ⊢e ?M ≡ ?N ∈ ?A |- _ ] =>
        notHyp (G ⊢e M ∈ A); pose proof (conv_typing1 H)
    | [ H : ?G ⊢e ?M ≡ ?N ∈ ?A |- _ ] =>
        notHyp (G ⊢e N ∈ A); pose proof (conv_typing2 H)
    (* (C) the domain of an extended context is a type *)
    | [ H : ?G ++ ?A ⊢e ?M ∈ ?B |- _ ] =>
        notHyp (G ⊢e A ∈ tuniv); pose proof (typing_ext_dom H)
    (* premises of the three type formers *)
    | [ H : ?G ⊢e tpi ?A ?B ∈ ?T |- _ ] =>
        notHyp (G ⊢e A ∈ tuniv); pose proof (proj1 (typing_tpi_prem_inv H))
    | [ H : ?G ⊢e tpi ?A ?B ∈ ?T |- _ ] =>
        notHyp (G ++ A ⊢e B ∈ tuniv); pose proof (proj2 (typing_tpi_prem_inv H))
    | [ H : ?G ⊢e tsig ?A ?B ∈ ?T |- _ ] =>
        notHyp (G ⊢e A ∈ tuniv); pose proof (proj1 (typing_tsig_prem_inv H))
    | [ H : ?G ⊢e tsig ?A ?B ∈ ?T |- _ ] =>
        notHyp (G ++ A ⊢e B ∈ tuniv); pose proof (proj2 (typing_tsig_prem_inv H))
    | [ H : ?G ⊢e tid ?A ?a ?b ∈ ?T |- _ ] =>
        notHyp (G ⊢e a ∈ A); pose proof (proj1 (proj2 (typing_tid_prem_inv H)))
    | [ H : ?G ⊢e tid ?A ?a ?b ∈ ?T |- _ ] =>
        notHyp (G ⊢e b ∈ A); pose proof (proj2 (proj2 (typing_tid_prem_inv H)))
    (* (R) the type of a term is a type *)
    | [ H : ?G ⊢e ?M ∈ ?A |- _ ] =>
        notHyp (G ⊢e A ∈ tuniv); pose proof (typing_regularity G M A H)
    (* transport a codomain along a domain conversion *)
    | [ HC : ?G ⊢e ?A0 ≡ ?A1 ∈ tuniv, HB : ?G ++ ?A0 ⊢e ?B ∈ ?T |- _ ] =>
        notHyp (G ++ A1 ⊢e B ∈ T);
        pose proof (ctx_conv_typing G A0 A1 B T HC HB)
    end.

(** Hints for the original system.  The recovery lemmas are handled by [sat],
    so this database is just the constructors plus context well-formedness. *)
Create HintDb minsound.
#[local] Hint Constructors typing conv ctx : minsound.
#[local] Hint Resolve typing_ctx conv_ctx : minsound.

Lemma min_sound :
  (forall n (Γ : Ctx n) M A, mtyping Γ M A -> Γ ⊢e M ∈ A)
  /\ (forall n (Γ : Ctx n) M N A, mconv Γ M N A -> Γ ⊢e M ≡ N ∈ A)
  /\ (forall n (Γ : Ctx n), mctx Γ -> ctx Γ).
Proof.
  apply mtyping_mutind.
  all: intros.
  all: sat.
  all: solve [ eauto 4 with minsound ].
Qed.

Definition mtyping_typing {n} {Γ : Ctx n} {M A} : mtyping Γ M A -> Γ ⊢e M ∈ A.
Proof. move: min_sound => [h _]. eauto. Qed.

Definition mconv_conv {n} {Γ : Ctx n} {M N A} : mconv Γ M N A -> Γ ⊢e M ≡ N ∈ A.
Proof. move: min_sound => [_ [h _]]. eauto. Qed.

Definition mctx_ctx {n} {Γ : Ctx n} : mctx Γ -> ctx Γ.
Proof. move: min_sound => [_ [_ h]]. eauto. Qed.

(** The easy direction: every minimal rule's premises are a subset of the
    original rule's, so the translation just forgets the presuppositions. *)
Create HintDb mincomplete.
#[local] Hint Constructors mtyping mconv mctx : mincomplete.

Lemma min_complete :
  (forall n (Γ : Ctx n) M A, Γ ⊢e M ∈ A -> mtyping Γ M A)
  /\ (forall n (Γ : Ctx n) M N A, Γ ⊢e M ≡ N ∈ A -> mconv Γ M N A)
  /\ (forall n (Γ : Ctx n), ctx Γ -> mctx Γ).
Proof.
  apply typing_mutind.
  all: intros.
  all: solve [ eauto 3 with mincomplete ].
Qed.

Definition typing_mtyping {n} {Γ : Ctx n} {M A} : Γ ⊢e M ∈ A -> mtyping Γ M A.
Proof. move: min_complete => [h _]. eauto. Qed.

Definition conv_mconv {n} {Γ : Ctx n} {M N A} : Γ ⊢e M ≡ N ∈ A -> mconv Γ M N A.
Proof. move: min_complete => [_ [h _]]. eauto. Qed.

Definition ctx_mctx {n} {Γ : Ctx n} : ctx Γ -> mctx Γ.
Proof. move: min_complete => [_ [_ h]]. eauto. Qed.

(** The two presentations specify the same three judgments. *)
Theorem mtyping_iff {n} (Γ : Ctx n) M A : mtyping Γ M A <-> Γ ⊢e M ∈ A.
Proof. split; [ exact: mtyping_typing | exact: typing_mtyping ]. Qed.

Theorem mconv_iff {n} (Γ : Ctx n) M N A : mconv Γ M N A <-> Γ ⊢e M ≡ N ∈ A.
Proof. split; [ exact: mconv_conv | exact: conv_mconv ]. Qed.

Theorem mctx_iff {n} (Γ : Ctx n) : mctx Γ <-> ctx Γ.
Proof. split; [ exact: mctx_ctx | exact: ctx_mctx ]. Qed.

(* ================================================================== *)
(** * Tally, and what is NOT claimed

    Counting one premise per rule premise, [typing.v]'s three judgments carry
    172 premises across their 57 rules; [mtyping] / [mconv] / [mctx] carry
    102.  So 70 of the original premises -- about two fifths -- are
    presuppositions, and [mtyping_iff] / [mconv_iff] / [mctx_iff] show that
    dropping them changes nothing.

    Where they come from, by tool:

    - (C) [typing Γ A tuniv] next to a premise judged in [Γ ++ A]:
      [t_abs], [t_tpi], [t_tsig], [t_mkpair], [t_tpi_prop], [c_eta],
      [c_beta], [c_beta_fst], [c_beta_snd], [c_mkpair1], [c_mkpair2].
    - (R) the type of a term is a type: the codomain premise of [t_abs] and
      [c_beta], and the [typing Γ A tuniv] of [t_tid], [t_rfl], [c_rfl],
      [c_jcase_beta].
    - (R) + premise inversion, reading a type former's premises back off a
      term of that type: both presuppositions of [t_app], [t_pfst], [t_psnd],
      [c_app1], [c_app2], [c_pfst], [c_psnd], [c_pair_eta]; the domain of
      [t_fix], [c_fix], [c_fix_cong]; and [A] with both endpoints in
      [t_jcase] and [c_jcase].
    - (T) a congruence need not carry its sides' typings: [c_ncase]'s [M1'],
      [c_abs]'s four typings, [c_fix_cong]'s two, [c_tid]'s three, [c_rfl]'s
      one, [c_jcase]'s three, and the domain typings of
      [c_tpi] / [c_tsig] / [c_tpi_prop].
    - (T) + [ctx_conv_typing]: the *right-hand* codomain typing of
      [c_tpi] / [c_tsig] / [c_tpi_prop], which lives in the other context.
    - [typing_ctx]: [c_cons]'s [ctx Γ].

    What is NOT claimed.  Unlike [finelt/minimal_types.v], this file does not
    prove that the 102 surviving premises are each necessary.  For most of
    them the reason is structural -- the premise is the rule's only premise,
    or it is the only one mentioning some metavariable (the motive [T] of
    [t_case] and [c_ncase], which the other premises see only as [T[zero..]]
    and [T[rho]]; the codomain [B] of [t_mkpair] and [c_beta_fst], seen only
    as [B[M..]]) -- but turning that into a proof would need the
    non-confusion/consistency facts that live in [adequacy.v]: refuting, say,
    [ctx (ctx_empty ++ zero)] means refuting
    [ctx_empty ⊢e tnat ≡ tuniv ∈ tuniv], which no syntactic argument in
    [typing.v] settles.  The [ctx Γ] premises of the leaf rules are in that
    situation, so their necessity is asserted here, not proved. *)
