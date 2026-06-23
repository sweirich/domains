Require Import ssreflect.

Require Import syntax.
Require Export fintype.
Require Export fin_util.

From Stdlib Require Export Logic.FunctionalExtensionality.
From Stdlib Require Import Program.Equality.

Lemma ext_fin {n A}{f g: fin n -> A} : 
  (forall x, f x = g x) -> f = g.
eapply functional_extensionality.
Qed.

Import ScopedNotations.
Import SubstNotations.

Disable Notation "'__Tm'" (all).

(** Define a notation scope specific to this language. *)
Declare Scope syntax_scope.

Module SyntaxNotations.
Export ScopedNotations.
Notation "⇑" := (up_Tm_Tm) : syntax_scope.
Notation "⇑ σ" := (var var_zero .: σ >> ren_Tm ↑) 
                    (only printing, at level 0) : syntax_scope.
End SyntaxNotations.
Import SyntaxNotations.

Create HintDb syntax.
Open Scope syntax_scope.


(* Single substitution commutes with [σ].*)
Lemma subst1_subst_comm 
  {n m} {B : Tm (S n)}{N : Tm n}{σ : fin n -> Tm m} :
  B[N .: var][σ] = B[⇑ σ][N[σ] .: var].
Proof.
Admitted.

(* subst_cons_eq: extending a substitution by a closed term commutes with the
   single-substitution form: [B[N .: σ] = B[⇑σ][N..]].  Same autosubst var≠ids
   gap as [subst1_subst_comm].  ADMITTED. *)
Lemma subst_cons_eq {n m} (B : Tm (S n)) (N : Tm m) (σ : fin n -> Tm m) :
  B[N .: σ] = B[⇑ σ][N .: var].
Admitted.

(* ------------------------------------------------ *)

Inductive Ctx : nat -> Type := 
| ctx_empty    : Ctx 0
| ctx_extend n : Ctx n -> Tm n -> Ctx (S n).

Notation "Γ ++ A" := (ctx_extend _ Γ A) : syntax_scope.

Fixpoint lookup {n} (x : fin n) : Ctx n -> Tm n.
  destruct n; cbn in x. done.
  destruct x as [p|]. 
  - move=> tl.
    inversion tl. exact (lookup _ p X)⟨↑⟩.
  - move=> tl.
    inversion tl. exact (X0⟨↑⟩).
Defined.

Lemma lookup_weaken {n}(Γ:Ctx n) A y : 
   lookup (Some y : fin (S n)) (Γ ++ A) = (lookup y Γ)[↑ >> var].
cbn [lookup]. fold fin in y. cbn [f_equal].
cbn. 
auto_unfold.
move: (@rinstInst'_Tm _ _ shift (lookup y Γ)) => h.
rewrite h.
reflexivity.
Qed.

(* for nrec *)
Definition rho {n} : fin (S n) -> Tm (S n) := 
   (succ (var var_zero) .: var >> ⟨↑⟩).

Inductive typing : forall {n} (Γ : Ctx n), Tm n -> Tm n -> Prop := 
  | t_var n (Γ : Ctx n) x : 
    ctx Γ ->
    typing Γ (var x) (lookup x Γ)
  | t_conv n (Γ : Ctx n) M A B : 
    typing Γ M A -> 
    conv Γ A B tuniv -> 
    typing Γ M B
  | t_abs n (Γ : Ctx n) A B N : 
    typing Γ A tuniv ->
    typing (Γ ++ A) B tuniv -> 
    typing (Γ ++ A) N B ->
    typing Γ (abs A N) (tpi A B)
  | t_app n (Γ : Ctx n) A B N M : 
    typing Γ A tuniv -> 
    typing (Γ ++ A) B tuniv -> 
    typing Γ N (tpi A B) ->
    typing Γ M A -> 
    typing Γ (app N M) B[M..]
  (* natural numbers *)
  | t_nat n (Γ : Ctx n) : 
    ctx Γ ->
    typing Γ tnat tuniv
  | t_zero n (Γ : Ctx n) : 
    ctx Γ ->
    typing Γ zero tnat 
  | t_succ n (Γ : Ctx n) M : 
    typing Γ M tnat ->
    typing Γ (succ M) tnat 
(*
  | t_nrec n (Γ : Ctx n) (T U : Tm (S n)) M0 M1 :
    typing (Γ ++ tnat) T tuniv ->
    typing Γ M0 (T[zero..]) ->
    U = T[rho] ->
    typing Γ M1 (tpi tnat (tpi T U⟨↑⟩ )) ->       
    typing Γ (nrec T M0 M1) (tpi tnat T) *)
  (* universes *)
  | t_tpi n (Γ : Ctx n) A B : 
    typing Γ A tuniv ->
    typing (Γ ++ A) B tuniv -> 
    typing Γ (tpi A B) tuniv
  | t_univ n (Γ : Ctx n) : 
    ctx Γ ->
    typing Γ tuniv tuniv
with conv :forall {n} (Γ : Ctx n), Tm n -> Tm n -> Tm n -> Prop := 
  | c_conv n (Γ : Ctx n) M N A B : 
    conv Γ M N A -> 
    conv Γ A B tuniv ->
    conv Γ M N B
  | c_refl n (Γ : Ctx n) M A : 
    typing Γ M A ->
    conv Γ M M A 
  | c_sym n (Γ : Ctx n) M N A : 
    conv Γ M N A -> 
    conv Γ N M A
  | c_trans n (Γ : Ctx n) M N P A  : 
    conv Γ M N A -> 
    conv Γ N P A -> 
    conv Γ M P A
  | c_app1 n (Γ : Ctx n) A B N N' M : 
    typing Γ A tuniv -> 
    typing (Γ ++ A) B tuniv -> 
    conv Γ N N' (tpi A B) ->
    typing Γ M A ->
    conv Γ (app N M) (app N' M) B[M..]
  | c_app2 n (Γ : Ctx n) A B N M M'  :          
    typing Γ A tuniv -> 
    typing (Γ ++ A) B tuniv -> 
    typing Γ N (tpi A B) ->
    conv Γ M M' A ->
    conv Γ (app N M) (app N M') B[M..]
  | c_beta n (Γ : Ctx n) A B M N :
    typing Γ A tuniv -> 
    typing (Γ ++ A) B tuniv -> 
    typing (Γ ++ A) N B -> 
    typing Γ M A ->
    conv Γ (app (abs A N) M) N[M..] B[M..]
  | c_eta n (Γ : Ctx n) A B N N' :
    typing Γ A tuniv -> 
    typing (Γ ++ A) B tuniv -> 
    typing Γ N (tpi A B) ->     
    typing Γ N' (tpi A B) ->     
    conv (Γ ++ A) (app N⟨↑⟩ (var var_zero))
      (app N'⟨↑⟩ (var var_zero)) B ->
    conv Γ N N' (tpi A B)
  (* natural numbers: TODO add typing hyps *)
(*
  | c_nrec_Z n (Γ : Ctx n) M0 M1 (T : Tm (S n)) : 
    typing  (Γ ++ tnat) T tuniv ->
    typing Γ M0 (T[zero..]) ->
    typing Γ M1 (tpi tnat (tpi T T[rho]⟨↑⟩ )) ->   
    conv Γ (app (nrec T M0 M1) zero) M0 T[zero..]
  | c_nrec_S n (Γ : Ctx n) T M0 M1 n : 
    typing (Γ ++ tnat) T tuniv ->
    typing Γ M0 (T[zero..]) ->
    typing Γ M1 (tpi tnat (tpi T T[rho]⟨↑⟩ )) ->    
    conv Γ (app (nrec T M0 M1) (succ n)) 
      (app (app M1 n) (app (nrec T M0 M1) n)) T[(succ n)..] *)
  | c_succ n (Γ : Ctx n) M N :
    conv Γ M N tnat ->
    conv Γ (succ M) (succ N) tnat
  | c_abs n (Γ : Ctx n) A A' B M M' :
    conv Γ A A' tuniv ->
    conv (Γ ++ A) M M' B ->
    conv Γ (abs A M) (abs A' M') (tpi A B)
  | c_tpi n (Γ : Ctx n) A0 A1 B0 B1 :
    conv Γ A0 A1 tuniv -> 
    conv (Γ ++ A0) B0 B1 tuniv -> 
    conv Γ (tpi A0 B0) (tpi A1 B1) tuniv
with ctx : forall {n}, Ctx n -> Prop :=
  | c_empty : ctx ctx_empty
  | c_cons n (Γ : Ctx n) A : ctx Γ -> 
     typing Γ A tuniv -> 
     ctx (Γ ++ A).

Lemma typing_ctx {n} (Γ : Ctx n) M A :
  typing Γ M A -> ctx Γ.
Proof.
  move=> h.
  induction h; eauto.
Qed.

Lemma conv_ctx {n} (Γ : Ctx n) M N A :
  conv Γ M N A -> ctx Γ.
Proof.
  move=> h.
  induction h; eauto using typing_ctx.
Qed.


(** This version of t_var is easier to work with sometimes
    as it doesn't require the type to already be in the form 
    Γ x. *)
Definition t_var' {n} (Γ : Ctx n) x τ : 
  lookup x Γ = τ -> ctx Γ -> typing Γ (var x) τ.
intros <-. eapply t_var. Qed.
Definition t_app' {n} (Γ : Ctx n) (A : Tm n) 
  (B : Tm (S n)) (N M : Tm n) (C:Tm n) :
       typing Γ A tuniv ->
            typing (Γ ++ A) B tuniv -> typing Γ N (tpi A B) 
       -> typing Γ M A 
       -> B[M..] = C
       -> typing Γ (app N M) C.
intros. subst. eapply t_app; eauto. Qed. 
Definition t_univ' {n} (Γ : Ctx n) A :
  tuniv = A -> ctx Γ ->
  typing Γ tuniv A.
intros <- h. eapply t_univ; eauto. Qed.

Definition c_app1' {n} (Γ : Ctx n) A B N N' M C :
    typing Γ A tuniv ->
    typing (Γ ++ A) B tuniv ->
    conv Γ N N' (tpi A B) ->
    typing Γ M A ->
    B[M..] = C ->
    conv Γ (app N M) (app N' M) C.
Proof. intros; subst; eauto using c_app1. Qed.

Definition c_app2' {n} (Γ : Ctx n) A B N M M' C :
    typing Γ A tuniv ->
    typing (Γ ++ A) B tuniv ->
    typing Γ N (tpi A B) ->
    conv Γ M M' A ->
    B[M..] = C ->
    conv Γ (app N M) (app N M') C.
Proof. intros; subst; eauto using c_app2. Qed.

Definition c_beta' {n} (Γ : Ctx n) A B M N C D :
    typing Γ A tuniv ->
    typing (Γ ++ A) B tuniv ->
    typing (Γ ++ A) N B ->
    typing Γ M A ->
    N[M..] = C ->
    B[M..] = D ->
    conv Γ (app (abs A N) M) C D.
Proof. intros; subst; eauto using c_beta. Qed.

(*
Definition c_nrec_Z' {n} (Γ : Ctx n) M0 M1 (T : Tm (S n)) C :
    typing (Γ ++ tnat) T tuniv ->
    typing Γ M0 (T[zero..]) ->
    typing Γ M1 (tpi tnat (tpi T T[rho]⟨↑⟩)) ->
    T[zero..] = C ->
    conv Γ (app (nrec T M0 M1) zero) M0 C.
Proof. intros; subst; eauto using c_nrec_Z. Qed.

Definition c_nrec_S' {n} (Γ : Ctx n) T M0 M1 e C :
    typing (Γ ++ tnat) T tuniv ->
    typing Γ M0 (T[zero..]) ->
    typing Γ M1 (tpi tnat (tpi T T[rho]⟨↑⟩)) ->
    T[(succ e)..] = C ->
    conv Γ (app (nrec T M0 M1) (succ e))
      (app (app M1 e) (app (nrec T M0 M1) e)) C.
Proof. intros; subst; eauto using c_nrec_S. Qed.
*)

#[export] Hint Resolve t_var'  t_univ': syntax.

#[export] Hint Constructors typing conv : syntax.


Module Notations.
Notation "Γ |-e a ∈ A" := (typing Γ a A) (at level 70) : syntax_scope.
Notation "Γ |-e a ≡ b ∈ A" := (conv Γ a b A) (at level 70) : syntax_scope.
End Notations.

Open Scope syntax_scope.
Import Notations.

(** * Renaming and substitution properties *)

(* == RenTypes *)
Definition typing_renaming {n} (Δ : Ctx n) 
  {m} (δ : fin m -> fin n)
  (Γ : Ctx m) : Prop := 
  forall i, lookup (δ i) Δ  = (lookup i Γ)⟨δ⟩.


(** The identity renaming preserves the context *)
Lemma typing_renaming_id {n} (Δ : Ctx n) :
  typing_renaming Δ id Δ.
Proof. unfold typing_renaming. intros x. asimpl. done. Qed.

(** shift extends the context *)
Lemma typing_renaming_shift {n} (Γ : Ctx n) (τ : Tm n) :
    typing_renaming (Γ ++ τ) shift Γ.
Proof.
  unfold typing_renaming. intros x. asimpl. fsimpl. done. Qed.

(** Lift a renaming to a new scope *)
Lemma typing_renaming_lift {n} (Δ : Ctx n) 
  {m} (Γ : Ctx m) (δ : fin m -> fin n) (τ : Tm m) :
  typing_renaming Δ δ Γ ->
  typing_renaming (Δ ++ τ⟨δ⟩) (up_ren δ) (Γ ++ τ).
Proof. intro h. unfold typing_renaming in *.
       auto_case; asimpl; try done.
       unfold ">>". rewrite h.
         asimpl. done.
Qed.

Create HintDb renaming.
#[export] Hint Resolve typing_renaming_lift 
  typing_renaming_id typing_renaming_shift : renaming.


Fixpoint renaming_typing {n} (Γ : Ctx n) a A {m} (Δ:Ctx m) δ : 
  Γ |-e a ∈ A -> typing_renaming Δ δ Γ -> ctx Δ -> Δ |-e a⟨δ⟩ ∈ A⟨δ⟩
with renaming_conv {n} (Γ : Ctx n) a b A {m} (Δ:Ctx m) δ : 
  Γ |-e a ≡ b ∈ A -> typing_renaming Δ δ Γ ->  ctx Δ -> Δ |-e a⟨δ⟩ ≡ b⟨δ⟩ ∈ A⟨δ⟩.
Proof.
  (* typing *)
  - have renaming_typing':
      forall n (Γ : Ctx n) a A m (Δ:Ctx m) δ B,
        Γ |-e a ∈ A -> typing_renaming Δ δ Γ ->  ctx Δ ->
           B = A⟨δ⟩ ->
           Δ |-e a⟨δ⟩ ∈ B.
    { intros until B. intros h tR cD ->. eapply renaming_typing; eauto. }
    have renaming_conv' :
      forall n (Γ : Ctx n) a b A m (Δ:Ctx m) δ B,
        Γ |-e a ≡ b ∈ A -> typing_renaming Δ δ Γ ->  ctx Δ ->
           B = A⟨δ⟩ ->
           Δ |-e a⟨δ⟩ ≡ b⟨δ⟩ ∈ B.
    { intros until B. intros h tR cD ->. eapply renaming_conv; eauto. }
    intros h tR wtΔ.
    dependent destruction h; subst.
    all: try have EC: ctx (Δ ++ A ⟨δ⟩) by
      eapply c_cons; eauto with renaming. 
    all: try solve [asimpl; econstructor; eauto with renaming; cbn].

    + (* var case *)
      eapply t_var'; eauto.
    + (* app *) 
      cbn. asimpl.
      eapply t_app' with (B:=B⟨up_ren δ⟩); eauto with renaming. 
      asimpl.
      auto.
(*    + (* nrec *)
      have EC: ctx (Δ ++ tnat).
      { eapply c_cons; eauto with renaming.
        eapply t_nat; eauto. }
      eapply t_nrec; eauto with renaming.
      eapply renaming_typing' in h1; eauto with renaming.
      eapply typing_renaming_lift with (τ:=tnat) in tR; eauto.
      eapply renaming_typing' in h2; eauto. asimpl. eauto.
      eapply renaming_typing' in h3; eauto with renaming.
      asimpl.
      f_equal. f_equal.
      unfold rho. asimpl.
      eapply ext_fin. intros [k|]; asimpl; reflexivity. *)
  (* conv *)
  - have renaming_typing':
      forall n (Γ : Ctx n) a A m (Δ:Ctx m) δ B,
        Γ |-e a ∈ A -> typing_renaming Δ δ Γ ->  ctx Δ ->
           B = A⟨δ⟩ ->
           Δ |-e a⟨δ⟩ ∈ B.
    { intros until B. intros h tR cD ->. eapply renaming_typing; eauto. }
    have renaming_conv' :
      forall n (Γ : Ctx n) a b A m (Δ:Ctx m) δ B,
        Γ |-e a ≡ b ∈ A -> typing_renaming Δ δ Γ ->  ctx Δ ->
           B = A⟨δ⟩ ->
           Δ |-e a⟨δ⟩ ≡ b⟨δ⟩ ∈ B.
    { intros until B. intros h tR cD ->. eapply renaming_conv; eauto. }
    intros h tR tΔ.
    dependent destruction h; subst.
    all: try have EC: ctx (Δ ++ A⟨δ⟩)
               by eapply c_cons; eauto with renaming.
    all: try solve [asimpl; econstructor; 
              eauto using renaming_typing' with renaming].
    + (* c_app1 *)
      cbn. asimpl.
      eapply c_app1' with (A:= A⟨δ⟩)(B := B⟨up_ren δ⟩);
        eauto using renaming_typing' with renaming.
      asimpl. reflexivity.
    + (* c_app2 *)
      cbn. asimpl.
      eapply c_app2' with (A:= A⟨δ⟩)(B := B⟨up_ren δ⟩);
        eauto using renaming_typing' with renaming.
      asimpl. reflexivity.
    + (* c_beta *)
      cbn. asimpl.
      eapply c_beta' with (A:= A⟨δ⟩)(B := B⟨up_ren δ⟩);
        try eapply renaming_typing'; eauto with renaming.
      asimpl; auto.
      asimpl; auto.
    + (* c_eta *)
      cbn. 
      eapply c_eta with (A := A⟨δ⟩)(B := B⟨up_ren δ⟩);
        try (eapply renaming_typing'; eauto with renaming).
      have TR': typing_renaming (Δ ++ ⟨δ⟩ A) (up_ren δ) (Γ ++ A).
      eauto with renaming.
      eapply renaming_conv' with (Δ := Δ ++ ⟨δ⟩ A)
        (δ := up_ren δ) (B := ⟨up_ren δ⟩ B) in h; eauto.
      cbn in h. 
      admit.
    + (* c_abs  *)
      admit.
    (*
    + (* c_nrec_Z *) admit.
    + (* c_nrec_S *) admit. *)
    + (* c_tpi *) 
Admitted.

(* All typed in well-formed contexts are well-formed *)
Lemma ctx_typing_lookup {n} (Γ : Ctx n) : 
  ctx Γ ->
  forall x, typing Γ (lookup x Γ) Core.tuniv.
Proof.
  move=> h. induction h.
  - done.
  - auto_case.
    + specialize (IHh f).
      unfold core.funcomp.
      eapply renaming_typing with (A := Core.tuniv) (δ:=↑);
        eauto with renaming. 
      eapply c_cons; eauto.
    + unfold core.funcomp.
      eapply renaming_typing with (A := Core.tuniv) (δ:=↑);
        eauto with renaming. 
      eapply c_cons; eauto. 
Qed.
      
(** Substution lemmas *)

Definition typing_subst {n} (Δ : Ctx n) {m} (σ : fin m -> Tm n)
  (Γ : Ctx m) : Prop := 
  forall x, (Δ |-e (σ x) ∈ (lookup x Γ)[σ]).

Lemma typing_subst_null {n} (Δ : Ctx n) :
  typing_subst Δ null ctx_empty.
Proof. unfold typing_subst. auto_case. Qed.

Lemma typing_subst_id {n} (Δ : Ctx n) :
  ctx Δ -> typing_subst Δ var Δ.
Proof. move=>h. 
       unfold typing_subst. intro x. asimpl. econstructor; eauto. 
       Qed.

Lemma typing_subst_cons {n} (Δ : Ctx n) {m} (σ : fin m -> Tm n)
  (Γ : Ctx m) e τ : 
 Δ |-e e ∈ τ[σ] -> typing_subst Δ σ Γ ->
 typing_subst Δ (e .: σ) (Γ ++ τ).
Proof. intros. unfold typing_subst in *. intros [y|]; asimpl; eauto. Qed.

Lemma typing_subst_lift {n} (Δ : Ctx n) {m} (σ : fin m -> Tm n)
  (Γ : Ctx m) τ : 
  ctx (Δ ++ τ[σ]) ->
  typing_subst Δ σ Γ -> typing_subst (Δ ++ τ[σ]) (⇑ σ) (Γ ++ τ).
Proof.
  unfold typing_subst in *.
  intros EC h.
  intro x. destruct x.
  + specialize (h f).
    cbn.
    eapply renaming_typing with (Δ := Δ ++ τ[σ])in h;
      eauto with renaming.
    asimpl in h. done.
  +  cbn. eapply t_var'; eauto.
     cbn. asimpl. eauto.
Qed.

(** Add the substitution lemmas as hints *)
#[export] Hint Resolve typing_subst_lift (* typing_subst_cons *)
             typing_subst_id typing_subst_null : rec.

Fixpoint
  substitution_tm {n} (Γ : Ctx n) a A {m} (Δ:Ctx m) σ : 
  Γ |-e a ∈ A -> typing_subst Δ σ Γ -> ctx Δ -> Δ |-e a[σ] ∈ A[σ]
with 
 substitution_conv {n} (Γ : Ctx n) a b A {m} (Δ:Ctx m) σ : 
  Γ |-e a ≡ b ∈ A -> typing_subst Δ σ Γ -> ctx Δ -> Δ |-e a[σ] ≡ b[σ] ∈ A[σ]
.
Proof.
  all: intros h tS tΔ.
  - dependent destruction h; subst.
    all: cbn; asimpl.
    all: try solve [econstructor; eauto with syntax].
    + unfold typing_subst in tS. eauto.
    + admit.
Admitted.

(* ----------- context conversion -------------- *)

Lemma ctc_conv_typing_subst {n} (Γ:Ctx n) A A' : 
  typing Γ A tuniv -> 
  typing Γ A' tuniv -> 
  conv Γ A A' tuniv -> 
  typing_subst (Γ ++ A) var (Γ ++ A').
Proof. 
  move=> t1 t2 C.
  have CTX:  ctx (Γ ++ A).
  { eapply c_cons; eauto using typing_ctx. } 
  unfold typing_subst.
  move=> [y|]. fold fin in y.
  + cbn. asimpl. eapply t_var'; eauto.
    eapply lookup_weaken; eauto.
  + cbn. 
    eapply t_conv with (A :=⟨↑⟩A). 
    eapply t_var; eauto. 
    asimpl.
    rewrite rinstInst'_Tm.
    eapply substitution_conv with (A := tuniv); eauto.
    unfold typing_subst. move=> x.
    unfold core.funcomp.
    eapply t_var'; eauto.
    cbn.
    auto_unfold.
    rewrite -> rinstInst'_Tm.
    unfold core.funcomp.
    done.
Qed.

Lemma ctx_conv_typing {n} (Γ:Ctx n) A A' M B : 
  conv Γ A A' tuniv -> 
  typing (Γ ++ A) M B -> typing (Γ ++ A') M B.
Proof.
Admitted.


Lemma ctx_conv_conv {n} (Γ:Ctx n) A A' M N B : 
  conv Γ A A' tuniv -> 
  conv (Γ ++ A) M N B -> conv (Γ ++ A') M N B.
Proof.
  move=> CA CMN.
Admitted.

(* conv_typing: regularity of conversion — both sides of a conversion are
   well-typed at the common type.  A standard syntactic metatheory fact (by
   induction on [conv]); ADMITTED alongside the other syntactic gaps. *)
Lemma conv_typing {n} {Γ : Ctx n} {M N A : Tm n} :
  conv Γ M N A -> typing Γ M A /\ typing Γ N A.
Proof.
  induction 1; eauto.
  all: split.
  all: try destruct IHconv1 as [h1 h2].
  all: try destruct IHconv2 as [h3 h4].
  all: try destruct IHconv as [h5 h6].
  all: eauto.
  - eapply t_conv; eauto.
  - eapply t_conv; eauto.
  - eapply t_app; eauto.
  - eapply t_app'; eauto.
  - eapply t_app; eauto.
  - eapply t_conv. eapply t_app; eauto.
Admitted.



(*

ctx-conv-WtSub : {n : Nat} {G : Ctx n} {A A' : Expr n} ->
    HasType G A U -> HasType G A' U -> ConvTm G A A' U ->
    WtSub (extend G A') (extend G A) idSub

ctx-conv-HasType : {n : Nat} {G : Ctx n} {A A' : Expr n}
    {M B : Expr (suc n)} ->
    HasType G A U -> HasType G A' U -> ConvTm G A A' U ->
    HasType (extend G A) M B -> HasType (extend G A') M B

  -- Context conversion for ConvTm
  ctx-conv-ConvTm : {n : Nat} {G : Ctx n} {A A' : Expr n}
    {M N B : Expr (suc n)} ->
    HasType G A U -> HasType G A' U -> ConvTm G A A' U ->
    ConvTm (extend G A) M N B -> ConvTm (extend G A') M N B
*)
