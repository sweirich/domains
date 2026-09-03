Require Import ssreflect.

From Stdlib Require Export Logic.FunctionalExtensionality.
From Stdlib Require Import Program.Equality.

Require Export autosubst.core.
Require Export autosubst.fintype.
Require Import syntax.syntax.

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

(* ------------------------------------------------ *)
(** * typing and conversion rules *)
(* ------------------------------------------------ *)

Inductive Ctx : nat -> Type := 
| ctx_empty    : Ctx 0
| ctx_extend n : Ctx n -> Tm n -> Ctx (S n).

Arguments ctx_extend {_}.

Fixpoint lookup {n} (x : fin n) : Ctx n -> Tm n.
  destruct n; cbn in x. done.
  destruct x as [p|]; move=> tl; inversion tl.
  - exact (lookup _ p X)⟨↑⟩.
  - exact (X0⟨↑⟩).
Defined.

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
    typing (ctx_extend Γ A) B tuniv -> 
    typing (ctx_extend Γ A) N B ->
    typing Γ (abs A N) (tpi A B)
  | t_app n (Γ : Ctx n) A B N M : 
    typing Γ A tuniv -> 
    typing (ctx_extend Γ A) B tuniv -> 
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

  | t_case n (Γ : Ctx n) (T : Tm (S n)) M M0 M1 :
    typing (ctx_extend Γ tnat) T tuniv ->
    typing Γ M tnat ->
    typing Γ M0 (T[zero..]) ->
    typing (ctx_extend Γ tnat) M1 T[rho] ->
    typing Γ (ncase M M0 M1) (T[M..])
  (* universes *)
  | t_tpi n (Γ : Ctx n) A B : 
    typing Γ A tuniv ->
    typing (ctx_extend Γ A) B tuniv -> 
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
    typing (ctx_extend Γ A) B tuniv -> 
    conv Γ N N' (tpi A B) ->
    typing Γ M A ->
    conv Γ (app N M) (app N' M) B[M..]
  | c_app2 n (Γ : Ctx n) A B N M M'  :          
    typing Γ A tuniv -> 
    typing (ctx_extend Γ A) B tuniv -> 
    typing Γ N (tpi A B) ->
    conv Γ M M' A ->
    conv Γ (app N M) (app N M') B[M..]
  | c_beta n (Γ : Ctx n) A B M N :
    typing Γ A tuniv -> 
    typing (ctx_extend Γ A) B tuniv -> 
    typing (ctx_extend Γ A) N B -> 
    typing Γ M A ->
    conv Γ (app (abs A N) M) N[M..] B[M..]
  | c_eta n (Γ : Ctx n) A B N N' :
    typing Γ A tuniv ->
    typing Γ N (tpi A B) ->
    typing Γ N' (tpi A B) ->
    conv (ctx_extend Γ A) (app N⟨↑⟩ (var var_zero))
      (app N'⟨↑⟩ (var var_zero)) B ->
    conv Γ N N' (tpi A B)

  (* natural numbers: *)
  
  | c_ncase_Z n (Γ : Ctx n) M0 M1 (T : Tm (S n)) : 
    typing (ctx_extend Γ  tnat) T tuniv ->
    typing Γ M0 (T[zero..]) ->
    typing (ctx_extend Γ tnat) M1 T[rho] ->   
    conv Γ (ncase zero M0 M1) M0 T[zero..]

  | c_ncase_S n (Γ : Ctx n) T M0 M1 N : 
    typing (ctx_extend Γ tnat) T tuniv ->
    typing Γ N tnat ->
    typing Γ M0 (T[zero..]) ->
    typing (ctx_extend Γ tnat) M1 T[rho] ->        
    conv Γ (ncase (succ N) M0 M1) M1[N..] T[(succ N)..] 

  | c_ncase n (Γ : Ctx n) T M M0 M1 M' M0' M1' : 
    typing (ctx_extend Γ tnat) T tuniv ->
    (* The successor branch of the *right* case must be typed, not merely
       convertible to [M1].  Admissible (it follows from [conv_typing] applied
       to the last premise), so the relation is unchanged; it is stated because
       semantic adequacy needs [semantic_typing] of [M1'] -- the two sides of
       the congruence reduce to the branch at *different* predecessor terms,
       and only [semantic_typing] carries the required cross-substitution
       information.  Compare [c_abs], which likewise carries typings for both
       bodies. *)
    typing (ctx_extend Γ tnat) M1' T[rho] ->
    conv Γ M M' tnat ->
    conv Γ M0 M0' T[zero..] ->
    conv (ctx_extend Γ tnat) M1 M1' T[rho] ->        
    conv Γ (ncase M M0 M1) (ncase M' M0' M1') T[M..]

  | c_succ n (Γ : Ctx n) M N :
    conv Γ M N tnat ->
    conv Γ (succ M) (succ N) tnat
  | c_abs n (Γ : Ctx n) A A' B M M' :
    typing Γ A tuniv ->
    typing Γ A' tuniv ->
    typing (ctx_extend Γ A) B tuniv ->
    typing (ctx_extend Γ A) M B ->
    typing (ctx_extend Γ A) M' B ->
    conv Γ A A' tuniv ->
    conv (ctx_extend Γ A) M M' B ->
    conv Γ (abs A M) (abs A' M') (tpi A B)
  | c_tpi n (Γ : Ctx n) A0 A1 B0 B1 :
    typing Γ A0 tuniv ->
    typing Γ A1 tuniv ->
    typing (ctx_extend Γ A0) B0 tuniv ->
    typing (ctx_extend Γ A1) B1 tuniv ->
    conv Γ A0 A1 tuniv ->
    conv (ctx_extend Γ A0) B0 B1 tuniv ->
    conv Γ (tpi A0 B0) (tpi A1 B1) tuniv
with ctx : forall {n}, Ctx n -> Prop :=
  | c_empty : ctx ctx_empty
  | c_cons n (Γ : Ctx n) A : ctx Γ -> 
     typing Γ A tuniv -> 
     ctx (ctx_extend Γ A).

(** Rules with unconstrained types *)
Definition t_var' {n} (Γ : Ctx n) x τ : 
  lookup x Γ = τ -> ctx Γ -> typing Γ (var x) τ.
Proof. intros <-. eapply t_var. Qed.

Definition t_app' {n} (Γ : Ctx n) (A : Tm n) 
  (B : Tm (S n)) (N M : Tm n) (C:Tm n) :
       typing Γ A tuniv -> typing (ctx_extend Γ A) B tuniv -> typing Γ N (tpi A B) 
       -> typing Γ M A  -> B[M..] = C -> typing Γ (app N M) C.
Proof. intros. subst. eapply t_app; eauto. Qed. 

Definition t_univ' {n} (Γ : Ctx n) A :
  tuniv = A -> ctx Γ ->
  typing Γ tuniv A.
Proof. intros <- h. eapply t_univ; eauto. Qed.

Definition c_app1' {n} (Γ : Ctx n) A B N N' M C :
    typing Γ A tuniv -> typing (ctx_extend Γ A) B tuniv -> conv Γ N N' (tpi A B) ->
    typing Γ M A -> B[M..] = C -> conv Γ (app N M) (app N' M) C.
Proof. intros; subst; eauto using c_app1. Qed.

Definition c_app2' {n} (Γ : Ctx n) A B N M M' C :
    typing Γ A tuniv -> typing (ctx_extend Γ A) B tuniv ->
    typing Γ N (tpi A B) ->  conv Γ M M' A ->  B[M..] = C ->
    conv Γ (app N M) (app N M') C.
Proof. intros; subst; eauto using c_app2. Qed.

Definition c_beta' {n} (Γ : Ctx n) A B M N C D :
    typing Γ A tuniv -> typing (ctx_extend Γ A) B tuniv ->
    typing (ctx_extend Γ A) N B -> typing Γ M A ->
    N[M..] = C -> B[M..] = D -> conv Γ (app (abs A N) M) C D.
Proof. intros; subst; eauto using c_beta. Qed.

Definition t_case' {n} (Γ : Ctx n) (T : Tm (S n)) M M0 M1 C :
    typing (ctx_extend Γ tnat) T tuniv ->
    typing Γ M tnat ->
    typing Γ M0 (T[zero..]) ->
    typing (ctx_extend Γ tnat) M1 T[rho] ->
    T[M..] = C ->
    typing Γ (ncase M M0 M1) C.
Proof. intros; subst; eauto using t_case. Qed.

Definition c_ncase_Z' {n} (Γ : Ctx n) (T : Tm (S n)) M0 M1 C :
    typing (ctx_extend Γ tnat) T tuniv ->
    typing Γ M0 (T[zero..]) ->
    typing (ctx_extend Γ tnat) M1 T[rho] ->
    T[zero..] = C ->
    conv Γ (ncase zero M0 M1) M0 C.
Proof. intros; subst; eauto using c_ncase_Z. Qed.

Definition c_ncase_S'' {n} (Γ : Ctx n) (T : Tm (S n)) M0 M1 N C D :
    typing (ctx_extend Γ tnat) T tuniv ->
    typing Γ N tnat ->
    typing Γ M0 (T[zero..]) ->
    typing (ctx_extend Γ tnat) M1 T[rho] ->
    M1[N..] = C -> T[(succ N)..] = D ->
    conv Γ (ncase (succ N) M0 M1) C D.
Proof. intros; subst; eauto using c_ncase_S. Qed.

Definition c_ncase' {n} (Γ : Ctx n) (T : Tm (S n)) M M0 M1 M' M0' M1' C :
    typing (ctx_extend Γ tnat) T tuniv ->
    typing (ctx_extend Γ tnat) M1' T[rho] ->
    conv Γ M M' tnat ->
    conv Γ M0 M0' (T[zero..]) ->
    conv (ctx_extend Γ tnat) M1 M1' T[rho] ->
    T[M..] = C ->
    conv Γ (ncase M M0 M1) (ncase M' M0' M1') C.
Proof. intros; subst; eauto using c_ncase. Qed.

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

#[export] Hint Resolve t_var' t_univ' : syntax.

#[export] Hint Constructors typing conv : syntax.

Module Notations.
Notation "Γ ++ A" := (ctx_extend Γ A) : syntax_scope.
Notation "Γ ⊢e a ∈ A" := (typing Γ a A) (at level 70) : syntax_scope.
Notation "Γ ⊢e a ≡ b ∈ A" := (conv Γ a b A) (at level 70) : syntax_scope.
End Notations.

Import Notations.
Open Scope syntax_scope.

(** typing/conv implies the context is well-formed *)

Lemma typing_ctx {n} (Γ : Ctx n) M A :
  Γ ⊢e M ∈ A -> ctx Γ.
Proof. move=> h. induction h; eauto. Qed.

Lemma conv_ctx {n} (Γ : Ctx n) M N A :
  Γ ⊢e M ≡ N ∈ A -> ctx Γ.
Proof. move=> h. induction h; eauto using typing_ctx. Qed.


(* Single substitution commutes with [σ] *)
Lemma subst1_subst_comm {n m} {B : Tm (S n)}{N : Tm n}{σ : fin n -> Tm m} :
  B[N..][σ] = B[⇑ σ][N[σ]..].
Proof. asimpl. done. Qed.

Lemma subst1_ren_comm {n m} {B : Tm (S n)}{M : Tm n}{δ : fin n -> fin m} :
  ⟨δ⟩ B[M..] = B⟨up_ren δ⟩[M⟨δ⟩..].
Proof. asimpl. done. Qed.

Lemma subst_cons_eq {n m} (B : Tm (S n)) (N : Tm m) (σ : fin n -> Tm m) :
  B[N .: σ] = B[⇑ σ][N..].
Proof. asimpl. done. Qed.

Lemma ren_up_shift {n m} (δ : fin n -> fin m) (N : Tm n) :
  (N⟨↑⟩)⟨up_ren δ⟩ = (N⟨δ⟩)⟨↑⟩.
Proof. asimpl. done. Qed.

(* [rho] -- the [succ (var 0)] shift that types the dependent case's successor
   branch -- commutes with a lifted substitution and with a lifted renaming. *)
Lemma rho_subst_up {n m} (T : Tm (S n)) (σ : fin n -> Tm m) :
  (T[⇑ σ])[rho] = (T[rho])[⇑ σ].
Proof. unfold rho. asimpl. setoid_rewrite rinstInst'_Tm_pointwise. reflexivity. Qed.

Lemma rho_ren_up {n m} (T : Tm (S n)) (δ : fin n -> fin m) :
  (T⟨up_ren δ⟩)[rho] = ⟨up_ren δ⟩ (T[rho]).
Proof. unfold rho. asimpl. reflexivity. Qed.


(** * Renaming and substitution properties *)

(* Agda: RenTypes *)
Definition typing_renaming {n} (Δ : Ctx n) 
  {m} (δ : fin m -> fin n) (Γ : Ctx m) : Prop :=  
  forall i, lookup (δ i) Δ  = (lookup i Γ)⟨δ⟩.

(** The identity renaming preserves the context *)
Lemma typing_renaming_id {n} (Δ : Ctx n) :
  typing_renaming Δ id Δ.
Proof. unfold typing_renaming. intros x. asimpl. done. Qed.

(** shift extends the context *)
Lemma typing_renaming_shift {n} (Γ : Ctx n) (τ : Tm n) :
    typing_renaming (Γ ++ τ) shift Γ.
Proof. unfold typing_renaming. intros x. asimpl. fsimpl. done. Qed.

(** Lift a renaming to a new scope *)
Lemma typing_renaming_lift {n} (Δ : Ctx n) 
  {m} (Γ : Ctx m) (δ : fin m -> fin n) (τ : Tm m) :
  typing_renaming Δ δ Γ ->
  typing_renaming (Δ ++ τ⟨δ⟩) (up_ren δ) (Γ ++ τ).
Proof. intro h. unfold typing_renaming in *.
       auto_case; asimpl; try done. unfold ">>". rewrite h.
       asimpl. done.
Qed.

Create HintDb renaming.
#[export] Hint Resolve typing_renaming_lift 
  typing_renaming_id typing_renaming_shift : renaming.

Fixpoint renaming_typing {n} (Γ : Ctx n) a A {m} (Δ:Ctx m) δ 
  (h : Γ ⊢e a ∈ A) {struct h} :
         typing_renaming Δ δ Γ -> ctx Δ -> Δ ⊢e a⟨δ⟩ ∈ A⟨δ⟩
with renaming_conv {n} (Γ : Ctx n) a b A {m} (Δ:Ctx m) δ 
  (h : Γ ⊢e a ≡ b ∈ A) {struct h} :
    typing_renaming Δ δ Γ ->  ctx Δ -> Δ ⊢e a⟨δ⟩ ≡ b⟨δ⟩ ∈ A⟨δ⟩.
Proof.
  (* typing *)
  - intros tR wtΔ.
    dependent destruction h; subst.
    all: try have EC: ctx (Δ ++ A ⟨δ⟩) by
      eapply c_cons; eauto;
        eapply renaming_typing with (A:=tuniv); eauto.
    all: cbn.
    all: try solve [econstructor; 
                    eauto with renaming;
                    try eapply renaming_typing with (A:=tnat); 
                    try eapply renaming_typing with (A:=tuniv); 
                    try eapply renaming_conv   with (A:=tuniv); 
                    try eapply renaming_conv   with (A:=tnat); 
                    eauto with renaming].
    + eapply t_var'; eauto with renaming.
    + rewrite subst1_ren_comm.
      eapply t_app; eauto with renaming.
      eapply renaming_typing with (A:=tuniv); eauto with renaming.
      eapply renaming_typing with (A:=tuniv); eauto with renaming.
      eapply renaming_typing in h3; eauto.
    + (* t_case: renaming a dependent case *)
      have Ctn : ctx (Δ ++ tnat)
        by (eapply c_cons; [ exact wtΔ | apply t_nat; exact wtΔ ]).
      have TRl : typing_renaming (Δ ++ tnat) (up_ren δ) (Γ ++ tnat)
        := @typing_renaming_lift m Δ n Γ δ tnat tR.
      have TT : typing (Δ ++ tnat) (T⟨up_ren δ⟩) tuniv.
      { move: (renaming_typing _ _ T tuniv _ _ (up_ren δ) h1 TRl Ctn) => hh.
        asimpl in hh. exact hh. }
      have TM : typing Δ (M⟨δ⟩) tnat.
      { move: (renaming_typing _ _ M tnat _ _ δ h2 tR wtΔ) => hh.
        asimpl in hh. exact hh. }
      have TM0 : typing Δ (M0⟨δ⟩) ((T⟨up_ren δ⟩)[zero..]).
      { move: (renaming_typing _ _ M0 (T[zero..]) _ _ δ h3 tR wtΔ) => hh.
        asimpl in hh. asimpl. exact hh. }
      have TM1 : typing (Δ ++ tnat) (M1⟨up_ren δ⟩) ((T⟨up_ren δ⟩)[rho]).
      { move: (renaming_typing _ _ M1 (T[rho]) _ _ (up_ren δ) h4 TRl Ctn) => hh.
        rewrite rho_ren_up. exact hh. }
      eapply t_case';
        [ exact TT | exact TM | exact TM0 | exact TM1 | first [ asimpl; reflexivity | symmetry; apply subst1_ren_comm ] ].
  - intros tR wtΔ.
    dependent destruction h; subst.
    all: try have EC: ctx (Δ ++ A ⟨δ⟩) by
      eapply c_cons; eauto;
        eapply renaming_typing with (A:=tuniv); eauto.
    all: cbn.
    all: try solve [econstructor; 
                    eauto with renaming;
                    try eapply renaming_typing with (A:=tnat); 
                    try eapply renaming_typing with (A:=tuniv); 
                    try eapply renaming_conv   with (A:=tuniv); 
                    eauto with renaming].
    + rewrite subst1_ren_comm.
      eapply c_app1; eauto with renaming.
      eapply renaming_typing with (A:=tuniv); eauto.
      eapply renaming_typing with (A:=tuniv); eauto with renaming.
      asimpl.
      eapply renaming_conv in h; eauto with renaming.
    + rewrite subst1_ren_comm.
      eapply c_app2; eauto with renaming.
      eapply renaming_typing with (A:=tuniv); eauto.
      eapply renaming_typing with (A:=tuniv); eauto with renaming.
      asimpl.
      eapply renaming_typing in H1; eauto with renaming.
    + repeat rewrite subst1_ren_comm.
      eapply c_beta; eauto.
      eapply renaming_typing with (A:=tuniv); eauto.
      eapply renaming_typing with (A:=tuniv); eauto with renaming.
      eapply renaming_typing; eauto with renaming.
    + eapply c_eta; eauto.
      eapply renaming_typing with (A:=tuniv); eauto.
      eapply renaming_typing with (A:=tpi A B); eauto with renaming.
      eapply renaming_typing with (A:=tpi A B); eauto with renaming.
      eapply renaming_conv with (Δ := Δ ++ A⟨δ⟩)(δ:=up_ren δ) in h;
        eauto with renaming.
      asimpl in h. done.
    + (* c_ncase_Z *)
      have Ctn : ctx (Δ ++ tnat)
        by (eapply c_cons; [ exact wtΔ | apply t_nat; exact wtΔ ]).
      have TRl : typing_renaming (Δ ++ tnat) (up_ren δ) (Γ ++ tnat)
        := @typing_renaming_lift m Δ n Γ δ tnat tR.
      have TT : typing (Δ ++ tnat) (T⟨up_ren δ⟩) tuniv.
      { move: (renaming_typing _ _ T tuniv _ _ (up_ren δ) H TRl Ctn) => hh.
        asimpl in hh. exact hh. }
      have TM0 : typing Δ (M0⟨δ⟩) ((T⟨up_ren δ⟩)[zero..]).
      { move: (renaming_typing _ _ M0 (T[zero..]) _ _ δ H0 tR wtΔ) => hh.
        asimpl in hh. asimpl. exact hh. }
      have TM1 : typing (Δ ++ tnat) (M1⟨up_ren δ⟩) ((T⟨up_ren δ⟩)[rho]).
      { move: (renaming_typing _ _ M1 (T[rho]) _ _ (up_ren δ) H1 TRl Ctn) => hh.
        rewrite rho_ren_up. exact hh. }
      eapply c_ncase_Z';
        [ exact TT | exact TM0 | exact TM1 | first [ asimpl; reflexivity | symmetry; apply subst1_ren_comm ] ].
    + (* c_ncase_S *)
      have Ctn : ctx (Δ ++ tnat)
        by (eapply c_cons; [ exact wtΔ | apply t_nat; exact wtΔ ]).
      have TRl : typing_renaming (Δ ++ tnat) (up_ren δ) (Γ ++ tnat)
        := @typing_renaming_lift m Δ n Γ δ tnat tR.
      have TT : typing (Δ ++ tnat) (T⟨up_ren δ⟩) tuniv.
      { move: (renaming_typing _ _ T tuniv _ _ (up_ren δ) H TRl Ctn) => hh.
        asimpl in hh. exact hh. }
      have TN : typing Δ (N⟨δ⟩) tnat.
      { move: (renaming_typing _ _ N tnat _ _ δ H0 tR wtΔ) => hh.
        asimpl in hh. exact hh. }
      have TM0 : typing Δ (M0⟨δ⟩) ((T⟨up_ren δ⟩)[zero..]).
      { move: (renaming_typing _ _ M0 (T[zero..]) _ _ δ H1 tR wtΔ) => hh.
        asimpl in hh. asimpl. exact hh. }
      have TM1 : typing (Δ ++ tnat) (M1⟨up_ren δ⟩) ((T⟨up_ren δ⟩)[rho]).
      { move: (renaming_typing _ _ M1 (T[rho]) _ _ (up_ren δ) H2 TRl Ctn) => hh.
        rewrite rho_ren_up. exact hh. }
      eapply c_ncase_S'';
        [ exact TT | exact TN | exact TM0 | exact TM1
        | first [ asimpl; reflexivity | symmetry; apply subst1_ren_comm ] | first [ asimpl; reflexivity | symmetry; apply subst1_ren_comm ] ].
    + (* c_ncase *)
      have Ctn : ctx (Δ ++ tnat)
        by (eapply c_cons; [ exact wtΔ | apply t_nat; exact wtΔ ]).
      have TRl : typing_renaming (Δ ++ tnat) (up_ren δ) (Γ ++ tnat)
        := @typing_renaming_lift m Δ n Γ δ tnat tR.
      have TT : typing (Δ ++ tnat) (T⟨up_ren δ⟩) tuniv.
      { move: (renaming_typing _ _ T tuniv _ _ (up_ren δ) H TRl Ctn) => hh.
        asimpl in hh. exact hh. }
      have TM1' : typing (Δ ++ tnat) (M1'⟨up_ren δ⟩) ((T⟨up_ren δ⟩)[rho]).
      { move: (renaming_typing _ _ M1' (T[rho]) _ _ (up_ren δ) H0 TRl Ctn) => hh.
        rewrite rho_ren_up. exact hh. }
      have CM : conv Δ (M⟨δ⟩) (M'⟨δ⟩) tnat.
      { move: (renaming_conv _ _ M M' tnat _ _ δ h1 tR wtΔ) => hh.
        asimpl in hh. exact hh. }
      have CM0 : conv Δ (M0⟨δ⟩) (M0'⟨δ⟩) ((T⟨up_ren δ⟩)[zero..]).
      { move: (renaming_conv _ _ M0 M0' (T[zero..]) _ _ δ h2 tR wtΔ) => hh.
        asimpl in hh. asimpl. exact hh. }
      have CM1 : conv (Δ ++ tnat) (M1⟨up_ren δ⟩) (M1'⟨up_ren δ⟩) ((T⟨up_ren δ⟩)[rho]).
      { move: (renaming_conv _ _ M1 M1' (T[rho]) _ _ (up_ren δ) h3 TRl Ctn) => hh.
        rewrite rho_ren_up. exact hh. }
      eapply c_ncase';
        [ exact TT | exact TM1' | exact CM | exact CM0 | exact CM1
        | first [ asimpl; reflexivity | symmetry; apply subst1_ren_comm ] ].
    + eapply c_succ.
      eapply renaming_conv with (A:=tnat); eauto.
    + (* tpi *)
      have EC0: ctx (Δ ++ A0⟨δ⟩) by
       eapply c_cons; eauto;
       eapply renaming_typing with (A:= tuniv); eauto.
      have EC1: ctx (Δ ++ A1⟨δ⟩) by
       eapply c_cons; eauto;
       eapply renaming_typing with (A:= tuniv); eauto.
      eapply c_tpi; eauto.
      eapply renaming_typing with (A:= tuniv); eauto.
      eapply renaming_typing with (A:= tuniv); eauto.
      eapply renaming_typing with (A:= tuniv); eauto with renaming.
      eapply renaming_typing with (A:= tuniv); eauto with renaming.
      eapply renaming_conv with (A:= tuniv); eauto.
      eapply renaming_conv with (A:= tuniv); eauto with renaming.
Qed.

(** * All types in well-formed contexts are well-formed *)
Lemma ctx_typing_lookup {n} (Γ : Ctx n) : 
  ctx Γ ->  forall x, Γ ⊢e lookup x Γ ∈ tuniv.
Proof.
  move=> h. induction h; try done.
  auto_case; unfold core.funcomp;
    eapply renaming_typing with (A := Core.tuniv) (δ:=↑);
    eauto with renaming;
    eapply c_cons; eauto.
Qed.
      
(** * Substitution lemmas *)

(* A substitution is well-typed when every variable has the type 
   specified by the context (after substitution) *)
Definition typing_subst {n} (Δ : Ctx n) {m} (σ : fin m -> Tm n)
  (Γ : Ctx m) : Prop := 
  forall x, Δ ⊢e σ x ∈ (lookup x Γ)[σ].

Lemma typing_subst_null {n} (Δ : Ctx n) :
  typing_subst Δ null ctx_empty.
Proof. unfold typing_subst. auto_case. Qed.

Lemma typing_subst_id {n} (Δ : Ctx n) :
  ctx Δ -> typing_subst Δ var Δ.
Proof. move=>h. unfold typing_subst. intro x. asimpl. 
       econstructor; eauto. Qed.

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

Lemma typing_subst_cons {n} (Δ : Ctx n) {m} (σ : fin m -> Tm n)
  (Γ : Ctx m) e τ : 
 Δ ⊢e e ∈ τ[σ] -> typing_subst Δ σ Γ ->
 typing_subst Δ (e .: σ) (Γ ++ τ).
Proof. intros. unfold typing_subst in *. intros [y|]; asimpl; eauto. Qed.


(** Add the substitution lemmas as hints *)
#[export] Hint Resolve typing_subst_lift
  typing_subst_id typing_subst_null : renaming.

Fixpoint
  substitution_tm {n} (Γ : Ctx n) a A {m} (Δ:Ctx m) σ : 
  Γ ⊢e a ∈ A -> typing_subst Δ σ Γ -> ctx Δ -> Δ ⊢e a[σ] ∈ A[σ]
with 
 substitution_conv {n} (Γ : Ctx n) a b A {m} (Δ:Ctx m) σ : 
  Γ ⊢e a ≡ b ∈ A -> typing_subst Δ σ Γ -> ctx Δ -> Δ ⊢e a[σ] ≡ b[σ] ∈ A[σ]
.
Proof.
  all: intros h tS tΔ.
  - dependent destruction h; subst.
    all: cbn; asimpl.
    all: try (have EC: ctx (Δ ++ A[σ]) by
          eapply c_cons; eauto;
          eapply substitution_tm with (A:= tuniv); eauto).
    all: try solve [econstructor; 
                    try eapply substitution_tm with (A:=tuniv); 
                    eauto with syntax renaming].
    + unfold typing_subst in tS. eauto.
    + eapply t_conv; 
        try eapply substitution_conv with (A:=tuniv);
        eauto with renaming.
    + eapply t_app'; eauto.
      eapply substitution_tm with (A:= tuniv); eauto.
      eapply substitution_tm with (A:= tuniv); eauto with renaming.
      eapply substitution_tm with (A:= tpi A B); eauto with renaming.
      asimpl. reflexivity.
    + (* t_case: substituting a dependent case.  [asimpl] has already put the
         goal's motive in the [T[M[σ] .: σ]] form; [subst_cons_eq] turns it into
         the [T[⇑σ][M[σ]..]] shape that [t_case] concludes with. *)
      have Ctn : ctx (Δ ++ tnat)
        by (eapply c_cons; [ exact tΔ | apply t_nat; exact tΔ ]).
      have TSl : typing_subst (Δ ++ tnat) (⇑ σ) (Γ ++ tnat)
        := @typing_subst_lift m Δ n σ Γ tnat Ctn tS.
      have TT : typing (Δ ++ tnat) (T[⇑ σ]) tuniv.
      { move: (substitution_tm _ _ T tuniv _ _ (⇑ σ) h1 TSl Ctn) => hh.
        asimpl in hh. exact hh. }
      have TM : typing Δ (M[σ]) tnat.
      { move: (substitution_tm _ _ M tnat _ _ σ h2 tS tΔ) => hh.
        asimpl in hh. exact hh. }
      have TM0 : typing Δ (M0[σ]) ((T[⇑ σ])[zero..]).
      { move: (substitution_tm _ _ M0 (T[zero..]) _ _ σ h3 tS tΔ) => hh.
        asimpl in hh. asimpl. exact hh. }
      have TM1 : typing (Δ ++ tnat) (M1[⇑ σ]) ((T[⇑ σ])[rho]).
      { move: (substitution_tm _ _ M1 (T[rho]) _ _ (⇑ σ) h4 TSl Ctn) => hh.
        rewrite rho_subst_up. exact hh. }
      eapply t_case';
        [ exact TT | exact TM | exact TM0 | exact TM1 | asimpl; reflexivity ].
  - dependent destruction h; subst.
    all: try (have EC: ctx (Δ ++ A[σ]) by
       eapply c_cons; eauto;
       eapply substitution_tm with (A:= tuniv); eauto).
    + eapply c_conv; eauto.
      eapply substitution_conv with (A:=tuniv); eauto.
    + eapply c_refl; eauto.
    + eapply c_sym; eauto.
    + eapply c_trans; eauto.
    + (* t_app1 *)
      cbn. rewrite subst1_subst_comm.
      eapply c_app1; eauto.
      eapply substitution_tm with (A:=tuniv); eauto.
      eapply substitution_tm with (A:=tuniv); eauto with renaming.
      eapply substitution_conv with (A:= tpi A B); eauto.
    + (* t_app2 *)
      cbn. rewrite subst1_subst_comm.
      eapply c_app2; eauto.
      eapply substitution_tm with (A:=tuniv); eauto.
      eapply substitution_tm with (A:=tuniv); eauto with renaming.
      eapply substitution_tm with (A:= tpi A B); eauto.
    + (* beta *)
      cbn. repeat rewrite subst1_subst_comm.
      eapply c_beta; eauto.
      eapply substitution_tm with (A:=tuniv); eauto.
      eapply substitution_tm with (A:=tuniv); eauto with renaming.
      eapply substitution_tm; eauto with renaming.
    + (* eta *)
      cbn. 
      eapply c_eta; eauto.
      eapply substitution_tm with (A:=tuniv); eauto.
      eapply substitution_tm with (A:=tpi A B); eauto with renaming.
      eapply substitution_tm with (A:=tpi A B); eauto with renaming.
      eapply substitution_conv with (Δ := Δ ++ A[σ])(σ:=⇑σ) in h;
        eauto with renaming.
      asimpl in h. done.
    + (* c_ncase_Z *)
      have Ctn : ctx (Δ ++ tnat)
        by (eapply c_cons; [ exact tΔ | apply t_nat; exact tΔ ]).
      have TSl : typing_subst (Δ ++ tnat) (⇑ σ) (Γ ++ tnat)
        := @typing_subst_lift m Δ n σ Γ tnat Ctn tS.
      have TT : typing (Δ ++ tnat) (T[⇑ σ]) tuniv.
      { move: (substitution_tm _ _ T tuniv _ _ (⇑ σ) H TSl Ctn) => hh.
        asimpl in hh. exact hh. }
      have TM0 : typing Δ (M0[σ]) ((T[⇑ σ])[zero..]).
      { move: (substitution_tm _ _ M0 (T[zero..]) _ _ σ H0 tS tΔ) => hh.
        asimpl in hh. asimpl. exact hh. }
      have TM1 : typing (Δ ++ tnat) (M1[⇑ σ]) ((T[⇑ σ])[rho]).
      { move: (substitution_tm _ _ M1 (T[rho]) _ _ (⇑ σ) H1 TSl Ctn) => hh.
        rewrite rho_subst_up. exact hh. }
      cbn.
      eapply c_ncase_Z';
        [ exact TT | exact TM0 | exact TM1 | asimpl; reflexivity ].
    + (* c_ncase_S *)
      have Ctn : ctx (Δ ++ tnat)
        by (eapply c_cons; [ exact tΔ | apply t_nat; exact tΔ ]).
      have TSl : typing_subst (Δ ++ tnat) (⇑ σ) (Γ ++ tnat)
        := @typing_subst_lift m Δ n σ Γ tnat Ctn tS.
      have TT : typing (Δ ++ tnat) (T[⇑ σ]) tuniv.
      { move: (substitution_tm _ _ T tuniv _ _ (⇑ σ) H TSl Ctn) => hh.
        asimpl in hh. exact hh. }
      have TN : typing Δ (N[σ]) tnat.
      { move: (substitution_tm _ _ N tnat _ _ σ H0 tS tΔ) => hh.
        asimpl in hh. exact hh. }
      have TM0 : typing Δ (M0[σ]) ((T[⇑ σ])[zero..]).
      { move: (substitution_tm _ _ M0 (T[zero..]) _ _ σ H1 tS tΔ) => hh.
        asimpl in hh. asimpl. exact hh. }
      have TM1 : typing (Δ ++ tnat) (M1[⇑ σ]) ((T[⇑ σ])[rho]).
      { move: (substitution_tm _ _ M1 (T[rho]) _ _ (⇑ σ) H2 TSl Ctn) => hh.
        rewrite rho_subst_up. exact hh. }
      cbn.
      eapply c_ncase_S'';
        [ exact TT | exact TN | exact TM0 | exact TM1
        | asimpl; reflexivity | asimpl; reflexivity ].
    + (* c_ncase *)
      have Ctn : ctx (Δ ++ tnat)
        by (eapply c_cons; [ exact tΔ | apply t_nat; exact tΔ ]).
      have TSl : typing_subst (Δ ++ tnat) (⇑ σ) (Γ ++ tnat)
        := @typing_subst_lift m Δ n σ Γ tnat Ctn tS.
      have TT : typing (Δ ++ tnat) (T[⇑ σ]) tuniv.
      { move: (substitution_tm _ _ T tuniv _ _ (⇑ σ) H TSl Ctn) => hh.
        asimpl in hh. exact hh. }
      have TM1' : typing (Δ ++ tnat) (M1'[⇑ σ]) ((T[⇑ σ])[rho]).
      { move: (substitution_tm _ _ M1' (T[rho]) _ _ (⇑ σ) H0 TSl Ctn) => hh.
        rewrite rho_subst_up. exact hh. }
      have CM : conv Δ (M[σ]) (M'[σ]) tnat.
      { move: (substitution_conv _ _ M M' tnat _ _ σ h1 tS tΔ) => hh.
        asimpl in hh. exact hh. }
      have CM0 : conv Δ (M0[σ]) (M0'[σ]) ((T[⇑ σ])[zero..]).
      { move: (substitution_conv _ _ M0 M0' (T[zero..]) _ _ σ h2 tS tΔ) => hh.
        asimpl in hh. asimpl. exact hh. }
      have CM1 : conv (Δ ++ tnat) (M1[⇑ σ]) (M1'[⇑ σ]) ((T[⇑ σ])[rho]).
      { move: (substitution_conv _ _ M1 M1' (T[rho]) _ _ (⇑ σ) h3 TSl Ctn) => hh.
        rewrite rho_subst_up. exact hh. }
      cbn.
      eapply c_ncase';
        [ exact TT | exact TM1' | exact CM | exact CM0 | exact CM1
        | asimpl; reflexivity ].
    + cbn.
      eapply c_succ.
      eapply substitution_conv with (A:=tnat); eauto.
    + (* abs *)
      cbn.
      eapply c_abs; eauto.
      eapply substitution_tm with (A:=tuniv); eauto.
      eapply substitution_tm with (A:=tuniv); eauto.
      eapply substitution_tm with (A:=tuniv); eauto with renaming.
      eapply substitution_tm; eauto with renaming.
      eapply substitution_tm; eauto with renaming.
      eapply substitution_conv with (A:=tuniv); eauto.
      eapply substitution_conv; eauto with renaming.

    + (* tpi *)
      cbn.
      have EC0: ctx (Δ ++ A0[σ]).
      { eapply c_cons; eauto;
        eapply substitution_tm with (A:= tuniv); eauto.
      }
      have EC1: ctx (Δ ++ A1[σ]).
      { eapply c_cons; eauto;
        eapply substitution_tm with (A:= tuniv); eauto.
      }
      eapply c_tpi; eauto.
      eapply substitution_tm with (A:= tuniv); eauto.
      eapply substitution_tm with (A:= tuniv); eauto.
      eapply substitution_tm with (A:= tuniv);
        eauto with renaming.
      eapply substitution_tm with (A:= tuniv);
        eauto with renaming.
      eapply substitution_conv with (A:= tuniv);
        eauto.
      eapply substitution_conv with (A:= tuniv);
        eauto with renaming.
Qed.

(* ----------- context conversion -------------- *)

Lemma lookup_weaken {n}(Γ:Ctx n) A y : 
   lookup (Some y : fin (S n)) (Γ ++ A) = (lookup y Γ)[↑ >> var].
Proof. cbn [lookup]. fold fin in y. cbn [f_equal].
cbn. auto_unfold. move: (@rinstInst'_Tm _ _ shift (lookup y Γ)) => h. done.
Qed.


Lemma ctc_conv_typing_subst {n} (Γ:Ctx n) A A' : 
  Γ ⊢e A ∈ tuniv -> 
  Γ ⊢e A' ∈ tuniv -> 
  Γ ⊢e A ≡ A' ∈ tuniv -> 
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

(* B[·] respects conversion in its argument. *)
Lemma conv_subst_arg {n} (Γ : Ctx n) A (B : Tm (S n)) M M' :
  Γ ⊢e A ∈ tuniv ->  
  Γ ++ A ⊢e B ∈ tuniv ->
  Γ ⊢e M  ∈ A -> 
  Γ ⊢e M' ∈ A -> 
  Γ ⊢e M ≡ M' ∈ A ->
  Γ ⊢e B[M..] ≡ B[M'..] ∈ tuniv.
Proof.
  move=> tA tB tM tM' CMM'.
  have CtxA : ctx (Γ ++ A) by (eapply c_cons; eauto using typing_ctx).
  have tU : typing (Γ ++ A) tuniv tuniv by (apply t_univ; exact CtxA).
  have tabs : typing Γ (abs A B) (tpi A tuniv) by (eapply t_abs; eauto).
  have b1 : conv Γ (app (abs A B) M) B[M..] tuniv
    by (eapply c_beta' with (A:=A)(B:=tuniv)(M:=M)(N:=B); try reflexivity; eauto).
  have b2 : conv Γ (app (abs A B) M') B[M'..] tuniv
    by (eapply c_beta' with (A:=A)(B:=tuniv)(M:=M')(N:=B); try reflexivity; eauto).
  have a2 : conv Γ (app (abs A B) M) (app (abs A B) M') tuniv
    by (eapply c_app2' with (A:=A)(B:=tuniv)(N:=abs A B)(M:=M)(M':=M'); try reflexivity; eauto).
  eapply c_trans; [ apply c_sym; exact b1 | ].
  eapply c_trans; [ exact a2 | exact b2 ].
Qed.

(* Context conversion, with the two domain typings supplied explicitly (so it
   does not depend on [conv_typing] and can be used inside it). *)
Lemma ctx_conv_typing' {n} (Γ:Ctx n) A A' M B :
  Γ ⊢e A ≡ A' ∈ tuniv -> Γ ⊢e A ∈ tuniv -> Γ ⊢e A' ∈ tuniv ->
  Γ ++ A ⊢e M ∈ B -> Γ ++ A' ⊢e M ∈ B.
Proof.
  move=> CA tA tA' TM.
  have TS : typing_subst (Γ ++ A') var (Γ ++ A)
    by (eapply ctc_conv_typing_subst; [ exact tA' | exact tA | apply c_sym; exact CA ]).
  have CTX : ctx (Γ ++ A') by (eapply c_cons; eauto using typing_ctx).
  move: (substitution_tm _ M B _ var TM TS CTX) => h. asimpl in h. exact h.
Qed.

(* Regularity of conversion: both sides of a conversion are well-typed at the
   common type, by induction on [conv]. *)
Lemma conv_typing {n} {Γ : Ctx n} {M N A : Tm n} :
  Γ ⊢e M ≡ N ∈ A -> Γ ⊢e M ∈ A /\ Γ ⊢e N ∈ A.
Proof.
  induction 1;
    repeat match goal with [ H : _ /\ _ |- _ ] => destruct H end;
    split; eauto using t_conv, t_app, t_succ, t_tpi, t_abs.
  - (* c_app2, second side: [app N M' : B[M..]] *)
    eapply t_conv; [ eapply t_app; eauto | ].
    apply c_sym. eapply conv_subst_arg; eauto.
  - (* c_beta, second side: [N[M..] : B[M..]] *)
    eapply substitution_tm;
      [ eauto
      | eapply typing_subst_cons; [ asimpl; eauto | apply typing_subst_id; eauto using typing_ctx ]
      | eauto using typing_ctx ].
  - (* c_ncase_Z, first side: [ncase zero M0 M1 : T[zero..]] *)
    have cG : ctx Γ by (eauto using typing_ctx).
    eapply t_case; [ eassumption | apply t_zero; exact cG | eassumption | eassumption ].
  - (* c_ncase_S, first side: [ncase (succ N) M0 M1 : T[(succ N)..]] *)
    eapply t_case;
      [ eassumption | apply t_succ; eassumption | eassumption | eassumption ].
  - (* c_ncase_S, second side: [M1[N..] : T[(succ N)..]], by substituting the
       successor branch; [(T[rho])[N..]] is [T[(succ N)..]]. *)
    have cG : ctx Γ by (eauto using typing_ctx).
    have EQ : (T[rho])[N..] = T[(succ N)..] by (unfold rho; asimpl).
    rewrite -EQ.
    eapply substitution_tm;
      [ eassumption
      | eapply typing_subst_cons;
          [ asimpl; eassumption | apply typing_subst_id; exact cG ]
      | exact cG ].
  - (* c_ncase, first side *)
    eapply t_case; eassumption.
  - (* c_ncase, second side: [ncase M' M0' M1'] is typed at the *primed* motive
       [T[M'..]], so retype it along [conv T[M..] ≡ T[M'..]]. *)
    have cG : ctx Γ by (eauto using typing_ctx).
    eapply t_conv.
    + eapply t_case; eassumption.
    + apply c_sym. eapply conv_subst_arg;
        [ apply t_nat; exact cG | eassumption | eassumption | eassumption
        | eassumption ].
  - (* c_abs, second side: [abs A' M' : tpi A B] *)
    have TSm : typing_subst (Γ ++ A') var (Γ ++ A)
      by (eapply ctc_conv_typing_subst; [ eauto | eauto | apply c_sym; eauto ]).
    have CtxA' : ctx (Γ ++ A') by (eapply c_cons; eauto using typing_ctx).
    have tBA' : typing (Γ ++ A') B tuniv
      by (move: (substitution_tm _ B tuniv _ var ltac:(eauto) TSm CtxA') => h; asimpl in h; exact h).
    have tM'A' : typing (Γ ++ A') M' B
      by (move: (substitution_tm _ M' B _ var ltac:(eauto) TSm CtxA') => h; asimpl in h; exact h).
    eapply t_conv; [ eapply t_abs; eauto | ].
    apply c_sym. eapply c_tpi;
      [ eauto | eauto | eauto | exact tBA' | eauto | apply c_refl; eauto ].
Qed.

Lemma ctx_conv_typing {n} (Γ:Ctx n) A A' M B :
  Γ ⊢e A ≡ A' ∈ tuniv ->
  Γ ++ A  ⊢e M ∈ B -> 
  Γ ++ A' ⊢e M ∈ B.
Proof.
  move=> CA TM. have [tA tA'] := conv_typing CA.
  eapply ctx_conv_typing'; eauto.
Qed.


Lemma ctx_conv_conv {n} (Γ:Ctx n) A A' M N B :
  Γ ⊢e A ≡ A' ∈ tuniv ->
  Γ ++ A  ⊢e M ≡ N ∈ B -> 
  Γ ++ A' ⊢e M ≡ N ∈ B.
Proof.
  move=> CA CMN.
  have [tA tA'] := conv_typing CA.
  have TS : typing_subst (Γ ++ A') var (Γ ++ A)
    by (eapply ctc_conv_typing_subst; [ exact tA' | exact tA | apply c_sym; exact CA ]).
  have CTX : ctx (Γ ++ A') by (eapply c_cons; eauto using typing_ctx).
  move: (substitution_conv _ _ _ _ _ _ CMN TS CTX) => H.
  asimpl in H. exact H.
Qed.

(** * inversion lemmas for typing *)

Lemma typing_app_inv n (Γ : Ctx n) M N A : 
  Γ ⊢e app M N ∈ A -> 
      exists A1 , exists A2, Γ ⊢e M ∈ tpi A1 A2 /\ Γ ⊢e N ∈ A1 /\ Γ ⊢e A2[N..] ≡ A ∈ tuniv.
Proof. 
  move=> h.
  dependent induction h.
  - specialize (IHh M N ltac:(eauto)).
    destruct IHh as [A1 [A2 [TM [TN CC]]]].
    exists A1. exists A2. repeat split; auto.
    eapply c_trans; eauto.
  - clear IHh1 IHh2 IHh3 IHh4.
    exists A. exists B. repeat split; auto.
    eapply c_refl; eauto.
    eapply substitution_tm with (σ := N..) in h2. cbn in h2.
    eapply h2.
    eapply typing_subst_cons. asimpl. auto.
    eapply typing_subst_id. eapply typing_ctx; eauto.
    eapply typing_ctx; eauto.
Qed.

Lemma typing_abs_inv n (Γ : Ctx n) M A B: 
  Γ ⊢e abs A M ∈ B -> 
      exists B2, Γ ++ A ⊢e M ∈ B2 /\ Γ ⊢e tpi A B2 ≡ B ∈ tuniv.
Proof. 
  move=>h.
  dependent induction h.
  - specialize (IHh M A ltac:(eauto)).
    destruct IHh as [B2 [TM CC]].
    exists B2. repeat split; auto.
    eapply c_trans; eauto.
  - clear IHh1 IHh2 IHh3.
    exists B. repeat split; auto.
    eapply c_refl; eauto.
    eapply t_tpi; eauto.
Qed.

(** Type inversion through conversions for the base type/numeral formers: each
    one's principal type ([tuniv] for [tuniv]/[tnat]/[tpi], [tnat] for
    [zero]/[succ]) is convertible to whatever type the term is given. *)

Lemma typing_univ_inv {n} {Γ : Ctx n} {T} :
  Γ ⊢e tuniv ∈ T -> Γ ⊢e tuniv ≡ T ∈ tuniv.
Proof.
  move=> h; dependent induction h.
  - eapply c_trans; [ first [ eapply IHh; reflexivity | exact IHh ] | eassumption ].
  - apply c_refl; apply t_univ; assumption.
Qed.

Lemma typing_nat_inv {n} {Γ : Ctx n} {T} :
  Γ ⊢e tnat ∈ T -> Γ ⊢e tuniv ≡ T ∈ tuniv.
Proof.
  move=> h; dependent induction h.
  - eapply c_trans; [ first [ eapply IHh; reflexivity | exact IHh ] | eassumption ].
  - apply c_refl; apply t_univ; assumption.
Qed.

Lemma typing_tpi_inv {n} {Γ : Ctx n} {A0 B0 T} :
  Γ ⊢e tpi A0 B0 ∈ T -> Γ ⊢e tuniv ≡ T ∈ tuniv.
Proof.
  move=> h; dependent induction h.
  - eapply c_trans; [ first [ eapply IHh; reflexivity | exact IHh ] | eassumption ].
  - apply c_refl; apply t_univ; eapply typing_ctx; eassumption.
Qed.

Lemma typing_zero_inv {n} {Γ : Ctx n} {T} :
  Γ ⊢e zero ∈ T -> Γ ⊢e tnat ≡ T ∈ tuniv.
Proof.
  move=> h; dependent induction h.
  - eapply c_trans; [ first [ eapply IHh; reflexivity | exact IHh ] | eassumption ].
  - apply c_refl; apply t_nat; assumption.
Qed.

Lemma typing_succ_inv {n} {Γ : Ctx n} {M0 T} :
  Γ ⊢e succ M0 ∈ T -> Γ ⊢e tnat ≡ T ∈ tuniv.
Proof.
  move=> h; dependent induction h.
  - eapply c_trans; [ first [ eapply IHh; reflexivity | exact IHh ] | eassumption ].
  - apply c_refl; apply t_nat; eapply typing_ctx; eassumption.
Qed.

(* The argument of a well-typed successor is a natural number.  (Companion to
   [typing_succ_inv], which only recovers the principal type.) *)
Lemma typing_succ_arg_inv {n} {Γ : Ctx n} {P T} :
  Γ ⊢e succ P ∈ T -> Γ ⊢e P ∈ tnat.
Proof.
  move=> h; dependent induction h.
  - first [ eapply IHh; reflexivity | exact IHh ].
  - assumption.
Qed.


