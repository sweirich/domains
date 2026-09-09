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


(* ---- the derived Pi-types of the based-J eliminator ---------------------
   Agda [ID/Syntax/Raw.agda]:

     motive_ty A   =  (x y : A) -> tid A x y -> U
     base_ty A C   =  (x : A) -> C x x (rfl x)

   Both are spelled out in de Bruijn form.  Inside [motive_ty] the variable
   [x] is index 1 and [y] is index 0, so the identity type's own domain is [A]
   weakened twice.  [jcase C d p] at [p : tid A a b] then has the binder-free
   type [app (app (app C a) b) p], which substitutes definitionally -- that is
   what makes the whole fragment cheap.                                     *)

Definition motive_ty {n} (A : Tm n) : Tm n :=
  tpi A (tpi A⟨↑⟩
          (tpi (tid A⟨↑⟩⟨↑⟩ (var (shift var_zero)) (var var_zero)) tuniv)).

Definition base_ty {n} (A C : Tm n) : Tm n :=
  tpi A (app (app (app C⟨↑⟩ (var var_zero)) (var var_zero)) (rfl (var var_zero))).

(* Both derived types commute with renaming and substitution (Agda
   [ren-motiveTy] / [subst-motiveTy] / [ren-baseTy] / [subst-baseTy]).  Being
   binder-free apart from the [tpi]s, they are pure [asimpl]. *)
Lemma ren_motive_ty {n m} (δ : fin n -> fin m) (A : Tm n) :
  (motive_ty A)⟨δ⟩ = motive_ty (A⟨δ⟩).
Proof. unfold motive_ty. asimpl. reflexivity. Qed.

Lemma subst_motive_ty {n m} (σ : fin n -> Tm m) (A : Tm n) :
  (motive_ty A)[σ] = motive_ty (A[σ]).
Proof. unfold motive_ty. asimpl. reflexivity. Qed.

Lemma ren_base_ty {n m} (δ : fin n -> fin m) (A C : Tm n) :
  (base_ty A C)⟨δ⟩ = base_ty (A⟨δ⟩) (C⟨δ⟩).
Proof. unfold base_ty. asimpl. reflexivity. Qed.

Lemma subst_base_ty {n m} (σ : fin n -> Tm m) (A C : Tm n) :
  (base_ty A C)[σ] = base_ty (A[σ]) (C[σ]).
Proof. unfold base_ty. asimpl. reflexivity. Qed.



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
  (* fixpoints (Agda [ty-Y]): a step function [g : A -> A] has a fixpoint.
     The codomain is [A⟨↑⟩] -- [A] weakened, i.e. no dependency on the
     argument -- so [app g (fix_ g) : A⟨↑⟩[(fix_ g)..] = A]. *)
  | t_fix n (Γ : Ctx n) A g :
    typing Γ A tuniv ->
    typing Γ g (tpi A A⟨↑⟩) ->
    typing Γ (fix_ g) A
  (* identity type (Agda [ty-Id]/[ty-Ref]/[ty-J]) *)
  | t_tid n (Γ : Ctx n) A a b :
    typing Γ A tuniv ->
    typing Γ a A ->
    typing Γ b A ->
    typing Γ (tid A a b) tuniv
  | t_rfl n (Γ : Ctx n) A a :
    typing Γ A tuniv ->
    typing Γ a A ->
    typing Γ (rfl a) (tid A a a)
  (* Martin-Lof's original J, with a fully dependent motive.  The result type
     is binder-free, so no substitution commutation is needed anywhere. *)
  | t_jcase n (Γ : Ctx n) A a b C d p :
    typing Γ A tuniv ->
    typing Γ a A ->
    typing Γ b A ->
    typing Γ C (motive_ty A) ->
    typing Γ d (base_ty A C) ->
    typing Γ p (tid A a b) ->
    typing Γ (jcase C d p) (app (app (app C a) b) p)
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
  (* Y-unfolding (Agda [conv-Y]) and its congruence (Agda [conv-Y-cong]).
     As with [c_abs], the congruence carries typings for both step functions;
     they are admissible (via [conv_typing]) but semantic adequacy needs
     [semantic_typing] of each side. *)
  | c_fix n (Γ : Ctx n) A g :
    typing Γ A tuniv ->
    typing Γ g (tpi A A⟨↑⟩) ->
    conv Γ (fix_ g) (app g (fix_ g)) A
  | c_fix_cong n (Γ : Ctx n) A g g' :
    typing Γ A tuniv ->
    typing Γ g (tpi A A⟨↑⟩) ->
    typing Γ g' (tpi A A⟨↑⟩) ->
    conv Γ g g' (tpi A A⟨↑⟩) ->
    conv Γ (fix_ g) (fix_ g') A
  (* identity type: congruences and the J beta rule (Agda [conv-Id],
     [conv-Ref], [conv-J], [conv-J-beta]).  As with [c_abs] and [c_fix_cong],
     the congruences carry the left-hand sides' typings: they are admissible
     via [conv_typing], but semantic adequacy needs [semantic_typing] of each
     component. *)
  | c_tid n (Γ : Ctx n) A A' a a' b b' :
    typing Γ A tuniv ->
    typing Γ a A ->
    typing Γ b A ->
    conv Γ A A' tuniv ->
    conv Γ a a' A ->
    conv Γ b b' A ->
    conv Γ (tid A a b) (tid A' a' b') tuniv
  | c_rfl n (Γ : Ctx n) A a a' :
    typing Γ A tuniv ->
    typing Γ a A ->
    conv Γ a a' A ->
    conv Γ (rfl a) (rfl a') (tid A a a)
  (* J on the LITERAL diagonal [rfl a0].  Both sides have the *same* type
     [app (app (app C a0) a0) (rfl a0)], so there are no endpoint- or
     motive-equality premises and subject reduction for this rule needs no
     Id-injectivity. *)
  | c_jcase_beta n (Γ : Ctx n) A a0 C d :
    typing Γ A tuniv ->
    typing Γ a0 A ->
    typing Γ C (motive_ty A) ->
    typing Γ d (base_ty A C) ->
    conv Γ (jcase C d (rfl a0)) (app d a0)
           (app (app (app C a0) a0) (rfl a0))
  | c_jcase n (Γ : Ctx n) A a b C C' d d' p p' :
    typing Γ A tuniv ->
    typing Γ a A ->
    typing Γ b A ->
    typing Γ C (motive_ty A) ->
    typing Γ d (base_ty A C) ->
    typing Γ p (tid A a b) ->
    conv Γ C C' (motive_ty A) ->
    conv Γ d d' (base_ty A C) ->
    conv Γ p p' (tid A a b) ->
    conv Γ (jcase C d p) (jcase C' d' p') (app (app (app C a) b) p)
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

(* Weakening commutes with a lifted substitution -- the substitution analogue
   of [ren_up_shift].  Needed for the codomain [A⟨↑⟩] of a fixpoint's step
   function. *)
Lemma subst_up_shift {n m} (σ : fin n -> Tm m) (N : Tm n) :
  (N⟨↑⟩)[⇑ σ] = (N[σ])⟨↑⟩.
Proof. asimpl. done. Qed.

(* Substituting into a weakened term does nothing: the fixpoint's result type
   [A⟨↑⟩[(fix_ g)..]] is just [A]. *)
Lemma subst1_shift {n} (A N : Tm n) : A⟨↑⟩[N..] = A.
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
    + (* t_fix *)
      eapply t_fix.
      * exact (renaming_typing _ _ A tuniv _ _ δ h1 tR wtΔ).
      * rewrite -ren_up_shift.
        move: (renaming_typing _ _ g (tpi A A⟨↑⟩) _ _ δ h2 tR wtΔ) => hh.
        cbn in hh. exact hh.
    + (* t_jcase: the derived motive/base types commute with renaming.
         ([t_tid] and [t_rfl] are discharged by the [econstructor; eauto]
         prelude above -- their types rename structurally.) *)
      (* Each premise is a direct appeal to the mutual IH, with the term and
         type given explicitly: the conclusion does not mention [A], and the
         renamed types are already pushed through the renaming, so
         higher-order unification against [⟨?δ⟩ ?A] would not fire. *)
      eapply t_jcase.
      1: eapply (renaming_typing _ _ A tuniv _ _ δ); eauto.
      1: eapply (renaming_typing _ _ a A _ _ δ); eauto.
      1: eapply (renaming_typing _ _ b A _ _ δ); eauto.
      1: (rewrite -ren_motive_ty;
          eapply (renaming_typing _ _ C (motive_ty A) _ _ δ); eauto).
      1: (rewrite -ren_base_ty;
          eapply (renaming_typing _ _ d (base_ty A C) _ _ δ); eauto).
      1: eapply (renaming_typing _ _ p (tid A a b) _ _ δ); eauto.
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
    + (* c_fix *)
      eapply c_fix.
      * exact (renaming_typing _ _ A tuniv _ _ δ H tR wtΔ).
      * rewrite -ren_up_shift.
        move: (renaming_typing _ _ g (tpi A A⟨↑⟩) _ _ δ H0 tR wtΔ) => hh.
        cbn in hh. exact hh.
    + (* c_fix_cong *)
      eapply c_fix_cong.
      * exact (renaming_typing _ _ A tuniv _ _ δ H tR wtΔ).
      * rewrite -ren_up_shift.
        move: (renaming_typing _ _ g (tpi A A⟨↑⟩) _ _ δ H0 tR wtΔ) => hh.
        cbn in hh. exact hh.
      * rewrite -ren_up_shift.
        move: (renaming_typing _ _ g' (tpi A A⟨↑⟩) _ _ δ H1 tR wtΔ) => hh.
        cbn in hh. exact hh.
      * rewrite -ren_up_shift.
        move: (renaming_conv _ _ g g' (tpi A A⟨↑⟩) _ _ δ h tR wtΔ) => hh.
        cbn in hh. exact hh.
    + (* c_jcase_beta.  ([c_tid] and [c_rfl] are discharged by the
         [econstructor; eauto] prelude.)  The only obstacle is that the derived
         motive/base types must be pushed under the renaming first, which is
         [ren_motive_ty]/[ren_base_ty]; after that every premise is a direct
         appeal to the mutual IH. *)
      eapply c_jcase_beta.
      1: eapply (renaming_typing _ _ A tuniv _ _ δ); eauto.
      1: eapply (renaming_typing _ _ a0 A _ _ δ); eauto.
      1: (rewrite -ren_motive_ty;
          eapply (renaming_typing _ _ C (motive_ty A) _ _ δ); eauto).
      1: (rewrite -ren_base_ty;
          eapply (renaming_typing _ _ d (base_ty A C) _ _ δ); eauto).
    + (* c_jcase, likewise *)
      eapply c_jcase.
      1: eapply (renaming_typing _ _ A tuniv _ _ δ); eauto.
      1: eapply (renaming_typing _ _ a A _ _ δ); eauto.
      1: eapply (renaming_typing _ _ b A _ _ δ); eauto.
      1: (rewrite -ren_motive_ty;
          eapply (renaming_typing _ _ C (motive_ty A) _ _ δ); eauto).
      1: (rewrite -ren_base_ty;
          eapply (renaming_typing _ _ d (base_ty A C) _ _ δ); eauto).
      1: eapply (renaming_typing _ _ p (tid A a b) _ _ δ); eauto.
      1: (rewrite -ren_motive_ty;
          eapply (renaming_conv _ _ C C' (motive_ty A) _ _ δ); eauto).
      1: (rewrite -ren_base_ty;
          eapply (renaming_conv _ _ d d' (base_ty A C) _ _ δ); eauto).
      1: eapply (renaming_conv _ _ p p' (tid A a b) _ _ δ); eauto.
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

(* Weakening a type into an extended context. *)
Lemma typing_weaken_shift {n} (Γ : Ctx n) (A B : Tm n) :
  typing Γ A tuniv -> typing Γ B tuniv -> typing (Γ ++ B) A⟨↑⟩ tuniv.
Proof.
  move=> hA hB.
  have C : ctx (Γ ++ B) by (eapply c_cons; [ eapply typing_ctx; exact hA | exact hB ]).
  move: (renaming_typing Γ A tuniv (Γ ++ B) shift hA
           (typing_renaming_shift Γ B) C) => hh.
  asimpl in hh. exact hh.
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
    + (* t_fix *)
      eapply t_fix.
      * move: (substitution_tm _ _ A tuniv _ _ σ h1 tS tΔ) => hh.
        asimpl in hh. exact hh.
      * rewrite -subst_up_shift.
        move: (substitution_tm _ _ g (tpi A A⟨↑⟩) _ _ σ h2 tS tΔ) => hh.
        cbn in hh. exact hh.
    + (* t_jcase: as in [renaming_typing], with [subst_motive_ty]/[subst_base_ty]
         (and [t_tid]/[t_rfl] discharged by the prelude) *)
      eapply t_jcase.
      1: eapply (substitution_tm _ _ A tuniv _ _ σ); eauto.
      1: eapply (substitution_tm _ _ a A _ _ σ); eauto.
      1: eapply (substitution_tm _ _ b A _ _ σ); eauto.
      1: (rewrite -subst_motive_ty;
          eapply (substitution_tm _ _ C (motive_ty A) _ _ σ); eauto).
      1: (rewrite -subst_base_ty;
          eapply (substitution_tm _ _ d (base_ty A C) _ _ σ); eauto).
      1: eapply (substitution_tm _ _ p (tid A a b) _ _ σ); eauto.
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

    + (* c_fix *)
      cbn. eapply c_fix.
      * move: (substitution_tm _ _ A tuniv _ _ σ H tS tΔ) => hh.
        asimpl in hh. exact hh.
      * rewrite -subst_up_shift.
        move: (substitution_tm _ _ g (tpi A A⟨↑⟩) _ _ σ H0 tS tΔ) => hh.
        cbn in hh. exact hh.
    + (* c_fix_cong *)
      cbn. eapply c_fix_cong.
      * move: (substitution_tm _ _ A tuniv _ _ σ H tS tΔ) => hh.
        asimpl in hh. exact hh.
      * rewrite -subst_up_shift.
        move: (substitution_tm _ _ g (tpi A A⟨↑⟩) _ _ σ H0 tS tΔ) => hh.
        cbn in hh. exact hh.
      * rewrite -subst_up_shift.
        move: (substitution_tm _ _ g' (tpi A A⟨↑⟩) _ _ σ H1 tS tΔ) => hh.
        cbn in hh. exact hh.
      * rewrite -subst_up_shift.
        move: (substitution_conv _ _ g g' (tpi A A⟨↑⟩) _ _ σ h tS tΔ) => hh.
        cbn in hh. exact hh.
    + (* c_tid *)
      cbn. eapply c_tid.
      1: eapply (substitution_tm _ _ A tuniv _ _ σ); eauto.
      1: eapply (substitution_tm _ _ a A _ _ σ); eauto.
      1: eapply (substitution_tm _ _ b A _ _ σ); eauto.
      1: eapply (substitution_conv _ _ A A' tuniv _ _ σ); eauto.
      1: eapply (substitution_conv _ _ a a' A _ _ σ); eauto.
      1: eapply (substitution_conv _ _ b b' A _ _ σ); eauto.
    + (* c_rfl *)
      cbn. eapply c_rfl.
      1: eapply (substitution_tm _ _ A tuniv _ _ σ); eauto.
      1: eapply (substitution_tm _ _ a A _ _ σ); eauto.
      1: eapply (substitution_conv _ _ a a' A _ _ σ); eauto.
    + (* c_jcase_beta *)
      cbn. eapply c_jcase_beta.
      1: eapply (substitution_tm _ _ A tuniv _ _ σ); eauto.
      1: eapply (substitution_tm _ _ a0 A _ _ σ); eauto.
      1: (rewrite -subst_motive_ty;
          eapply (substitution_tm _ _ C (motive_ty A) _ _ σ); eauto).
      1: (rewrite -subst_base_ty;
          eapply (substitution_tm _ _ d (base_ty A C) _ _ σ); eauto).
    + (* c_jcase *)
      cbn. eapply c_jcase.
      1: eapply (substitution_tm _ _ A tuniv _ _ σ); eauto.
      1: eapply (substitution_tm _ _ a A _ _ σ); eauto.
      1: eapply (substitution_tm _ _ b A _ _ σ); eauto.
      1: (rewrite -subst_motive_ty;
          eapply (substitution_tm _ _ C (motive_ty A) _ _ σ); eauto).
      1: (rewrite -subst_base_ty;
          eapply (substitution_tm _ _ d (base_ty A C) _ _ σ); eauto).
      1: eapply (substitution_tm _ _ p (tid A a b) _ _ σ); eauto.
      1: (rewrite -subst_motive_ty;
          eapply (substitution_conv _ _ C C' (motive_ty A) _ _ σ); eauto).
      1: (rewrite -subst_base_ty;
          eapply (substitution_conv _ _ d d' (base_ty A C) _ _ σ); eauto).
      1: eapply (substitution_conv _ _ p p' (tid A a b) _ _ σ); eauto.

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
(* =====================================================================
   The types of the based-J eliminator.

   [jcase C d p] has the binder-free type [app (app (app C a) b) p], so the
   only real work is showing that this application *is* a type -- i.e. that
   the motive, applied to the two endpoints and the proof, lands in [tuniv].
   That is [motive_app_typing] below; [base_app_typing] is its instance at the
   diagonal, and is exactly the second side of [c_jcase_beta].
   ===================================================================== *)

Lemma typing_weaken1 {n} (Γ : Ctx n) (M A B : Tm n) :
  typing Γ M A -> typing Γ B tuniv -> typing (Γ ++ B) M⟨↑⟩ A⟨↑⟩.
Proof.
  move=> hM hB.
  have C : ctx (Γ ++ B) by (eapply c_cons; [ eapply typing_ctx; exact hM | exact hB ]).
  exact (renaming_typing Γ M A (Γ ++ B) shift hM (typing_renaming_shift Γ B) C).
Qed.

(* the innermost identity type of [motive_ty] *)
Lemma motive_id_typing {n} (Γ : Ctx n) (A : Tm n) :
  typing Γ A tuniv ->
  typing ((Γ ++ A) ++ A⟨↑⟩)
    (tid A⟨↑⟩⟨↑⟩ (var (shift var_zero)) (var var_zero)) tuniv.
Proof.
  move=> TA.
  have cG : ctx Γ by (eapply typing_ctx; exact TA).
  have cA : ctx (Γ ++ A) by (eapply c_cons; [ exact cG | exact TA ]).
  have TA1 : typing (Γ ++ A) A⟨↑⟩ tuniv by (eapply typing_weaken_shift; exact TA).
  have cA1 : ctx ((Γ ++ A) ++ A⟨↑⟩) by (eapply c_cons; [ exact cA | exact TA1 ]).
  have TA2 : typing ((Γ ++ A) ++ A⟨↑⟩) A⟨↑⟩⟨↑⟩ tuniv
    by (eapply typing_weaken_shift; exact TA1).
  eapply t_tid; [ exact TA2 | | ].
  - eapply t_var'; [ reflexivity | exact cA1 ].
  - eapply t_var'; [ reflexivity | exact cA1 ].
Qed.

(* the first and second codomains of [motive_ty], as types *)
Lemma motive_cod1_typing {n} (Γ : Ctx n) (A : Tm n) :
  typing Γ A tuniv ->
  typing (Γ ++ A)
    (tpi A⟨↑⟩ (tpi (tid A⟨↑⟩⟨↑⟩ (var (shift var_zero)) (var var_zero)) tuniv))
    tuniv.
Proof.
  move=> TA.
  have cG : ctx Γ by (eapply typing_ctx; exact TA).
  have cA : ctx (Γ ++ A) by (eapply c_cons; [ exact cG | exact TA ]).
  have TA1 : typing (Γ ++ A) A⟨↑⟩ tuniv by (eapply typing_weaken_shift; exact TA).
  have TId := motive_id_typing Γ A TA.
  eapply t_tpi; [ exact TA1 | ].
  eapply t_tpi; [ exact TId | ].
  apply t_univ. eapply c_cons; [ eapply c_cons; [ exact cA | exact TA1 ] | exact TId ].
Qed.

Lemma motive_cod2_typing {n} (Γ : Ctx n) (A a : Tm n) :
  typing Γ A tuniv -> typing Γ a A ->
  typing (Γ ++ A) (tpi (tid A⟨↑⟩ a⟨↑⟩ (var var_zero)) tuniv) tuniv.
Proof.
  move=> TA Ta.
  have cG : ctx Γ by (eapply typing_ctx; exact TA).
  have cA : ctx (Γ ++ A) by (eapply c_cons; [ exact cG | exact TA ]).
  have TA1 : typing (Γ ++ A) A⟨↑⟩ tuniv by (eapply typing_weaken_shift; exact TA).
  have Ta1 : typing (Γ ++ A) a⟨↑⟩ A⟨↑⟩ by (eapply typing_weaken1; [ exact Ta | exact TA ]).
  have Tv : typing (Γ ++ A) (var var_zero) A⟨↑⟩
    by (eapply t_var'; [ reflexivity | exact cA ]).
  have TId : typing (Γ ++ A) (tid A⟨↑⟩ a⟨↑⟩ (var var_zero)) tuniv

    by (eapply t_tid; [ exact TA1 | exact Ta1 | exact Tv ]).
  eapply t_tpi; [ exact TId | ].
  apply t_univ. eapply c_cons; [ exact cA | exact TId ].
Qed.

Lemma motive_ty_typing {n} (Γ : Ctx n) (A : Tm n) :
  typing Γ A tuniv -> typing Γ (motive_ty A) tuniv.
Proof.
  move=> TA. unfold motive_ty.
  eapply t_tpi; [ exact TA | (eapply motive_cod1_typing; exact TA) ].
Qed.

(* the motive applied to one and two arguments *)
Lemma motive_app1_typing {n} (Γ : Ctx n) (A a C : Tm n) :
  typing Γ A tuniv -> typing Γ a A -> typing Γ C (motive_ty A) ->
  typing Γ (app C a) (tpi A (tpi (tid A⟨↑⟩ a⟨↑⟩ (var var_zero)) tuniv)).
Proof.
  move=> TA Ta TC.
  eapply t_app';
    [ exact TA | (eapply motive_cod1_typing; exact TA) | exact TC | exact Ta | ].
  asimpl. substify. asimpl. reflexivity.
Qed.

Lemma motive_app2_typing {n} (Γ : Ctx n) (A a b C : Tm n) :
  typing Γ A tuniv -> typing Γ a A -> typing Γ b A ->
  typing Γ C (motive_ty A) ->
  typing Γ (app (app C a) b) (tpi (tid A a b) tuniv).
Proof.
  move=> TA Ta Tb TC.
  eapply t_app';
    [ exact TA | (eapply motive_cod2_typing; [ exact TA | exact Ta ])
    | (eapply motive_app1_typing; [ exact TA | exact Ta | exact TC ]) | exact Tb
    | (asimpl; substify; asimpl; reflexivity) ].
Qed.

(* ... and to all three, which is the type of [jcase C d p]. *)
Lemma motive_app_typing {n} (Γ : Ctx n) (A a b C p : Tm n) :
  typing Γ A tuniv -> typing Γ a A -> typing Γ b A ->
  typing Γ C (motive_ty A) -> typing Γ p (tid A a b) ->
  typing Γ (app (app (app C a) b) p) tuniv.
Proof.
  move=> TA Ta Tb TC Tp.
  have TId : typing Γ (tid A a b) tuniv by (eapply t_tid; [ exact TA | exact Ta | exact Tb ]).
  eapply t_app';
    [ exact TId
    | apply t_univ; eapply c_cons; [ eapply typing_ctx; exact TA | exact TId ]
    | (eapply motive_app2_typing; [ exact TA | exact Ta | exact Tb | exact TC ]) | exact Tp
    | (asimpl; substify; asimpl; reflexivity) ].
Qed.

(* The second side of [c_jcase_beta]: the base applied to the diagonal
   witness has exactly the type that [jcase C d (rfl a)] has. *)
Lemma base_app_typing {n} (Γ : Ctx n) (A a C d : Tm n) :
  typing Γ A tuniv -> typing Γ a A ->
  typing Γ C (motive_ty A) -> typing Γ d (base_ty A C) ->
  typing Γ (app d a) (app (app (app C a) a) (rfl a)).
Proof.
  move=> TA Ta TC Td.
  have cG : ctx Γ by (eapply typing_ctx; exact TA).
  have cA : ctx (Γ ++ A) by (eapply c_cons; [ exact cG | exact TA ]).
  have TA1 : typing (Γ ++ A) A⟨↑⟩ tuniv by (eapply typing_weaken_shift; exact TA).
  have Tv : typing (Γ ++ A) (var var_zero) A⟨↑⟩
    by (eapply t_var'; [ reflexivity | exact cA ]).
  have TC1 : typing (Γ ++ A) C⟨↑⟩ (motive_ty A⟨↑⟩).
  { move: (typing_weaken1 Γ C (motive_ty A) A TC TA) => hh.
    rewrite ren_motive_ty in hh. exact hh. }
  have TR : typing (Γ ++ A) (rfl (var var_zero)) (tid A⟨↑⟩ (var var_zero) (var var_zero))

    by (eapply t_rfl; [ exact TA1 | exact Tv ]).
  eapply t_app';
    [ exact TA
    | (eapply motive_app_typing; [ exact TA1 | exact Tv | exact Tv | exact TC1 | exact TR ])
    | exact Td | exact Ta | (asimpl; substify; asimpl; reflexivity) ].
Qed.

(* Congruence of the [jcase] result type, for the second side of [c_jcase]. *)
Lemma motive_app_conv {n} (Γ : Ctx n) (A a b C C' p p' : Tm n) :
  typing Γ A tuniv -> typing Γ a A -> typing Γ b A ->
  typing Γ C (motive_ty A) -> typing Γ C' (motive_ty A) ->
  typing Γ p (tid A a b) ->
  conv Γ C C' (motive_ty A) -> conv Γ p p' (tid A a b) ->
  conv Γ (app (app (app C a) b) p) (app (app (app C' a) b) p') tuniv.
Proof.
  move=> TA Ta Tb TC TC' Tp CC Cp.
  have TId : typing Γ (tid A a b) tuniv by (eapply t_tid; [ exact TA | exact Ta | exact Tb ]).
  have cId : ctx (Γ ++ tid A a b)
    by (eapply c_cons; [ eapply typing_ctx; exact TA | exact TId ]).
  have TU : typing (Γ ++ tid A a b) tuniv tuniv by (apply t_univ; exact cId).
  have C1 : conv Γ (app C a) (app C' a)
              (tpi A (tpi (tid A⟨↑⟩ a⟨↑⟩ (var var_zero)) tuniv)).
  { eapply c_app1';
      [ exact TA | (eapply motive_cod1_typing; exact TA) | exact CC | exact Ta
      | (asimpl; substify; asimpl; reflexivity) ]. }
  have C2 : conv Γ (app (app C a) b) (app (app C' a) b) (tpi (tid A a b) tuniv).
  { eapply c_app1';
      [ exact TA | (eapply motive_cod2_typing; [ exact TA | exact Ta ]) | exact C1 | exact Tb
      | (asimpl; substify; asimpl; reflexivity) ]. }
  have C3 : conv Γ (app (app (app C a) b) p) (app (app (app C' a) b) p) tuniv.
  { eapply c_app1'; [ exact TId | exact TU | exact C2 | exact Tp | reflexivity ]. }
  have C4 : conv Γ (app (app (app C' a) b) p) (app (app (app C' a) b) p') tuniv.
  { eapply c_app2';
      [ exact TId | exact TU | (eapply motive_app2_typing; [ exact TA | exact Ta | exact Tb | exact TC' ])
      | exact Cp | reflexivity ]. }
  eapply c_trans; [ exact C3 | exact C4 ].
Qed.

Lemma conv_weaken1 {n} (Γ : Ctx n) (M N A B : Tm n) :
  conv Γ M N A -> typing Γ B tuniv -> conv (Γ ++ B) M⟨↑⟩ N⟨↑⟩ A⟨↑⟩.
Proof.
  move=> hM hB.
  have C : ctx (Γ ++ B) by (eapply c_cons; [ eapply conv_ctx; exact hM | exact hB ]).
  exact (renaming_conv Γ M N A (Γ ++ B) shift hM (typing_renaming_shift Γ B) C).
Qed.

(* [base_ty A C] is a type, and is a congruence in the motive.  The latter is
   what retypes the primed base of [c_jcase]: its premise gives
   [d' : base_ty A C], while [t_jcase] on the primed side wants
   [d' : base_ty A C']. *)
Lemma base_ty_typing {n} (Γ : Ctx n) (A C : Tm n) :
  typing Γ A tuniv -> typing Γ C (motive_ty A) ->
  typing Γ (base_ty A C) tuniv.
Proof.
  move=> TA TC. unfold base_ty.
  have cG : ctx Γ by (eapply typing_ctx; exact TA).
  have cA : ctx (Γ ++ A) by (eapply c_cons; [ exact cG | exact TA ]).
  have TA1 : typing (Γ ++ A) A⟨↑⟩ tuniv by (eapply typing_weaken_shift; exact TA).
  have Tv : typing (Γ ++ A) (var var_zero) A⟨↑⟩
    by (eapply t_var'; [ reflexivity | exact cA ]).
  have TC1 : typing (Γ ++ A) C⟨↑⟩ (motive_ty A⟨↑⟩).
  { move: (typing_weaken1 Γ C (motive_ty A) A TC TA) => hh.
    rewrite ren_motive_ty in hh. exact hh. }
  have TR : typing (Γ ++ A) (rfl (var var_zero)) (tid A⟨↑⟩ (var var_zero) (var var_zero))
    by (eapply t_rfl; [ exact TA1 | exact Tv ]).
  eapply t_tpi;
    [ exact TA
    | eapply motive_app_typing;
        [ exact TA1 | exact Tv | exact Tv | exact TC1 | exact TR ] ].
Qed.

Lemma base_ty_conv {n} (Γ : Ctx n) (A C C' : Tm n) :
  typing Γ A tuniv -> typing Γ C (motive_ty A) -> typing Γ C' (motive_ty A) ->
  conv Γ C C' (motive_ty A) ->
  conv Γ (base_ty A C) (base_ty A C') tuniv.
Proof.
  move=> TA TC TC' CC. unfold base_ty.
  have cG : ctx Γ by (eapply typing_ctx; exact TA).
  have cA : ctx (Γ ++ A) by (eapply c_cons; [ exact cG | exact TA ]).
  have TA1 : typing (Γ ++ A) A⟨↑⟩ tuniv by (eapply typing_weaken_shift; exact TA).
  have Tv : typing (Γ ++ A) (var var_zero) A⟨↑⟩
    by (eapply t_var'; [ reflexivity | exact cA ]).
  have TR : typing (Γ ++ A) (rfl (var var_zero)) (tid A⟨↑⟩ (var var_zero) (var var_zero))
    by (eapply t_rfl; [ exact TA1 | exact Tv ]).
  have TC1 : typing (Γ ++ A) C⟨↑⟩ (motive_ty A⟨↑⟩).
  { move: (typing_weaken1 Γ C (motive_ty A) A TC TA) => hh.
    rewrite ren_motive_ty in hh. exact hh. }
  have TC1' : typing (Γ ++ A) C'⟨↑⟩ (motive_ty A⟨↑⟩).
  { move: (typing_weaken1 Γ C' (motive_ty A) A TC' TA) => hh.
    rewrite ren_motive_ty in hh. exact hh. }
  have CC1 : conv (Γ ++ A) C⟨↑⟩ C'⟨↑⟩ (motive_ty A⟨↑⟩).
  { move: (conv_weaken1 Γ C C' (motive_ty A) A CC TA) => hh.
    rewrite ren_motive_ty in hh. exact hh. }
  eapply c_tpi;
    [ exact TA | exact TA
    | eapply motive_app_typing;
        [ exact TA1 | exact Tv | exact Tv | exact TC1 | exact TR ]
    | eapply motive_app_typing;
        [ exact TA1 | exact Tv | exact Tv | exact TC1' | exact TR ]
    | apply c_refl; exact TA
    | eapply motive_app_conv;
        [ exact TA1 | exact Tv | exact Tv | exact TC1 | exact TC1' | exact TR
        | exact CC1 | apply c_refl; exact TR ] ].
Qed.

(* Congruence of the [jcase] result type in the *endpoint arguments*.  Needed
   because a J-beta redex [jcase C d (rfl a0)] is typed by the derivation at
   [app (app (app C a) b) (rfl a0)] while [c_jcase_beta] states the
   contraction at [app (app (app C a0) a0) (rfl a0)]. *)
Lemma motive_app_conv_args {n} (Γ : Ctx n) (A a a' b b' C p : Tm n) :
  typing Γ A tuniv ->
  typing Γ a A -> typing Γ a' A -> typing Γ b A -> typing Γ b' A ->
  typing Γ C (motive_ty A) -> typing Γ p (tid A a b) ->
  conv Γ a a' A -> conv Γ b b' A ->
  conv Γ (app (app (app C a) b) p) (app (app (app C a') b') p) tuniv.
Proof.
  move=> TA Ta Ta' Tb Tb' TC Tp Caa Cbb.
  have cG : ctx Γ by (eapply typing_ctx; exact TA).
  have TIdab : typing Γ (tid A a b) tuniv by (eapply t_tid; [ exact TA | exact Ta | exact Tb ]).
  have TIda'b : typing Γ (tid A a' b) tuniv by (eapply t_tid; [ exact TA | exact Ta' | exact Tb ]).
  have cIdab : ctx (Γ ++ tid A a b) by (eapply c_cons; [ exact cG | exact TIdab ]).
  have cIda'b : ctx (Γ ++ tid A a' b) by (eapply c_cons; [ exact cG | exact TIda'b ]).
  (* the motive, applied to the first argument *)
  have C1 : conv Γ (app C a) (app C a')
              (tpi A (tpi (tid A⟨↑⟩ a⟨↑⟩ (var var_zero)) tuniv)).
  { eapply c_app2';
      [ exact TA | (eapply motive_cod1_typing; exact TA) | exact TC | exact Caa
      | (asimpl; substify; asimpl; reflexivity) ]. }
  (* ... and to the second *)
  have C2 : conv Γ (app (app C a) b) (app (app C a') b) (tpi (tid A a b) tuniv).
  { eapply c_app1';
      [ exact TA | (eapply motive_cod2_typing; [ exact TA | exact Ta ])
      | exact C1 | exact Tb | (asimpl; substify; asimpl; reflexivity) ]. }
  have C3 : conv Γ (app (app C a') b) (app (app C a') b') (tpi (tid A a' b) tuniv).
  { eapply c_app2';
      [ exact TA | (eapply motive_cod2_typing; [ exact TA | exact Ta' ])
      | (eapply motive_app1_typing; [ exact TA | exact Ta' | exact TC ])
      | exact Cbb | (asimpl; substify; asimpl; reflexivity) ]. }
  (* [C2] and [C3] sit at different codomains; align [C3] along the [tid]
     congruence in the first endpoint *)
  have CAlign : conv Γ (tpi (tid A a' b) tuniv) (tpi (tid A a b) tuniv) tuniv.
  { eapply c_tpi;
      [ exact TIda'b | exact TIdab
      | apply t_univ; exact cIda'b | apply t_univ; exact cIdab
      | eapply c_tid;
          [ exact TA | exact Ta' | exact Tb | apply c_refl; exact TA
          | apply c_sym; exact Caa | apply c_refl; exact Tb ]
      | apply c_refl; apply t_univ; exact cIda'b ]. }
  have C3' : conv Γ (app (app C a') b) (app (app C a') b') (tpi (tid A a b) tuniv)
    by (eapply c_conv; [ exact C3 | exact CAlign ]).
  have C4 : conv Γ (app (app C a) b) (app (app C a') b') (tpi (tid A a b) tuniv)
    by (eapply c_trans; [ exact C2 | exact C3' ]).
  eapply c_app1';
    [ exact TIdab | apply t_univ; exact cIdab | exact C4 | exact Tp | reflexivity ].
Qed.

(* The [motive_ty] spine's types, level by level.  [spine_Val] and friends hand
   back [B0[N..]] for the [B0] read off the head-reduced Π-type, so the adequacy
   driver needs these normal forms by name. *)
Lemma motive_cod1_subst {n} (A a : Tm n) :
  (tpi A⟨↑⟩ (tpi (tid A⟨↑⟩⟨↑⟩ (var (shift var_zero)) (var var_zero)) tuniv))[a..]
  = tpi A (tpi (tid A⟨↑⟩ a⟨↑⟩ (var var_zero)) tuniv).
Proof. asimpl. substify. asimpl. reflexivity. Qed.

Lemma motive_cod2_subst {n} (A a b : Tm n) :
  (tpi (tid A⟨↑⟩ a⟨↑⟩ (var var_zero)) tuniv)[b..] = tpi (tid A a b) tuniv.
Proof. asimpl. reflexivity. Qed.

Lemma motive_cod3_subst {n} (p : Tm n) :
  (tuniv : Tm (S n))[p..] = tuniv.
Proof. reflexivity. Qed.

(* The spine types are congruent in their instantiating arguments.  This is the
   syntactic half of the per-level type transports in the [J] driver's motive
   walk: the walk's left side instantiates the motive at the witness and its
   right side at the endpoints, so the two sides' *types* drift apart level by
   level and have to be reconciled by [EqVal_EqVal_fwd], which wants both a
   [conv] (these lemmas) and an [EqValTy] (the [PiEdgeEqTy] component of the
   level above). *)
Lemma motive_cod2_inst_conv {n} (Γ : Ctx n) (A a a' b : Tm n) :
  typing Γ A tuniv -> typing Γ a A -> typing Γ a' A -> typing Γ b A ->
  conv Γ a a' A ->
  conv Γ (tpi (tid A a b) tuniv) (tpi (tid A a' b) tuniv) tuniv.
Proof.
  move=> TA Ta Ta' Tb ca.
  have cG : ctx Γ by (eapply typing_ctx; exact TA).
  have TId : typing Γ (tid A a b) tuniv
    by (eapply t_tid; [ exact TA | exact Ta | exact Tb ]).
  have TId' : typing Γ (tid A a' b) tuniv
    by (eapply t_tid; [ exact TA | exact Ta' | exact Tb ]).
  have cI : ctx (Γ ++ tid A a b) by (eapply c_cons; [ exact cG | exact TId ]).
  have cI' : ctx (Γ ++ tid A a' b) by (eapply c_cons; [ exact cG | exact TId' ]).
  eapply c_tpi;
    [ exact TId | exact TId'
    | (apply t_univ; exact cI) | (apply t_univ; exact cI')
    | (eapply c_tid;
       [ exact TA | exact Ta | exact Tb | apply c_refl; exact TA
       | exact ca | apply c_refl; exact Tb ])
    | (apply c_refl; apply t_univ; exact cI) ].
Qed.

Lemma motive_cod1_inst_conv {n} (Γ : Ctx n) (A a a' : Tm n) :
  typing Γ A tuniv -> typing Γ a A -> typing Γ a' A -> conv Γ a a' A ->
  conv Γ (tpi A (tpi (tid A⟨↑⟩ a⟨↑⟩ (var var_zero)) tuniv))
         (tpi A (tpi (tid A⟨↑⟩ a'⟨↑⟩ (var var_zero)) tuniv)) tuniv.
Proof.
  move=> TA Ta Ta' ca.
  have cG : ctx Γ by (eapply typing_ctx; exact TA).
  have cA : ctx (Γ ++ A) by (eapply c_cons; [ exact cG | exact TA ]).
  have TA1 : typing (Γ ++ A) A⟨↑⟩ tuniv
    by (eapply typing_weaken_shift; [ exact TA | exact TA ]).
  have Tv : typing (Γ ++ A) (var var_zero) A⟨↑⟩
    by (eapply t_var'; [ reflexivity | exact cA ]).
  have Ta1 : typing (Γ ++ A) a⟨↑⟩ A⟨↑⟩
    by (eapply typing_weaken1; [ exact Ta | exact TA ]).
  have Ta1' : typing (Γ ++ A) a'⟨↑⟩ A⟨↑⟩
    by (eapply typing_weaken1; [ exact Ta' | exact TA ]).
  have ca1 : conv (Γ ++ A) a⟨↑⟩ a'⟨↑⟩ A⟨↑⟩
    by (eapply conv_weaken1; [ exact ca | exact TA ]).
  eapply c_tpi;
    [ exact TA | exact TA
    | (eapply motive_cod2_typing; [ exact TA | exact Ta ])
    | (eapply motive_cod2_typing; [ exact TA | exact Ta' ])
    | (apply c_refl; exact TA)
    | (eapply motive_cod2_inst_conv;
       [ exact TA1 | exact Ta1 | exact Ta1' | exact Tv | exact ca1 ]) ].
Qed.

(* ------------------------------------------------------------------
   Driving [jcase] to its base branch.

   These three are the *syntactic* half of the adequacy driver for [J].  The
   semantic driver learns from the logical relation that the proof [p] reduces
   to some [rfl P0] whose witness [P0] is convertible to **both** endpoints
   (Coquand's membership rule read off [ValId]).  Given that, [jcase C d p]
   converts to [app d P0], and the diagonal type the [c_jcase_beta] rule
   produces converts to the goal type -- so no Id-injectivity is needed here
   beyond the two endpoint conversions the relation already stores.
   ------------------------------------------------------------------ *)

(* Coquand's rule as a retyping: a witness below both endpoints inhabits the
   *off-diagonal* identity type. *)
Lemma rfl_offdiag_typing {n} (Γ : Ctx n) (A P0 a b : Tm n) :
  typing Γ A tuniv -> typing Γ P0 A -> typing Γ a A -> typing Γ b A ->
  conv Γ P0 a A -> conv Γ P0 b A ->
  typing Γ (rfl P0) (tid A a b).
Proof.
  move=> TA TP Ta Tb ca cb.
  eapply t_conv; [ eapply t_rfl; [ exact TA | exact TP ] | ].
  eapply c_tid;
    [ exact TA | exact TP | exact TP | apply c_refl; exact TA | exact ca | exact cb ].
Qed.

(* [c_jcase_beta]'s diagonal type converts to the goal's type. *)
Lemma motive_app_conv_witness {n} (Γ : Ctx n) (A P0 a b C p : Tm n) :
  typing Γ A tuniv -> typing Γ P0 A -> typing Γ a A -> typing Γ b A ->
  typing Γ C (motive_ty A) -> typing Γ p (tid A a b) ->
  conv Γ P0 a A -> conv Γ P0 b A ->
  conv Γ p (rfl P0) (tid A a b) ->
  conv Γ (app (app (app C P0) P0) (rfl P0)) (app (app (app C a) b) p) tuniv.
Proof.
  move=> TA TP Ta Tb TC Tp ca cb cp.
  have TRd : typing Γ (rfl P0) (tid A P0 P0)
    by (eapply t_rfl; [ exact TA | exact TP ]).
  have TRo : typing Γ (rfl P0) (tid A a b)
    by (eapply rfl_offdiag_typing;
        [ exact TA | exact TP | exact Ta | exact Tb | exact ca | exact cb ]).
  eapply c_trans.
  - (* move the two endpoint arguments *)
    eapply motive_app_conv_args;
      [ exact TA | exact TP | exact Ta | exact TP | exact Tb | exact TC | exact TRd
      | exact ca | exact cb ].
  - (* ... then the proof argument *)
    eapply motive_app_conv;
      [ exact TA | exact Ta | exact Tb | exact TC | exact TC | exact TRo
      | apply c_refl; exact TC | apply c_sym; exact cp ].
Qed.

(* The driver conversion: [jcase C d p] converts to the base branch applied to
   the witness, *at the goal's type*.  This is the [conv] side of the
   [Val_beta_expand] / [EqVal_headred_expand] appeal in [st_jcase]/[sc_jcase];
   the [HeadRed] side is [reduction.HeadRed_jcase]. *)
Lemma jcase_drive_conv {n} (Γ : Ctx n) (A P0 a b C d p : Tm n) :
  typing Γ A tuniv -> typing Γ P0 A -> typing Γ a A -> typing Γ b A ->
  typing Γ C (motive_ty A) -> typing Γ d (base_ty A C) ->
  typing Γ p (tid A a b) ->
  conv Γ P0 a A -> conv Γ P0 b A ->
  conv Γ p (rfl P0) (tid A a b) ->
  conv Γ (jcase C d p) (app d P0) (app (app (app C a) b) p).
Proof.
  move=> TA TP Ta Tb TC Td Tp ca cb cp.
  eapply c_trans.
  - (* the scrutinee converts to a literal [rfl] *)
    eapply c_jcase;
      [ exact TA | exact Ta | exact Tb | exact TC | exact Td | exact Tp
      | apply c_refl; exact TC | apply c_refl; exact Td | exact cp ].
  - (* ... which contracts, and the diagonal type it lands at converts back *)
    eapply c_conv.
    + eapply c_jcase_beta; [ exact TA | exact TP | exact TC | exact Td ].
    + eapply motive_app_conv_witness;
        [ exact TA | exact TP | exact Ta | exact Tb | exact TC | exact Tp
        | exact ca | exact cb | exact cp ].
Qed.

Lemma conv_typing {n} {Γ : Ctx n} {M N A : Tm n} :
  Γ ⊢e M ≡ N ∈ A -> Γ ⊢e M ∈ A /\ Γ ⊢e N ∈ A.
Proof.
  induction 1;
    repeat match goal with [ H : _ /\ _ |- _ ] => destruct H end;
    split; eauto using t_conv, t_app, t_succ, t_tpi, t_abs, t_fix,
                       t_tid, t_rfl, t_jcase.
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
  - (* c_fix, second side: [app g (fix_ g) : A], using [A⟨↑⟩[(fix_ g)..] = A] *)
    have hfix : typing Γ (fix_ g) A by (eapply t_fix; eassumption).
    eapply t_app' with (A := A) (B := A⟨↑⟩);
      [ eassumption
      | apply typing_weaken_shift; eassumption
      | eassumption
      | exact hfix
      | apply subst1_shift ].
  - (* c_rfl, second side: [rfl a' : tid A a a].  [t_rfl] types it at
       [tid A a' a'], so retype along the [tid] congruence. *)
    eapply t_conv;
      [ eapply t_rfl; eauto
      | apply c_sym; eapply c_tid; eauto using c_refl ].
  - (* c_jcase_beta, second side: exactly [base_app_typing] *)
    eapply (@base_app_typing _ Γ A a0 C d); eauto.
  - (* c_jcase, second side: [t_jcase] on the primed components types
       [jcase C' d' p'] at the *primed* result type, so retype it along the
       congruence [motive_app_conv].  The primed base needs retyping too:
       the premise gives [d' : base_ty A C], [t_jcase] wants
       [d' : base_ty A C']. *)
    have Td' : typing Γ d' (base_ty A C')
      by (eapply t_conv; [ eauto | eapply base_ty_conv; eauto ]).
    eapply t_conv;
      [ eapply (@t_jcase _ Γ A a b C' d' p'); eauto
      | apply c_sym; eapply (@motive_app_conv _ Γ A a b C C' p p'); eauto ].
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

(* Typing inversions for the identity fragment, on the model of
   [typing_univ_inv] / [typing_abs_inv]. *)
Lemma typing_tid_inv {n} {Γ : Ctx n} {A a b T} :
  Γ ⊢e tid A a b ∈ T -> Γ ⊢e tuniv ≡ T ∈ tuniv.
Proof.
  move=> h; dependent induction h.
  - eapply c_trans; [ first [ eapply IHh; reflexivity | exact IHh ] | eassumption ].
  - apply c_refl; apply t_univ; eapply typing_ctx; eassumption.
Qed.

Lemma typing_rfl_inv {n} {Γ : Ctx n} {a T} :
  Γ ⊢e rfl a ∈ T -> exists A, Γ ⊢e a ∈ A /\ Γ ⊢e tid A a a ≡ T ∈ tuniv.
Proof.
  move=> h; dependent induction h.
  - move: (IHh a ltac:(reflexivity)) => [A0 [ta cc]].
    exists A0. split; [ exact ta | ]. eapply c_trans; [ exact cc | eassumption ].
  - exists A. split; [ eassumption | ]. apply c_refl. eapply t_tid; eauto.
Qed.

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


