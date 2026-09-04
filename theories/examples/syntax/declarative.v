Require Import ssreflect.

From Stdlib Require Export Logic.FunctionalExtensionality.
From Stdlib Require Import Program.Equality.

Require Export autosubst.core.
Require Export autosubst.fintype.
Require Import syntax.syntax.
Require Import syntax.typing.

Import SyntaxNotations.
Import typing.Notations.
Open Scope syntax_scope.

Inductive typing : forall {n} (Γ : Ctx n), Tm n -> Tm n -> Prop := 

  | t_var n (Γ : Ctx n) x : 
    typing Γ (var x) (lookup x Γ)

  | t_conv n (Γ : Ctx n) M A B : 
    typing Γ M A -> 
    conv Γ A B tuniv -> 
    typing Γ M B

  | t_abs n (Γ : Ctx n) A B N : 
    typing Γ A tuniv ->
    typing (ctx_extend Γ A) N B ->
    typing Γ (abs A N) (tpi A B)

  | t_app n (Γ : Ctx n) A B N M : 
    typing Γ N (tpi A B) ->
    typing Γ M A -> 
    typing Γ (app N M) B[M..]

  | t_nat n (Γ : Ctx n) : 
    typing Γ tnat tuniv

  | t_zero n (Γ : Ctx n) : 
    typing Γ zero tnat 

  | t_succ n (Γ : Ctx n) M : 
    typing Γ M tnat ->
    typing Γ (succ M) tnat 

  | t_tpi n (Γ : Ctx n) A B : 
    typing Γ A tuniv ->
    typing (Γ ++ A) B tuniv -> 
    typing Γ (tpi A B) tuniv

  | t_univ n (Γ : Ctx n) : 
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

  | c_app n (Γ : Ctx n) A B N N' M : 
    conv Γ M M' (tpi A B) ->
    conv Γ N N' A ->
    conv Γ (app M N) (app M N') B[M..]

  | c_beta n (Γ : Ctx n) A B M N :
    typing Γ (abs A N) (tpi A B) -> 
    typing Γ M A ->
    conv Γ (app (abs A N) M) N[M..] B[M..]

  | c_eta n (Γ : Ctx n) A B N N' :
    typing Γ N (tpi A B) ->
    typing Γ N' (tpi A B) ->
    conv (Γ ++ A) 
           (app N⟨↑⟩  (var var_zero))
           (app N'⟨↑⟩ (var var_zero)) B ->
    conv Γ N N' (tpi A B)

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
