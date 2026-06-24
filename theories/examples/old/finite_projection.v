(* Finitary projection *)
(* cf. FinitaryProject.agda *)


From Stdlib Require Import Relations List Program
     ssreflect ssrfun ssrbool.
From Stdlib Require Import Classes.RelationClasses 
  Classes.Morphisms Lia Arith.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Require Import findom.
Require Import types.
Require Import syntax.syntax.
Require Import syntax.typing.

Import SyntaxNotations.
Import SubstNotations.

Open Scope syntax_scope.

Import Raw.



(* if u has type a then return it else return bot *)
Fixpoint proj_tpi' (proj : elt -> elt -> elt) 
  (f : list (elt * elt)) 
  (a: elt) (b:elt)
   : list (elt * elt) := 
    match f with 
    | nil => nil 
    | cons (u,v) ps => 
        cons (proj u a, proj v b) (proj_tpi' proj ps a b)
    end.

Fixpoint proj_fun' (proj : elt -> elt -> elt)
  (g : list (elt * elt)) 
  (a : elt) (f : list (elt * elt)) 
  : list (elt * elt) := 
    match g with 
    | nil => nil 
    | cons (u,v) ps => 
        let x := proj u a  in
        let y := match app f x with 
                 | Some t => proj v t
                 | None => bot
                 end
        in
        cons (x, y) (proj_fun' proj ps a f)
    end.

Fixpoint proj (u : elt) (a : elt) {struct u} : elt := 
  match a with 
  | bot => bot
  | tuniv i => match u with 
              | tnat => tnat
              | tuniv j => if (j <? i) then tuniv j else bot
              | tpi b f => tpi (proj b (tuniv i))
                              (proj_tpi' proj f b (tuniv i))
              | _ => bot
              end
  | tpi a f => match u with 
              | abs g => abs (proj_fun' proj g a f)
              | _ => bot
              end
  | tnat => match u with 
             | zero => zero
             | succ v => succ (proj v tnat)
             | _ => bot
           end
  | _ => bot
  end
 .

Notation proj_tpi := (proj_tpi' proj).
Notation proj_fun := (proj_fun' proj).

Lemma proj_bot_ty u : proj u bot = bot.
destruct u; try done.
Qed.

Lemma proj_bot_tm a : proj bot a = bot.
destruct a; try done.
Qed.

Lemma proj_tuniv i j : 
  proj (tuniv i) (tuniv j) = if i <? j then tuniv i else bot.
Proof.
  cbn. destruct j; try lia. done.
  destruct (i <=? j) eqn:LE; reflexivity.
Qed.

Lemma proj_tnat_tuniv j :
  proj tnat (tuniv j) = tnat.
Proof.
  reflexivity.
Qed.

Lemma proj_succ_tnat u : 
  proj (succ u) tnat = succ (proj u tnat).
Proof. 
  cbn. f_equal.
Qed.

Lemma proj_tpi_tuniv a f j  : 
  proj (tpi a f) (tuniv j) = 
    tpi (proj a (tuniv j)) (proj_tpi f a (tuniv j)). 
Proof.
  reflexivity.
Qed.

Lemma proj_abs_tpi f a g :
  proj (abs f) (tpi a g) = abs (proj_fun f a g).
Proof.
  reflexivity.
Qed.

Lemma proj_forward a u : wt u a -> proj u a = u.
Proof.
  move=> h.
  induction h.
  all: try reflexivity.
  - rewrite proj_bot_tm. done.
  - rewrite proj_tuniv.  
    admit.
  - rewrite proj_succ_tnat. rewrite IHh. done.
  - rewrite proj_tpi_tuniv. rewrite IHh.
    f_equal.
    admit.
    (*
    clear H H1 h H3 IHh.
    move: H0 H2.
    induction g as [|[u v]g].
    all: move=> Hui Hvi. cbn. done.
    move:(Hui u v ltac:(left; reflexivity)) => h1.
    move:(Hvi u v ltac:(left; reflexivity)) => h2.
    cbn.
    f_equal.
    rewrite h1. rewrite h2. done.
    eapply IHg; eauto.
    move=> ui vi Ing. 
    eapply Hui; eauto. right; eauto.
    move=> ui vi Ing.
    eapply Hvi; eauto. right; eauto. *)
  - rewrite proj_abs_tpi. f_equal.
    admit.
    (*
    move: f H H0 H1 H2 H3.
    induction f as [|[u v]f].
    all: intros HTu HEu HTv HEv Vf. all: cbn. done.
    have Vg: valid_fun g. { move: H4 => /andP. eauto. } 
    have Vu: valid u. { admit. } 
    destruct (valid_app_exists Vg Vu) as [w [EQw Vw]].
    erewrite (HEu u v w); eauto. 2: left; eauto.
    rewrite EQw. f_equal.
    rewrite (HEv u v w); eauto. left; eauto.
    destruct (~~is_nil f) eqn:Nf.
    + have Vff: valid (abs f). { admit. } 
      eapply IHf; eauto.
      all: move=> ui vi wi INf APP.
      eapply HTu; eauto. right; eauto.
      eapply HEu; eauto. right; eauto.
      eapply HTv; eauto. right; eauto.
      eapply HEv; eauto. right; eauto.
    + destruct f; try done. *)
Admitted.


Fixpoint proj_backward u {struct u} : forall a i , 
  wt a (tuniv i) -> valid u -> proj u a = u -> wt u a.
Proof.
  dependent destruction u.
  all: intros a i Wt Vu EQ.
  - eapply wt_bot; eauto with valid.
  - destruct a; try done. 
    eapply wt_tnat; eauto with valid.
  - destruct a; try done.
    rewrite  proj_tuniv in EQ. 
    destruct (n <? n0) eqn:LT; try done.
    inversion Wt. subst.
    eapply wt_tuniv; eauto. 
    rewrite Nat.ltb_lt in LT. done.
  - destruct a; try done.
    eapply wt_zero; eauto.
  - destruct a; try done.
    eapply wt_succ; eauto.
    rewrite proj_succ_tnat in EQ. inversion EQ. clear EQ.
    rewrite H0. eapply proj_backward; eauto.
  - admit.
  - admit.
Admitted.
    
(* Lemma 2 *)
Lemma proj_valid a u : wt u a -> valid (proj u a).
move=> WT. rewrite proj_forward; eauto with valid.
Qed.

Hint Resolve proj_valid : valid.

