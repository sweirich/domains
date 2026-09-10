(** * types.v: Well-typed finite elements ([wt], the FinMem relation)

    This file defines the typing relation [wt u a] ("the finite element [u]
    is a member of the type [a]"), the Coq analogue of Agda's [FinMem].  It
    is the semantic well-typedness judgment on the elements of the value
    domain (defined in [findom.v]), and is the layer the value PER in
    [raw_validity.v] is built over.

    The headline results are:
    - [wt_le]  — typing is monotone in the type: [u : a] and [a <= b] give [u : b];
    - [wt_lub] — types are closed under joins of compatible members;
    - [wt_app] — application: if [abs w : tpi a f] and [u : a] then [w u : f u].

    The first two are proven together inside module [WTLE] by well-founded
    induction on a rank bound [k], because each direction needs the other at
    smaller rank; the closed forms are re-exported afterwards. *)

From Stdlib Require Import Relations List Program
     ssreflect ssrfun ssrbool.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

From Stdlib Require Import Classes.RelationClasses Classes.Morphisms Lia Arith.


Require Import smpl.Smpl.

Require Import utils.all.
Require Import finelt.utils.

From Equations Require Import Equations.

Require Import findom.

Import findom.Raw.

(* Note about minimality / function representation
 
   For some functions: we might want this property
 
    (ui,vi) in f, (uj,vj) in f,   ui <= uj implies vi <= vj 

   This gives us for any (ui,vi) in f,
    app f ui = Some vi    
    (* exactly, don't need to look at other tuples *)

    
   example: consider F:
     (succ (succ bot),  { (1,1) }  )
     (succ bot, { (0,0) } )


   minimal but violates the property because 
      F (suc (succ bot)) = { (0,0), (1,1) }

   this property + minimal means unique representation for sets of pairs
   
*)


(* -------------------------------------------------------------- *)


(** Well-typed elements ([FinMem]).  [wt u a] reads "element [u] inhabits type
    [a]".  In this branch [tuniv] has no universe-level argument
    (type-in-type), so every type lives in the single universe [tuniv].  A type
    [tpi a g] (a finite Π / dependent-function code) is well-formed when its
    domain [a] is a type, every recorded key/value pair types its key at [a]
    and its value at [tuniv], and the underlying term is [valid]; an
    abstraction [abs f] inhabits [tpi a g] when each entry's key types at [a]
    and its value types at the codomain [app g ui]. *)
Inductive wt : elt -> elt -> Prop :=
  | wt_bot a :
    wt a tuniv ->
    wt bot a

  | wt_tuniv :
    wt tuniv tuniv

  | wt_tnat :
    wt tnat tuniv

  | wt_zero :
    wt zero tnat

  | wt_succ u :
    wt u tnat ->
    wt (succ u) tnat

  | wt_tpi a g :
    wt a tuniv ->
    (* check all pairs *)
    (forall ui vi, In (ui, vi) g -> wt ui a) ->
    (forall ui vi, In (ui,vi) g -> wt vi tuniv) ->
    (* make sure tm is valid *)
    valid (tpi a g) ->
    wt (tpi a g) tuniv

  | wt_abs a f g :
    (* check definition against type *)
    (forall ui vi, In (ui, vi) f -> wt ui a) ->
    (forall ui vi, In (ui,vi) f -> wt vi (app g ui)) ->
    (* make sure tm is valid *)
    valid (abs f) ->
    (* make sure type is a type *)
    wt (tpi a g) tuniv ->
    wt (abs f) (tpi a g)

  (* Identity fragment (Agda [ID/Domain/MemStage.agda], clauses
     [fm' (IdCode t u v) UCode] and [fm' (RefEl w) (IdCode t u v)]).

     [tid t u v] is a *type code*: it inhabits [tuniv] exactly when [t] is a
     type and both endpoints inhabit [t].  (That [bot] then inhabits
     [tid t u v] is already given by [wt_bot].) *)
  | wt_tid c x y :
    wt c tuniv ->
    wt x c ->
    wt y c ->
    wt (tid c x y) tuniv

  (* [rfl w] is a *proof*: it inhabits [tid t u v] when the witness [w]
     inhabits [t] and sits below *both* endpoints (Coquand's rule).  The
     [wt (tid t u v) tuniv] premise keeps the type projections
     ([wt_ty_tuniv] and friends) available. *)
  | wt_rfl w c x y :
    wt w c ->
    le w x ->
    le w y ->
    wt (tid c x y) tuniv ->
    wt (rfl w) (tid c x y)

  (* Σ fragment (Agda [SigmaProp/PaperSemanticsSigma.agda], clauses
     [FinMem (SigmaCode a f) UCode] and [FinMem (PairCode u v) (SigmaCode a f)]).

     [tsig a g] is the [tpi] rule verbatim -- Σ-codes and Π-codes are typed
     identically, and both live only in [tuniv] (Agda's
     [FinMem (SigmaCode a f) PropCode = Empty]). *)
  | wt_tsig a g :
    wt a tuniv ->
    (forall ui vi, In (ui, vi) g -> wt ui a) ->
    (forall ui vi, In (ui, vi) g -> wt vi tuniv) ->
    valid (tsig a g) ->
    wt (tsig a g) tuniv

  (* [mkpair x y] inhabits [tsig a g] when [x] inhabits the domain and [y]
     inhabits the codomain *instantiated at the first component*, [app g x].
     That is the dependency, and it is the same [app g u] shape [wt_abs] uses.
     The [valid] premise carries the "not both [bot]" side condition. *)
  | wt_mkpair x y a g :
    wt x a ->
    wt y (app g x) ->
    valid (mkpair x y) ->
    wt (tsig a g) tuniv ->
    wt (mkpair x y) (tsig a g)

  (* Prop fragment (Agda [SigmaProp/PaperSemanticsSigma.agda], clauses
     [FinMem PropCode UCode] and [FinMem (PiCode a f) PropCode]).

     [tprop] is a type code: [Prop : U].  Note what is deliberately absent --
     [tprop] is not a member of itself (Agda's
     [decFinMem PropCode PropCode = no]) and no [tsig] code is a member of it
     (Agda's [decFinMem (SigmaCode a f) PropCode = no]), which is why the Σ
     fragment is independent of this one. *)
  | wt_tprop :
    wt tprop tuniv

  (* A Π code inhabits [tprop] when its codomain values do: the [wt_tpi] rule
     with [tprop] in place of [tuniv] on the values.  This is [ty-Pi-Prop]'s
     semantic side, and it is the only way a non-[bot] element gets into
     [tprop]. *)
  | wt_tpi_prop a g :
    wt a tuniv ->
    (forall ui vi, In (ui, vi) g -> wt ui a) ->
    (forall ui vi, In (ui, vi) g -> wt vi tprop) ->
    valid (tpi a g) ->
    wt (tpi a g) tprop.

(** * Validity *)

(** A well-typed element is a [valid] term, and so is its type. *)
Fixpoint wt_valid_tm u a : wt u a -> valid u.
- induction 1; eauto.
  (* [tid]: validity is componentwise, so it has no [valid] premise (unlike
     [wt_tpi]/[wt_abs], whose tables need one) — build it from the IHs. *)
  cbn. apply /andP ; split ; [ apply /andP ; split | ]; assumption.
Qed.

Lemma wt_valid_ty u a : wt u a -> valid a.
induction 1; eauto using wt_valid_tm.
Qed.

Hint Resolve wt_valid_tm wt_valid_ty : valid.

(* Only bot has type bot *)
Lemma wt_bot_inv u : wt u bot -> u = bot.
Proof. move=> h. inversion h. done. Qed.

(** Generation / regularity *)

(** Regularity: the type of any well-typed element is itself a type, i.e. lives
    in [tuniv].  (Agda: [FinMem-a-in-U]; here type-in-type makes [tuniv] the
    single universe.) *)
Lemma wt_ty_tuniv u a : wt u a -> wt a tuniv.
Proof.
  induction 1; eauto using wt_tuniv, wt_tnat, wt_tpi, wt_tprop.
Qed.

(** ** Inversion lemmas *)


Lemma wt_succ_inv u:
  wt (succ u) tnat -> wt u tnat.
move=>h. inversion h. done. Defined.

Lemma wt_abs_ty g b f : 
  wt (abs g) (tpi b f) -> wt (tpi b f) tuniv.
Proof. 
  move=> h. inversion h. eauto.
Defined.


Lemma wt_abs_inv1 g a f : 
  wt (abs f) (tpi a g) ->     
  (forall ui vi, In (ui, vi) f -> wt ui a).
Proof. 
  move=> h. inversion h. eauto.
Defined.

Lemma wt_abs_inv2 g a f :
  wt (abs f) (tpi a g) ->
  (forall ui vi t, In (ui,vi) f ->
              app g ui = t -> wt vi t).
Proof. 
  move=> h. inversion h. intros. subst. auto.
Defined.


Lemma wt_tpi_keys a g :
  wt (tpi a g) tuniv -> forall ui vi, In (ui, vi) g -> wt ui a.
Proof. move=> h. inversion h. eauto. Defined.

Lemma wt_tpi_dom a g :
  wt (tpi a g) tuniv  -> wt a tuniv.
Proof.
  move=> h. inversion h. eauto.
Defined.

(* ---- accessors for the Sigma fragment ---- *)

(* The first component inhabits the domain code, ... *)
Lemma wt_mkpair_fst x y a g :
  wt (mkpair x y) (tsig a g) -> wt x a.
Proof. move=> h. inversion h. eauto. Defined.

(* ... the second inhabits the table applied to the first (this is where the
   dependency lives), ... *)
Lemma wt_mkpair_snd x y a g :
  wt (mkpair x y) (tsig a g) -> wt y (app g x).
Proof. move=> h. inversion h. eauto. Defined.

(* ... and the type of a pair is a well-formed Sigma code. *)
Lemma wt_mkpair_ty x y a g :
  wt (mkpair x y) (tsig a g) -> wt (tsig a g) tuniv.
Proof. move=> h. inversion h. eauto. Defined.

Lemma wt_tsig_dom a g :
  wt (tsig a g) tuniv -> wt a tuniv.
Proof. move=> h. inversion h. eauto. Defined.

Lemma wt_tsig_keys a g :
  wt (tsig a g) tuniv -> forall ui vi, In (ui, vi) g -> wt ui a.
Proof. move=> h. inversion h. eauto. Defined.

(* The only inhabitants of a Sigma code are [bot] and pairs. *)
Lemma wt_tsig_shape v a g :
  wt v (tsig a g) -> v = bot \/ exists x y, v = mkpair x y.
Proof.
  move=> h. dependent destruction h.
  - left; reflexivity.
  - right; eauto.
Qed.

(* ---- accessors for the identity fragment ---- *)

Lemma wt_tid_dom c x y :
  wt (tid c x y) tuniv -> wt c tuniv.
Proof. move=> h. inversion h. eauto. Defined.

Lemma wt_tid_lhs c x y :
  wt (tid c x y) tuniv -> wt x c.
Proof. move=> h. inversion h. eauto. Defined.

Lemma wt_tid_rhs c x y :
  wt (tid c x y) tuniv -> wt y c.
Proof. move=> h. inversion h. eauto. Defined.

(* The type of a proof is a well-formed [tid] code, ... *)
Lemma wt_rfl_ty w c x y :
  wt (rfl w) (tid c x y) -> wt (tid c x y) tuniv.
Proof. move=> h. inversion h. eauto. Defined.

(* ... its witness inhabits the type code, ... *)
Lemma wt_rfl_wit w c x y :
  wt (rfl w) (tid c x y) -> wt w c.
Proof. move=> h. inversion h. eauto. Defined.

(* ... and sits below both endpoints (Coquand's rule). *)
Lemma wt_rfl_le_lhs w c x y :
  wt (rfl w) (tid c x y) -> le w x.
Proof. move=> h. inversion h. eauto. Defined.

Lemma wt_rfl_le_rhs w c x y :
  wt (rfl w) (tid c x y) -> le w y.
Proof. move=> h. inversion h. eauto. Defined.




Lemma wt_abs_cons 
  a f g :
  wt (abs f) (tpi a g) -> 
  forall ui vi,
    wt ui a -> wt vi (app g ui) ->
    valid (abs ((ui,vi)::f)) ->
    wt (abs ((ui,vi) :: f)) (tpi a g).
Proof.
  move=> h.
  inversion h. subst.
  intros ui vi WTui WTvi Vcons.
  have Vui: valid ui. eauto with valid.
  eapply wt_abs.
  - intros ui0 vi0 [EQ|INf].
    + inversion EQ. subst. auto.
    + eauto.
  - intros ui0 vi0 [EQ|INf].
    + inversion EQ. subst ui0. subst vi0. clear EQ.
      done.
    + eapply H3; eauto.
  - done.
  - done.
Qed.

Lemma wt_tpi_tail a u v g : 
  wt (tpi a ((u,v)::g)) tuniv -> wt (tpi a g) tuniv.
Proof.
  intro h. inversion h.
  eapply wt_tpi; eauto.
  - intros ui vi Ing.
    eapply H2; eauto. right. eauto.
  - intros ui vi Ing.
    eapply H3; eauto. right. eauto.
  - apply valid_tpi_inv in H4. move: H4 => [Va Vl].
    eapply valid_tpi_intro; eauto.
    eapply valid_fun_tail; eauto.
Qed.

Lemma wt_abs_tail u v w b f :
  wt (abs ((u,v)::w)) (tpi b f) -> ~~is_nil w ->
  wt (abs w) (tpi b f).
Proof.
  move=> WT Nw. inversion WT. subst.
  have Vb: valid b. eauto with valid.
  have Vf: valid_fun f. eauto with valid.
  have Vw: valid_fun ((u,v):: w). eauto with valid.
  move: (valid_fun_tail Vw) => Vt.
  move: (valid_fun_head Vw) => Vh.
  eapply wt_abs; eauto. 
  - intros ui vi Inw. eapply H2; eauto. right; eauto.
  - intros ui vi Inw. eapply H3; eauto. right; eauto.
  - cbn. rewrite Vt. rewrite Nw. done.
Qed.


From Stdlib Require Import Psatz.

(** ** Monotonicity and join-closure of typing

    [wt_le] (typing respects [le] on types) and [wt_lub] (types are closed
    under joins of compatible elements) are mutually dependent, so they are
    proven simultaneously by strong induction on a rank bound [k]: the record
    [WTLE_Lemmas k] packages both statements restricted to elements/types of
    rank [<= k], and [WTLE] discharges them for every [k]. The rank-free
    corollaries [wt_le] and [wt_lub] are exported just below the module. *)
(* Every non-[bot] code has positive rank.  ([selection.v] has the same lemma,
   but that file is downstream of this one.) *)
Lemma rk_pos_loc e : is_bot e = false -> 1 <= rk e.
Proof. destruct e; cbn; first discriminate; lia. Qed.

Lemma is_bot_eq_loc e : is_bot e = true -> e = bot.
Proof. destruct e; cbn; by [ | discriminate ]. Qed.

(* [tsig a g] and [tpi a g] are typed by *identical* premises (Agda's
   [FinMem (SigmaCode a f) UCode] is [FinMem (PiCode a f) UCode] verbatim), and
   their [valid]s are the same formula.  Converting between them lets the whole
   Π-table machinery -- [all_app_is_tuniv] above all -- be reused for Σ instead
   of duplicated. *)
(* [Defined], not [Qed]: [ValTySig]/[EqValTySig] embed this derivation as the
   [wt] index of a [PiEdgeVal]/[PiEdgeEq], so it has to stay transparent. *)
Lemma wt_tsig_tpi a g : wt (tsig a g) tuniv -> wt (tpi a g) tuniv.
Proof. move=> h. inversion h; subst. eapply wt_tpi; eauto. Defined.

Lemma wt_tpi_tsig a g : wt (tpi a g) tuniv -> wt (tsig a g) tuniv.
Proof. move=> h. inversion h; subst. eapply wt_tsig; eauto. Qed.

Module WTLE.


Record WTLE_Lemmas k := MkLemmas {
  (* both measures are STRICT and both mention the type, so that
     [rk_fun g < rk (tpi a g) < k] is available wherever a table is applied *)
  wt_le  : forall u a (h : wt u a) b, 
           max (rk a) (rk b) < k ->
           le a b -> wt a tuniv -> wt b tuniv -> wt u b ;
  (* The measure sees the TYPE as well as the elements.  [wt_mkpair]'s second
     component is typed at [app g x], so its case needs [rk_fun g] bounded --
     and [g] lives in the type [tsig a g].  [rk (tsig a g)] already carries a
     [1 +], so the bound comes out STRICT for free.

     [wt_rfl] is unaffected: its type components are bounded by the type's own
     rank ([rk c < rk (tid c x y) <= k]), which the measure now supplies.

     The inequality is STRICT, and that is what makes it close.  At a unit type
     ([tnat]/[tuniv]) the conjunct [rk a < k] *gives* [1 < k] rather than
     demanding it -- with [<=] the obligation migrated to every such recursive
     call and had to be discharged by hand. *)
  wt_lub : forall u a (h: wt u a) v, max (rk u) (max (rk v) (rk a)) < k ->
           compatible u v ->
           wt v a -> wt (lub u v) a 

}.

Lemma all_app_is_tuniv k
  (ih : WTLE_Lemmas k) {a g} (h : wt (tpi a g) tuniv) : 
  (rk_fun g) < k ->
  forall u, valid u -> wt (app g u) tuniv.
Proof.
  move: h.
  induction g as [|[ui vi] g];
  intros h RK u Vu.
  - inversion h; subst.
    rewrite app_nil_eq.
    eapply wt_bot. eapply wt_tuniv.
  - have WTt : wt (tpi a g) tuniv by (eapply wt_tpi_tail; eauto).
    specialize (IHg WTt ltac:(cbn in RK; cbn; lia) u). 
    rewrite app_cons_eq.
    destruct (le ui u) eqn:EQ.
    + inversion h.
      cbn in RK.
      have RK1 : rk (app g u) <= rk_fun g. eapply rk_app.
      have WT1 : wt vi tuniv by (apply: (H3 ui vi); left).
      (* the recursive [wt_lub] is at type [tuniv], so its measure carries
         [rk tuniv = 1] and needs [1 < k].  The table's own [no_bot_result]
         supplies it: [vi] is not [bot], so [1 <= rk vi <= rk_fun (…) < k]. *)
      have Vfc : valid_fun ((ui, vi) :: g) by (eauto with valid).
      have NBvi : is_bot vi = false.
      { have NB := valid_fun_no_bot Vfc.
        rewrite /no_bot_result /= in NB.
        move: NB => /andP [hnb _].
        destruct vi; try reflexivity.
        move: hnb. simp le. done. }
      have Rvi : 1 <= rk vi by (apply rk_pos_loc; exact NBvi).
      have Rtu : rk tuniv = 1 by reflexivity.
      eapply (@wt_lub _ ih _ _ WT1); eauto; try lia.
      eapply compatible_coherent_app; eauto.
      eapply le_compatible; eauto.
      eauto with valid.
    + eapply IHg; eauto.
Qed.


(* Discharging a recursive [wt_lub] obligation.

   The measure strictly decreases at every recursive call -- with ONE
   exception.  When the recursion leaves the type alone (which happens exactly
   at the unit types [tnat] and [tuniv], of rank 1) and BOTH joined elements
   are [bot], the element ranks are 0 and cannot pay for the type's rank floor:
   [max 0 (max 0 1) = 1] is not [< max 0 (max 0 1) = 1].

   That corner needs no recursion at all -- [lub bot z = z] -- so dispatch it
   first.  In the surviving branch neither side is [bot], which hands [lia] the
   [1 <= rk _] facts it was missing. *)
Ltac lub_rec :=
  match goal with
  | [ |- wt (lub ?x ?z) _ ] =>
      let Bx := fresh "Bx" in
      destruct (is_bot x) eqn:Bx;
      [ rewrite (is_bot_eq_loc Bx) lub_bot_l; eauto
      | let Bz := fresh "Bz" in
        destruct (is_bot z) eqn:Bz;
        [ rewrite (is_bot_eq_loc Bz) lub_bot_r; eauto
        | pose proof (rk_pos_loc Bx);
          pose proof (rk_pos_loc Bz);
          eapply wt_lub; eauto; try lia ] ]
  end.

Lemma WTLE : forall k, WTLE_Lemmas k.
Proof.
  elim /strong_ind.
  move=> m ih. 
  split.
(* wt is monotone *)
  - (* If u : a and a <= b, then u : b *)
    move=> u a h b RK. 
    dependent destruction h.
    all: move=> LE WTa WTb.
    7 : { 
      destruct (le_tpi_inv LE) as [a1 [g1 [-> [LEa LEg]]]].
      have Wta: wt a tuniv. inversion WTa; eauto.
      have Wta1: wt a1 tuniv. inversion WTb; eauto.      
      cbn in RK.
      eapply wt_abs; eauto.
      ++ intros ui vi Inf.
         specialize (ih (S (max (rk a) (rk a1))) ltac:(lia)).
         eapply wt_le; eauto; try lia.
      ++ intros ui vi Inf.
         have RA: rk (app g ui) <= rk_fun g. eapply rk_app.
         have RA1: rk (app g1 ui) <= rk_fun g1. eapply rk_app.
         specialize (ih (S (max (rk_fun g) (rk_fun g1))) ltac:(lia)).
         have Vg : valid_fun g. eauto with valid.
         have Vg1 : valid_fun g1. eauto with valid.
         have Vui : valid ui. eauto with valid.
         move: (le_fun_mono Vg Vg1 LEg Vui) => LEt.
         have WTt: (wt (app g1 ui) tuniv).
         { eapply all_app_is_tuniv; eauto. lia. }
         have WTt2: (wt (app g ui) tuniv).
         { inversion WTa. eapply all_app_is_tuniv; eauto. lia. }
         eapply wt_le; eauto. lia.
    } 
    all: cbn in RK.
    + eapply wt_bot; eauto.
    + apply le_tuniv_inv in LE. subst.
      eapply wt_tuniv.
    + apply le_tuniv_inv in LE. subst.
      eapply wt_tnat.
    + apply le_tnat_inv in LE. subst.
      eapply wt_zero.
    + eapply le_tnat_inv in LE. subst.
      eapply wt_succ; eauto.
    + apply le_tuniv_inv in LE. subst.
      eapply wt_tpi; eauto.
    + (* wt_tid: a type code, so [b] is [tuniv] and nothing moves *)
      apply le_tuniv_inv in LE. subst.
      eapply wt_tid; eauto.
    + (* wt_rfl: the witness must be retyped at the larger code and pushed
         below the larger endpoints *)
      destruct (le_tid_inv LE) as [c' [x' [y' [E [LEc [LEx LEy]]]]]]. subst.
      have Wc  : wt c  tuniv by (inversion WTa; eauto).
      have Wx  : wt x  c     by (inversion WTa; eauto).
      have Wy  : wt y  c     by (inversion WTa; eauto).
      have Wc' : wt c' tuniv by (inversion WTb; eauto).
      have Wx' : wt x' c'    by (inversion WTb; eauto).
      have Wy' : wt y' c'    by (inversion WTb; eauto).
      have Ww  : wt w c      by eauto.
      have Lwx : le w x      by eauto.
      have Lwy : le w y      by eauto.
      cbn in RK.
      specialize (ih (S (max (max (rk c) (rk c'))
                          (max (max (rk x) (rk x')) (max (rk y) (rk y')))))
                     ltac:(lia)).
      eapply wt_rfl; [ | | | exact WTb ].
      * solve [ eapply wt_le ; eauto ; lia | eapply wt_le ; eauto ].
      * eapply (@le_trans w x x') ; eauto with valid.
      * eapply (@le_trans w y y') ; eauto with valid.
    + (* wt_tsig: a type code, so [b] is [tuniv] and nothing moves *)
      apply le_tuniv_inv in LE. subst.
      eapply wt_tsig; eauto.
    + (* wt_mkpair: retype both components at the larger Σ-code.  The second
         component lives at [app g x], so it moves exactly as [wt_abs]'s
         table does -- through [le_fun_mono]. *)
      destruct (le_tsig_inv LE) as [a1 [g1 [-> [LEa LEg]]]].
      have Wta : wt a tuniv by (inversion WTa; eauto).
      have Wta1 : wt a1 tuniv by (inversion WTb; eauto).
      cbn in RK.
      eapply wt_mkpair; [ | | | exact WTb ].
      * specialize (ih (S (max (rk a) (rk a1))) ltac:(lia)).
        eapply wt_le; eauto.
      * have RA : rk (app g x) <= rk_fun g by eapply rk_app.
        have RA1 : rk (app g1 x) <= rk_fun g1 by eapply rk_app.
        specialize (ih (S (max (rk_fun g) (rk_fun g1))) ltac:(lia)).
        have Vg : valid_fun g by eauto with valid.
        have Vg1 : valid_fun g1 by eauto with valid.
        have Vx : valid x by eauto with valid.
        move: (le_fun_mono Vg Vg1 LEg Vx) => LEt.
        have WTt : wt (app g1 x) tuniv
          by (eapply all_app_is_tuniv;
              [ exact ih | eapply wt_tsig_tpi; exact WTb | lia | exact Vx ]).
        have WTt2 : wt (app g x) tuniv
          by (eapply all_app_is_tuniv;
              [ exact ih | eapply wt_tsig_tpi; exact WTa | lia | exact Vx ]).
        eapply wt_le; eauto. lia.
      * assumption.
    + (* wt_tprop: a type code, so [b] is [tuniv] and nothing moves *)
      apply le_tuniv_inv in LE. subst.
      eapply wt_tprop.
    + (* wt_tpi_prop: a Prop-valued Π code, so [b] is [tprop] and nothing
         moves -- [tprop] is [le]-maximal among its own approximants *)
      apply le_tprop_inv in LE. subst.
      eapply wt_tpi_prop; eauto.
  - (* If u : a and v : a, then lub u v : a. *)
    move=> u a h v RK Cav WTv.
    have WTa: wt a tuniv. eapply wt_ty_tuniv; eauto.
    have WTb:  wt bot a. eapply wt_bot; auto.
    have Vlub: valid (lub u v). 
    { eapply valid_lub; eauto using wt_valid_tm. } 
    (* the measure now mentions the type, so recursive calls at [tnat]/[tuniv]
       carry a [1 < _] conjunct *)
    have Rtu : rk tuniv = 1 by reflexivity.
    have Rtn : rk tnat = 1 by reflexivity.
    dependent destruction h.
    all: destruct v; cbn; auto.
    all: cbn in RK.
    all: try solve [eauto using wt].
    + inversion WTv; subst.
      eapply wt_succ; eauto.
      lub_rec.
    + inversion WTv; subst.
      cbn in Cav. move: Cav => /andP [Cav Cgl].
      rewrite Cgl.
      eapply wt_tpi; eauto.
      ++ lub_rec.
      ++ intros ui vi INgl.
         have Va: valid a. eauto with valid.
         have Vv: valid v. eauto with valid.
         have RKlub: rk (lub a v) <= max (rk a) (rk v). eapply rk_lub.
         destruct (in_app_or _ _ _ INgl) as [Ing|Inl].
         * eapply wt_le; eauto.  lia.
           eapply le_lub_left; eauto.
           lub_rec.
         * eapply wt_le; eauto.  lia.
           eapply le_lub_right; eauto.
           lub_rec.         
      ++ intros ui vi INgl.
         destruct (in_app_or _ _ _ INgl) as [Ing|Inl].
         eauto. eauto.
      ++ cbn in Vlub. rewrite Cgl in Vlub. done.
    + cbn in Cav. rewrite Cav.
      inversion WTv. subst.
      eapply wt_abs.
      ++ move=> u v APP.
       have Vf: valid_fun f. eauto with valid.
       have Vl: valid_fun l. eauto with valid.
       apply in_app_or in APP. destruct APP as [INf|Inl]; eauto.
    ++ (* wt rng for (f ++ l) *)
       move=> u v InApp.
       have Vf: valid_fun f. eauto with valid.
       have Vl: valid_fun l. eauto with valid.
       apply in_app_or in InApp. destruct InApp as [INf|Inl]; eauto.
    ++ cbn.
       apply /andP. split.
       eapply valid_append; eauto with valid.
       destruct f; try done.
    ++ done.

    + (* wt_tid: join the type codes, then retype both endpoint pairs at the
         joined code before joining them (Agda [Sup (IdCode ..) (IdCode ..)]) *)
      have Hc : wt c tuniv by eauto.
      have Hx : wt x c by eauto.
      have Hy : wt y c by eauto.
      have Hv1 : wt v1 tuniv by (inversion WTv; eauto).
      have Hv2 : wt v2 v1 by (inversion WTv; eauto).
      have Hv3 : wt v3 v1 by (inversion WTv; eauto).
      cbn in Cav. move: Cav => /andP [/andP [Cc Cx] Cy].
      have RKc : rk (lub c v1) <= max (rk c) (rk v1) by eapply rk_lub.
      have Hlubc : wt (lub c v1) tuniv
        by solve [ lub_rec | lub_rec ].
      have Lc : le c (lub c v1) by (eapply le_lub_left ; eauto with valid).
      have Lv1 : le v1 (lub c v1) by (eapply le_lub_right ; eauto with valid).
      have Hx' : wt x (lub c v1)
        by solve [ eapply wt_le ; eauto ; lia | eapply wt_le ; eauto ].
      have Hy' : wt y (lub c v1)
        by solve [ eapply wt_le ; eauto ; lia | eapply wt_le ; eauto ].
      have Hv2' : wt v2 (lub c v1)
        by solve [ eapply wt_le ; eauto ; lia | eapply wt_le ; eauto ].
      have Hv3' : wt v3 (lub c v1)
        by solve [ eapply wt_le ; eauto ; lia | eapply wt_le ; eauto ].
      eapply wt_tid; [ exact Hlubc | | ].
      ++ solve [ lub_rec | lub_rec ].
      ++ solve [ lub_rec | lub_rec ].
    + (* wt_rfl: join the witnesses; both stay below both endpoints, so
         [le_sup_lub] re-establishes Coquand's rule for the join *)
      have Hw : wt w c by eauto.
      have Lwx : le w x by eauto.
      have Lwy : le w y by eauto.
      have Htid : wt (tid c x y) tuniv by eauto.
      have Hv : wt v c by (inversion WTv; eauto).
      have Lvx : le v x by (inversion WTv; eauto).
      have Lvy : le v y by (inversion WTv; eauto).
      cbn in Cav.
      eapply wt_rfl; [ | | | exact Htid ].
      ++ solve [ lub_rec | lub_rec ].
      ++ eapply le_sup_lub ; eauto.
      ++ eapply le_sup_lub ; eauto.
    + (* wt_tsig: the [wt_tpi] argument verbatim *)
      inversion WTv; subst.
      cbn in Cav. move: Cav => /andP [Cav Cgl].
      rewrite Cgl.
      eapply wt_tsig; eauto.
      ++ lub_rec.
      ++ intros ui vi INgl.
         have Va: valid a. eauto with valid.
         have Vv: valid v. eauto with valid.
         have RKlub: rk (lub a v) <= max (rk a) (rk v). eapply rk_lub.
         destruct (in_app_or _ _ _ INgl) as [Ing|Inl].
         * eapply wt_le; eauto.  lia.
           eapply le_lub_left; eauto.
           lub_rec.
         * eapply wt_le; eauto.  lia.
           eapply le_lub_right; eauto.
           lub_rec.
      ++ intros ui vi INgl.
         destruct (in_app_or _ _ _ INgl) as [Ing|Inl].
         eauto. eauto.
      ++ cbn in Vlub. rewrite Cgl in Vlub. done.
    + (* wt_mkpair: join componentwise.  The second components live at
         [app g x] and [app g x'] respectively, so both are first pushed up to
         [app g (lub x x')] (monotonicity of the table in its argument) and
         only then joined. *)
      have Hx : wt x a by eauto.
      have Hy : wt y (app g x) by eauto.
      have Htsig : wt (tsig a g) tuniv by eauto.
      have Hv1 : wt v1 a by (inversion WTv; eauto).
      have Hv2 : wt v2 (app g v1) by (inversion WTv; eauto).
      cbn in Cav. move: Cav => /andP [Cx Cy].
      have Va : valid a by eauto with valid.
      have Vg : valid_fun g by eauto with valid.
      have Vx : valid x by eauto with valid.
      have Vv1 : valid v1 by eauto with valid.
      have RKx : rk (lub x v1) <= max (rk x) (rk v1) by eapply rk_lub.
      have Hlubx : wt (lub x v1) a
        by solve [ lub_rec | lub_rec ].
      have Vlubx : valid (lub x v1) by eauto using wt_valid_tm.
      have Lx : le x (lub x v1) by (eapply le_lub_left ; eauto).
      have Lv1 : le v1 (lub x v1) by (eapply le_lub_right ; eauto).
      have RAx : rk (app g x) <= rk_fun g by eapply rk_app.
      have RAv : rk (app g v1) <= rk_fun g by eapply rk_app.
      have RAl : rk (app g (lub x v1)) <= rk_fun g by eapply rk_app.
      have WTpi : wt (tpi a g) tuniv by (eapply wt_tsig_tpi; exact Htsig).
      (* [g] lives in the TYPE, and the measure sees it: [rk (tsig a g)] is
         [1 + max (rk a) (rk_fun g)], so [S (rk_fun g)] is bounded by the
         measure and the bundle can be instantiated at exactly that level. *)
      have RKg : S (rk_fun g) < m by lia.
      have ihg := ih _ RKg.
      have WTax : wt (app g x) tuniv
        by (eapply all_app_is_tuniv; [ exact ihg | exact WTpi | lia | exact Vx ]).
      have WTav : wt (app g v1) tuniv
        by (eapply all_app_is_tuniv; [ exact ihg | exact WTpi | lia | exact Vv1 ]).
      have WTal : wt (app g (lub x v1)) tuniv
        by (eapply all_app_is_tuniv;
            [ exact ihg | exact WTpi | lia | exact Vlubx ]).
      (* the table is fixed and the ARGUMENT grows, so this is
         [le_fun_mono_arg], not [le_fun_mono] *)
      have LEax : le (app g x) (app g (lub x v1))
        by (eapply le_fun_mono_arg; eauto).
      have LEav : le (app g v1) (app g (lub x v1))
        by (eapply le_fun_mono_arg; eauto).
      (* both retypings run at the [S (rk_fun g)] bundle: the two table
         results have rank [<= rk_fun g], so the [wt_le] measure is met *)
      have Hy' : wt y (app g (lub x v1))
        by (eapply (@wt_le _ ihg _ _ Hy);
            [ lia | exact LEax | exact WTax | exact WTal ]).
      have Hv2' : wt v2 (app g (lub x v1))
        by (eapply (@wt_le _ ihg _ _ Hv2);
            [ lia | exact LEav | exact WTav | exact WTal ]).
      eapply wt_mkpair; [ exact Hlubx | | | exact Htsig ].
      ++ (* join the second components, now that both sit at
            [app g (lub x v1)].  Its rank is [<= rk_fun g], so the bundle
            level is read straight off [RK]. *)
         have RKy : S (max (max (rk y) (rk v2)) (rk_fun g)) < m by lia.
         eapply (@wt_lub _ (ih _ RKy) _ _ Hy');
           [ lia | exact Cy | exact Hv2' ].
      ++ cbn in Vlub. exact Vlub.
    + (* wt_tpi_prop: the [wt_tpi] argument verbatim, with the codomain
         values at [tprop] instead of [tuniv] *)
      inversion WTv; subst.
      cbn in Cav. move: Cav => /andP [Cav Cgl].
      rewrite Cgl.
      eapply wt_tpi_prop; eauto.
      ++ lub_rec.
      ++ intros ui vi INgl.
         have Va: valid a. eauto with valid.
         have Vv: valid v. eauto with valid.
         have RKlub: rk (lub a v) <= max (rk a) (rk v). eapply rk_lub.
         destruct (in_app_or _ _ _ INgl) as [Ing|Inl].
         * eapply wt_le; eauto.  lia.
           eapply le_lub_left; eauto.
           lub_rec.
         * eapply wt_le; eauto.  lia.
           eapply le_lub_right; eauto.
           lub_rec.
      ++ intros ui vi INgl.
         destruct (in_app_or _ _ _ INgl) as [Ing|Inl].
         eauto. eauto.
      ++ cbn in Vlub. rewrite Cgl in Vlub. done.
Qed.
         
End WTLE.         


(** Typing is monotone in the type: if [u : a] and [a <= b] (both types) then
    [u : b].  (Agda: the [wt]-monotonicity half of [WTLE].) *)
Definition wt_le : forall u a (h : wt u a),
    forall b, le a b -> wt a tuniv -> wt b tuniv -> wt u b.
Proof.
  intros.
  eapply WTLE.wt_le; eauto. eapply WTLE.WTLE.
Qed.

(** Types are closed under joins: if [u : a] and [v : a] are compatible then
    [lub u v : a].  This is what makes each type an ideal (sub-lub-closed). *)
Definition wt_lub : forall u a (h: wt u a) v,
           compatible u v ->
           wt v a -> wt (lub u v) a.
Proof.   intros.
  eapply WTLE.wt_lub; eauto. eapply WTLE.WTLE.
Qed.

(** Applying a type-code [tpi a g] to any valid argument yields a type. *)
Lemma all_app_is_tuniv {a g} (h : wt (tpi a g) tuniv) :
  forall u, valid u -> wt (app g u) tuniv.
Proof. 
  intros.
  eapply WTLE.all_app_is_tuniv; eauto. eapply WTLE.WTLE.
Qed.

Lemma wt_tpi_inv2 a g :
  wt (tpi a g) tuniv  ->
  forall u v, valid u -> app g u = v -> wt v tuniv.
Proof.
  move=> h u v Vu <-. eapply all_app_is_tuniv; eauto.
Defined.


(* ------------------------------------------------------------------
   The Prop fragment's membership theory.
   ------------------------------------------------------------------ *)

(* A [tpi] code now inhabits TWO type codes, [tuniv] and [tprop].  Wherever
   the surrounding argument already knows the type approximates [tuniv] --
   which is exactly what [EvalRel Core.tuniv] gives -- that pins it down. *)
Lemma wt_tpi_ty_tuniv b f a : wt (tpi b f) a -> le a tuniv -> a = tuniv.
Proof.
  move=> h LE. dependent destruction h.
  - reflexivity.
  - exfalso. move: (le_tprop_inv _ LE) => E. discriminate.
Qed.

Lemma wt_tpi_prop_tail a u v g :
  wt (tpi a ((u,v)::g)) tprop -> wt (tpi a g) tprop.
Proof.
  intro h. inversion h.
  eapply wt_tpi_prop; eauto.
  - intros ui vi Ing. eapply H2; eauto. right. eauto.
  - intros ui vi Ing. eapply H3; eauto. right. eauto.
  - apply valid_tpi_inv in H4. move: H4 => [Va Vl].
    eapply valid_tpi_intro; eauto.
    eapply valid_fun_tail; eauto.
Qed.

(** The Prop analogue of [all_app_is_tuniv]: applying a Prop-valued Π code to
    any valid argument lands in [tprop].  No rank bookkeeping is needed here,
    because the closed [wt_lub] above is already available. *)
Lemma all_app_is_tprop {a g} (h : wt (tpi a g) tprop) :
  forall u, valid u -> wt (app g u) tprop.
Proof.
  move: h. induction g as [|[ui vi] g IHg]; intros h u Vu.
  - rewrite app_nil_eq. eapply wt_bot. eapply wt_tprop.
  - have WTt : wt (tpi a g) tprop by (eapply wt_tpi_prop_tail; eauto).
    specialize (IHg WTt u Vu).
    have WT1 : wt vi tprop by (inversion h; apply: (H3 ui vi); left; reflexivity).
    have Vfc : valid_fun ((ui, vi) :: g) by (eauto with valid).
    rewrite app_cons_eq.
    destruct (le ui u) eqn:EQ.
    + eapply wt_lub; [ exact WT1 | | exact IHg ].
      eapply compatible_coherent_app; eauto.
      eapply le_compatible; eauto.
      eauto with valid.
    + exact IHg.
Qed.

(** THE payload of the Prop fragment: a type whose code inhabits [tprop] has
    only [bot] as a member.  Proof irrelevance is then free, because
    [Val]/[EqVal] at a [bot] ELEMENT code are already total
    ([Val_Bot]/[EqVal_Bot]) -- so the logical relation needs no change at all.

    Agda: [FinMem-Prop-Bot] (PaperSemanticsSigma.agda:3061).  The one
    non-trivial case is [abs] at a Prop-valued Π ([FinMem-Prop-Bot-FunEl]):
    every edge value of the type's graph lands in [tprop], hence recursively in
    [bot], but a [valid] table carries no [bot] value and is non-empty -- so
    that case is vacuous rather than collapsing. *)
Lemma wt_prop_bot_rec : forall k u a, rk a < k -> wt u a -> wt a tprop -> u = bot.
Proof.
  elim /strong_ind => m ih u a RK Hu Ha.
  dependent destruction Ha.
  - (* a = bot: nothing but [bot] inhabits [bot] *)
    exact (wt_bot_inv Hu).
  - (* a = tpi a0 g with all codomain values in [tprop] *)
    rename a into a0.
    dependent destruction Hu.
    + reflexivity.
    + (* u = abs f: vacuous *)
      exfalso.
      have Vabs : valid (abs f) by assumption.
      have NN : ~~ is_nil f by (move: Vabs; cbn; move=> /andP [_ h]; exact h).
      destruct f as [|[u1 v1] f']; first (cbn in NN; done).
      have INf : In (u1, v1) ((u1, v1) :: f') by (left; reflexivity).
      have Vf : valid_fun ((u1, v1) :: f') by (eauto with valid).
      have Vu1 : valid u1 by (eauto with valid).
      have WTv1 : wt v1 (app g u1) by (eapply H0; exact INf).
      have WTapp : wt (app g u1) tprop
        by (eapply (@all_app_is_tprop a0 g); [ eapply wt_tpi_prop; eauto | exact Vu1 ]).
      have RKa : rk (app g u1) <= rk_fun g by (eapply rk_app).
      have RKg : rk_fun g < rk (tpi a0 g) by (cbn; lia).
      have RKlt : S (rk (app g u1)) < m by lia.
      have E : v1 = bot
        by (eapply (ih (S (rk (app g u1))) RKlt v1 (app g u1));
              [ lia | exact WTv1 | exact WTapp ]).
      (* but a valid table has no [bot] value *)
      have NB := valid_fun_no_bot Vf.
      rewrite /no_bot_result /= in NB.
      move: NB => /andP [hnb _].
      rewrite E in hnb. cbn in hnb. done.
Qed.

(** The domain-level Prop-to-U subtyping -- the semantic content of the typing
    rule [t_prop_u] (Agda [Adequacy5Helpers.agda], "Part 5b: FinMem
    PropCode-to-UCode conversion").  [tprop]'s inhabitants are [bot] and the
    Prop-valued Pi codes, and a Pi code all of whose codomain values are Props
    is in particular one all of whose codomain values are types -- recursively,
    down the rank of the code. *)
Lemma wt_prop_univ_rec : forall k v, rk v < k -> wt v tprop -> wt v tuniv.
Proof.
  elim /strong_ind => m ih v RK h.
  dependent destruction h.
  - (* v = bot: [bot] inhabits every code *)
    eapply wt_bot; eapply wt_tuniv.
  - (* v = tpi a g, with every codomain value in [tprop] *)
    rename a into a0.
    have RKg : S (rk_fun g) <= rk (tpi a0 g) by (cbn; lia).
    eapply wt_tpi; try eassumption.
    move=> ui vi Hin.
    have RKvi : rk vi <= rk_fun g by (exact (@In_rk_fun2 (ui, vi) g Hin)).
    have RKlt : S (rk vi) < m by lia.
    eapply (ih (S (rk vi)) RKlt vi); [ lia | eapply H0; exact Hin ].
Qed.

Lemma wt_prop_univ v : wt v tprop -> wt v tuniv.
Proof.
  move=> h. eapply (@wt_prop_univ_rec (S (rk v)) v); [ lia | exact h ].
Qed.

Lemma wt_prop_bot u a : wt u a -> wt a tprop -> u = bot.
Proof.
  move=> h1 h2.
  eapply (@wt_prop_bot_rec (S (rk a)) u a); [ lia | exact h1 | exact h2 ].
Qed.

(** Application (Corollary 2): if [abs w : tpi a f] and [u : a], then the
    applied value [app w u] inhabits the codomain image [app f u]. This is the
    semantic counterpart of the application typing rule. *)
Lemma wt_app w a f :
  wt (abs w) (tpi a f) ->
  forall u, wt u a -> wt (app w u) (app f u).
Proof.
  induction w as [|[ui vi] w'].
  - (* w = nil is impossible: valid (abs nil) is false *)
    move=> WT u WTu.
    move: (wt_valid_tm WT). by cbn.
  - move=> WT u WTu.
    have Vu : valid u by eauto with valid.
    have Vtpi : valid (tpi a f) by eauto with valid.
    have Vf : valid_fun f by (move: Vtpi => /andP [_ ?]; done).
    have Vabs : valid (abs ((ui,vi) :: w')) by eauto with valid.
    have Vw : valid_fun ((ui,vi) :: w') by (move: Vabs => /andP [Vff _]; done).
    have Vt : valid (app f u) by eapply (app_tpi_valid Vtpi Vu).
    have Vui : valid ui by eapply key_valid; eauto using valid_fun_head.
    have Vvi : valid vi by eapply val_valid; eauto using valid_fun_head.
    (* Extract per-entry typing info from WT *)
    inversion WT as [| | | | | |aX wX fX j HuiAll VabsX WTtpiX| | | | | | ]; subst.
    (* app f u is itself a type *)
    have WTfu : wt (app f u) tuniv.
    { eapply (all_app_is_tuniv); eauto. }
    (* r' := app w' u is well-typed at app f u *)
    have WTr' : wt (app w' u) (app f u).
    { destruct (~~ is_nil w') eqn:Nw.
      - have WTw' : wt (abs w') (tpi a f) by eapply wt_abs_tail; eauto.
        eapply IHw'; eauto.
      - destruct w'; try done. rewrite app_nil_eq.
        by eapply wt_bot. }
    rewrite app_cons_eq.
    destruct (le ui u) eqn:LEui.
    + (* ui <= u: result is lub vi (app w' u) *)
      have WTviwi : wt vi (app f ui)
        by (eapply (HuiAll ui vi); left). 
      have LEwit : le (app f ui) (app f u)
        by (eapply le_fun_mono_arg; eauto with valid).
      have WTvit : wt vi (app f u).
      { eapply wt_le; [exact WTviwi | exact LEwit | ..].
        - eapply wt_ty_tuniv; exact WTviwi.
        - exact WTfu. }
      eapply wt_lub; eauto.
      eapply compatible_coherent_app; eauto.
      eapply le_compatible; eauto.
      eauto with valid.
    + (* ui not below u: result is app w' u *)
      exact WTr'.
Qed.

(** Same as [wt_app] but only requires the argument to be [valid] (not
    necessarily typed at the domain): a typed function maps any valid argument
    to a value well-typed at the corresponding codomain image. The argument's
    typing is only used in [wt_app] to thread the recursion, so [valid u]
    suffices throughout. *)
Lemma wt_app_valid w a f :
  wt (abs w) (tpi a f) ->
  forall u, valid u -> wt (app w u) (app f u).
Proof.
  induction w as [|[ui vi] w'].
  - move=> WT u Vu.
    move: (wt_valid_tm WT). by cbn.
  - move=> WT u Vu.
    have Vtpi : valid (tpi a f) by eauto with valid.
    have Vf : valid_fun f by (move: Vtpi => /andP [_ ?]; done).
    have Vabs : valid (abs ((ui,vi) :: w')) by eauto with valid.
    have Vw : valid_fun ((ui,vi) :: w') by (move: Vabs => /andP [Vff _]; done).
    have Vt : valid (app f u) by eapply (app_tpi_valid Vtpi Vu).
    have Vui : valid ui by eapply key_valid; eauto using valid_fun_head.
    have Vvi : valid vi by eapply val_valid; eauto using valid_fun_head.
    inversion WT as [| | | | | |aX wX fX j HuiAll VabsX WTtpiX| | | | | | ]; subst.
    have WTfu : wt (app f u) tuniv.
    { eapply (all_app_is_tuniv); eauto. }
    have WTr' : wt (app w' u) (app f u).
    { destruct (~~ is_nil w') eqn:Nw.
      - have WTw' : wt (abs w') (tpi a f) by eapply wt_abs_tail; eauto.
        eapply IHw'; eauto.
      - destruct w'; try done. rewrite app_nil_eq.
        by eapply wt_bot. }
    rewrite app_cons_eq.
    destruct (le ui u) eqn:LEui.
    + have WTviwi : wt vi (app f ui)
        by (eapply (HuiAll ui vi); left).
      have LEwit : le (app f ui) (app f u)
        by (eapply le_fun_mono_arg; eauto with valid).
      have WTvit : wt vi (app f u).
      { eapply wt_le; [exact WTviwi | exact LEwit | ..].
        - eapply wt_ty_tuniv; exact WTviwi.
        - exact WTfu. }
      eapply wt_lub; eauto.
      eapply compatible_coherent_app; eauto.
      eapply le_compatible; eauto.
      eauto with valid.
    + exact WTr'.
Qed.


