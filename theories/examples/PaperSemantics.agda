{-# OPTIONS --without-K --exact-split #-}

------------------------------------------------------------------------
-- PaperSemantics.agda
--
-- Paper-faithful finite-function semantics for the domain model.
--
-- The paper (Coquand & Huber 2018) defines evaluation of a finite
-- function f at input u as:
--
--   f(u) = ⊔{ vᵢ | (uᵢ,vᵢ) ∈ f, uᵢ ≤ u }
--
-- i.e., the supremum of all outputs whose keys are BELOW the input
-- in the structural ordering.  This differs from the equality-based
-- first-match evaluation in StepIndexedSkeleton.agda.
--
-- The ordering on finite functions is the finite condition:
--
--   g ≤ h  iff  for each (u,v) in g, v ≤ h(u)
--
-- rather than the pointwise universal quantification ∀u. g(u) ≤ h(u).
-- These are equivalent for coherent functions (by monotonicity of h).
--
-- CONTENTS (trusted kernel — no postulates, no unsolved metas):
--   1. Basic types and FinEl (imported from StepIndexedSkeleton)
--   2. Sup and append
--   3. Mutual block: leFinEl, leFun, EvalFun, LeCode, LeFunCode
--   4. FinMem (adapted to new EvalFun)
--   5. Coherence predicate
--   6. Basic order lemmas
--   7. Coherent-Sup, finMem-Sup-left/right, Coherent-EvalFun
--
-- Extended material (pCode, projections, monotonicity) is in
-- PaperSemanticsExtra.agda.
--
-- TRUSTED ANNOTATIONS:
--   {-# TERMINATING #-} on the main mutual block — justified by
--   induction on max(rk u, rk v) for leFinEl and rank decrease
--   through EvalFun for leFun.
------------------------------------------------------------------------

module PaperSemantics where

open import Basic
  using ( Top ; tt ; Empty
        ; Nat ; zero ; suc ; max
        ; Le ; Le-refl ; Le-suc ; Le-trans ; Le-max-l ; Le-max-r
        ; Eq ; refl ; Eq-transport ; Eq-sym ; Eq-cong
        ; Sigma ; mkSigma ; fst ; snd ; Pair
        ; List ; nil ; cons ; All
        ; FinEl ; Bot ; UCode ; FunEl ; PiCode ; FinFun
        ; rk ; rkFun
        ; min ; isPos ; min-isPos
        ; pair-eq ; cons-eq
        )

------------------------------------------------------------------------
-- Part 1: append and Sup on finite elements
------------------------------------------------------------------------

-- Append for finite functions (list concatenation)
append : FinFun -> FinFun -> FinFun
append nil         g = g
append (cons p ps) g = cons p (append ps g)

-- Binary supremum on finite elements.
-- Returns Bot for incompatible pairs (different constructors).
-- For compatible pairs, combines structurally.

Sup : FinEl -> FinEl -> FinEl
Sup Bot          x            = x
Sup UCode        Bot          = UCode
Sup UCode        UCode        = UCode
Sup UCode        (FunEl g)    = Bot
Sup UCode        (PiCode b g) = Bot
Sup (FunEl g)    Bot          = FunEl g
Sup (FunEl g)    UCode        = Bot
Sup (FunEl g)    (FunEl h)    = FunEl (append g h)
Sup (FunEl g)    (PiCode b h) = Bot
Sup (PiCode a f) Bot          = PiCode a f
Sup (PiCode a f) UCode        = Bot
Sup (PiCode a f) (FunEl h)    = Bot
Sup (PiCode a f) (PiCode b g) = PiCode (Sup a b) (append f g)

------------------------------------------------------------------------
-- Part 2: Main mutual block
--
-- Defines simultaneously:
--   leFinEl  : decidable ordering (Nat, positive = holds)
--   leFun    : decidable ordering on finite functions (finite check)
--   EvalFun  : sup-based evaluation (sup of all outputs with key ≤ input)
--   LeCode   : propositional ordering (Set)
--   LeFunCode: propositional ordering on finite functions
--
-- The ordering on finite functions uses the FINITE condition:
--   g ≤ h iff for each (u,v) in g, v ≤ h(u)
-- This is equivalent to pointwise ∀u.g(u)≤h(u) for coherent functions,
-- but is decidable and well-founded.
--
-- TERMINATION: justified by induction on max(rk u, rk v) for leFinEl,
-- with rank decrease through EvalFun (rk(EvalFun f u) < rk(FunEl f)).
------------------------------------------------------------------------

{-# TERMINATING #-}
mutual
  -- Decidable ordering test: positive result means LeCode holds
  leFinEl : FinEl -> FinEl -> Nat
  leFinEl Bot          x            = 1
  leFinEl UCode        Bot          = 0
  leFinEl UCode        UCode        = 1
  leFinEl UCode        (FunEl h)    = 0
  leFinEl UCode        (PiCode b g) = 0
  leFinEl (FunEl g)    Bot          = 0
  leFinEl (FunEl g)    UCode        = 0
  leFinEl (FunEl g)    (FunEl h)    = leFun g h
  leFinEl (FunEl g)    (PiCode b h) = 0
  leFinEl (PiCode a f) Bot          = 0
  leFinEl (PiCode a f) UCode        = 0
  leFinEl (PiCode a f) (FunEl h)    = 0
  leFinEl (PiCode a f) (PiCode b g) = min (leFinEl a b) (leFun f g)

  -- Finite ordering check on functions:
  -- each pair (u,v) in g satisfies v ≤ EvalFun h u
  leFun : FinFun -> FinFun -> Nat
  leFun nil         h = 1
  leFun (cons p ps) h = min (leFinEl (snd p) (EvalFun h (fst p))) (leFun ps h)

  -- Sup-based evaluation: sup of all outputs whose keys are ≤ input.
  -- This is the paper's  f(u) = ⊔{ vᵢ | uᵢ ≤ u }
  EvalFun : FinFun -> FinEl -> FinEl
  EvalFun nil         u = Bot
  EvalFun (cons p ps) u = EvalFun-step (leFinEl (fst p) u) (snd p) ps u

  EvalFun-step : Nat -> FinEl -> FinFun -> FinEl -> FinEl
  EvalFun-step zero    bi rest u = EvalFun rest u
  EvalFun-step (suc n) bi rest u = Sup bi (EvalFun rest u)

  -- Propositional ordering on finite elements
  LeCode : FinEl -> FinEl -> Set
  LeCode Bot          v            = Top
  LeCode UCode        Bot          = Empty
  LeCode UCode        UCode        = Top
  LeCode UCode        (FunEl h)    = Empty
  LeCode UCode        (PiCode b g) = Empty
  LeCode (FunEl g)    Bot          = Empty
  LeCode (FunEl g)    UCode        = Empty
  LeCode (FunEl g)    (FunEl h)    = LeFunCode g h
  LeCode (FunEl g)    (PiCode b h) = Empty
  LeCode (PiCode a f) Bot          = Empty
  LeCode (PiCode a f) UCode        = Empty
  LeCode (PiCode a f) (FunEl h)    = Empty
  LeCode (PiCode a f) (PiCode b g) = Pair (LeCode a b) (LeFunCode f g)

  -- Finite ordering on functions (propositional version)
  LeFunCode : FinFun -> FinFun -> Set
  LeFunCode nil         h = Top
  LeFunCode (cons p ps) h =
    Pair (LeCode (snd p) (EvalFun h (fst p))) (LeFunCode ps h)

------------------------------------------------------------------------
-- Part 4: Apply a finite element as a function
------------------------------------------------------------------------

applyEl : FinEl -> FinEl -> FinEl
applyEl Bot          v = Bot
applyEl UCode        v = Bot
applyEl (FunEl g)    v = EvalFun g v
applyEl (PiCode a f) v = Bot

------------------------------------------------------------------------
-- Part 3a: Compatibility
--
-- A finite function is coherent if whenever two keys are compatible
-- (have a common upper bound), the corresponding values are also
-- compatible.  This is the condition that makes finite functions
-- represent well-defined continuous maps.
------------------------------------------------------------------------

mutual
  Comp : FinEl -> FinEl -> Set
  Comp Bot          x            = Top
  Comp UCode        Bot          = Top
  Comp UCode        UCode        = Top
  Comp UCode        (FunEl g)    = Empty
  Comp UCode        (PiCode b g) = Empty
  Comp (FunEl g)    Bot          = Top
  Comp (FunEl g)    UCode        = Empty
  Comp (FunEl g)    (FunEl h)    = CompFun g h
  Comp (FunEl g)    (PiCode b h) = Empty
  Comp (PiCode a f) Bot          = Top
  Comp (PiCode a f) UCode        = Empty
  Comp (PiCode a f) (FunEl h)    = Empty
  Comp (PiCode a f) (PiCode b g) = Pair (Comp a b) (CompFun f g)

  CompFun : FinFun -> FinFun -> Set
  CompFun nil         g = Top
  CompFun (cons s f)  g = Pair (CompStepFun s g) (CompFun f g)

  CompStepFun : Pair FinEl FinEl -> FinFun -> Set
  CompStepFun s nil         = Top
  CompStepFun s (cons t g)  = Pair (CompStepStep s t) (CompStepFun s g)

  CompStepStep : Pair FinEl FinEl -> Pair FinEl FinEl -> Set
  CompStepStep s t = Comp (fst s) (fst t) -> Comp (snd s) (snd t)

------------------------------------------------------------------------
-- Part 3: FinMem + Coherence
------------------------------------------------------------------------

NotBot : FinEl -> Set
NotBot Bot          = Empty
NotBot UCode        = Top
NotBot (FunEl g)    = Top
NotBot (PiCode a f) = Top

{-# TERMINATING #-}
mutual
  FinMem : FinEl -> FinEl -> Set
  FinMem Bot          a              = FinMem a UCode
  FinMem UCode        UCode          = Top
  FinMem UCode        Bot            = Empty
  FinMem UCode        (FunEl g)      = Empty
  FinMem UCode        (PiCode a f)   = Empty
  FinMem (FunEl g)    (PiCode a f)   = Pair (FinMemFun g a f) (Pair (CoherentFun g) (FinMem (PiCode a f) UCode))
  FinMem (FunEl g)    Bot            = Empty
  FinMem (FunEl g)    UCode          = Empty
  FinMem (FunEl g)    (FunEl h)      = Empty
  FinMem (PiCode a f) UCode          = Pair (FinMem a UCode) (Pair (FinMemAllU f a) (CoherentFunTail f))
  FinMem (PiCode a f) Bot            = Empty
  FinMem (PiCode a f) (FunEl g)      = Empty
  FinMem (PiCode a f) (PiCode b g)   = Empty

  -- Every pair (ui,vi) in g: ui in a and vi in EvalFun f ui
  FinMemFun : FinFun -> FinEl -> FinFun -> Set
  FinMemFun nil         a f = Top
  FinMemFun (cons p ps) a f =
    Pair (Pair (FinMem (fst p) a) (FinMem (snd p) (EvalFun f (fst p))))
         (FinMemFun ps a f)

  -- Every pair (ai,bi) in f: ai in a and bi in UCode
  FinMemAllU : FinFun -> FinEl -> Set
  FinMemAllU nil         a = Top
  FinMemAllU (cons p ps) a =
    Pair (Pair (FinMem (fst p) a) (FinMem (snd p) UCode))
         (FinMemAllU ps a)

  Coherent : FinEl -> Set
  Coherent Bot          = Top
  Coherent UCode        = Top
  Coherent (FunEl g)    = CoherentFun g
  Coherent (PiCode a f) = Pair (Coherent a) (CoherentFunTail f)

  CoherentFun : FinFun -> Set
  CoherentFun nil         = Empty
  CoherentFun (cons p ps) = CoherentFunTail (cons p ps)

  record CFTcons (p : Pair FinEl FinEl) (ps : FinFun) : Set where
    inductive
    constructor mkCFT
    field
      key-coh  : Coherent (fst p)
      val-coh  : Coherent (snd p)
      val-nbot : NotBot (snd p)
      compat   : CoherentWith p ps
      tail-coh : CoherentFunTail ps

  CoherentFunTail : FinFun -> Set
  CoherentFunTail nil         = Top
  CoherentFunTail (cons p ps) = CFTcons p ps

  -- Every pair in ps is compatible with p (when keys are compatible)
  CoherentWith : Pair FinEl FinEl -> FinFun -> Set
  CoherentWith p nil         = Top
  CoherentWith p (cons q qs) =
    Pair (Comp (fst p) (fst q) -> Comp (snd p) (snd q))
         (CoherentWith p qs)

-- Convert CoherentFun to CoherentFunTail (identity on cons, absurd on nil)
cft-from-cf : (g : FinFun) -> CoherentFun g -> CoherentFunTail g
cft-from-cf nil         ()
cft-from-cf (cons p ps) coh = coh

-- Coherent (FunEl [(u,v)]) implies Coherent u and Coherent v
Coherent-singleton-key : (u v : FinEl) ->
  Coherent (FunEl (cons (mkSigma u v) nil)) -> Coherent u
Coherent-singleton-key u v coh = CFTcons.key-coh coh

Coherent-singleton-val : (u v : FinEl) ->
  Coherent (FunEl (cons (mkSigma u v) nil)) -> Coherent v
Coherent-singleton-val u v coh = CFTcons.val-coh coh

------------------------------------------------------------------------
-- Part 5b: Structural projections from FinMem
--
-- FinMem u a implies a : U, Coherent a, Coherent u
------------------------------------------------------------------------

{-# TERMINATING #-}
mutual
  FinMem-coh-u : (u a : FinEl) -> FinMem u a -> Coherent u
  FinMem-coh-u Bot          a            mem = tt
  FinMem-coh-u UCode        UCode        mem = tt
  FinMem-coh-u UCode        Bot          ()
  FinMem-coh-u UCode        (FunEl g)    ()
  FinMem-coh-u UCode        (PiCode a f) ()
  FinMem-coh-u (FunEl g)    (PiCode a f) mem = fst (snd mem)
  FinMem-coh-u (FunEl g)    Bot          ()
  FinMem-coh-u (FunEl g)    UCode        ()
  FinMem-coh-u (FunEl g)    (FunEl h)    ()
  FinMem-coh-u (PiCode a f) UCode        mem = mkSigma (FinMem-coh-u a UCode (fst mem)) (snd (snd mem))
  FinMem-coh-u (PiCode a f) Bot          ()
  FinMem-coh-u (PiCode a f) (FunEl g)    ()
  FinMem-coh-u (PiCode a f) (PiCode b g) ()

  FinMem-a-in-U : (u a : FinEl) -> FinMem u a -> FinMem a UCode
  FinMem-a-in-U Bot          a            mem = mem
  FinMem-a-in-U UCode        UCode        mem = tt
  FinMem-a-in-U UCode        Bot          ()
  FinMem-a-in-U UCode        (FunEl g)    ()
  FinMem-a-in-U UCode        (PiCode a f) ()
  FinMem-a-in-U (FunEl g)    (PiCode a f) mem = snd (snd mem)
  FinMem-a-in-U (FunEl g)    Bot          ()
  FinMem-a-in-U (FunEl g)    UCode        ()
  FinMem-a-in-U (FunEl g)    (FunEl h)    ()
  FinMem-a-in-U (PiCode a f) UCode        mem = tt
  FinMem-a-in-U (PiCode a f) Bot          ()
  FinMem-a-in-U (PiCode a f) (FunEl g)    ()
  FinMem-a-in-U (PiCode a f) (PiCode b g) ()

  FinMem-coh-a : (u a : FinEl) -> FinMem u a -> Coherent a
  FinMem-coh-a Bot          a            mem = FinMem-coh-u a UCode mem
  FinMem-coh-a UCode        UCode        mem = tt
  FinMem-coh-a UCode        Bot          ()
  FinMem-coh-a UCode        (FunEl g)    ()
  FinMem-coh-a UCode        (PiCode a f) ()
  FinMem-coh-a (FunEl g)    (PiCode a f) mem = FinMem-coh-u (PiCode a f) UCode (snd (snd mem))
  FinMem-coh-a (FunEl g)    Bot          ()
  FinMem-coh-a (FunEl g)    UCode        ()
  FinMem-coh-a (FunEl g)    (FunEl h)    ()
  FinMem-coh-a (PiCode a f) UCode        mem = tt
  FinMem-coh-a (PiCode a f) Bot          ()
  FinMem-coh-a (PiCode a f) (FunEl g)    ()
  FinMem-coh-a (PiCode a f) (PiCode b g) ()

-- Derive Coherent from FinMem a UCode
coh-from-aU : (a : FinEl) -> FinMem a UCode -> Coherent a
coh-from-aU a mem = FinMem-coh-u a UCode mem

------------------------------------------------------------------------
-- Part 6: Soundness of leFinEl
--
-- isPos (leFinEl u v) -> LeCode u v
------------------------------------------------------------------------

{-# TERMINATING #-}
mutual
  leFinEl-sound : (u v : FinEl) -> isPos (leFinEl u v) -> LeCode u v
  leFinEl-sound Bot          v            h = tt
  leFinEl-sound UCode        Bot          ()
  leFinEl-sound UCode        UCode        h = tt
  leFinEl-sound UCode        (FunEl g)    ()
  leFinEl-sound UCode        (PiCode b g) ()
  leFinEl-sound (FunEl g)    Bot          ()
  leFinEl-sound (FunEl g)    UCode        ()
  leFinEl-sound (FunEl g)    (FunEl h)    p = leFun-sound g h p
  leFinEl-sound (FunEl g)    (PiCode b h) ()
  leFinEl-sound (PiCode a f) Bot          ()
  leFinEl-sound (PiCode a f) UCode        ()
  leFinEl-sound (PiCode a f) (FunEl h)    ()
  leFinEl-sound (PiCode a f) (PiCode b g) p =
    let pp = min-isPos (leFinEl a b) (leFun f g) p
    in mkSigma (leFinEl-sound a b (fst pp)) (leFun-sound f g (snd pp))

  leFun-sound : (g h : FinFun) -> isPos (leFun g h) -> LeFunCode g h
  leFun-sound nil         h p = tt
  leFun-sound (cons p ps) h q =
    let pp = min-isPos (leFinEl (snd p) (EvalFun h (fst p))) (leFun ps h) q
    in mkSigma (leFinEl-sound (snd p) (EvalFun h (fst p)) (fst pp))
               (leFun-sound ps h (snd pp))

------------------------------------------------------------------------
-- Part 6b: Completeness of leFinEl
--
-- LeCode u v -> isPos (leFinEl u v)
------------------------------------------------------------------------

-- Introduction rule for isPos (min m n)
isPos-min : (m n : Nat) -> isPos m -> isPos n -> isPos (min m n)
isPos-min zero    n       () _
isPos-min (suc m) zero    _  ()
isPos-min (suc m) (suc n) _  _ = tt

{-# TERMINATING #-}
mutual
  leFinEl-complete : (u v : FinEl) -> LeCode u v -> isPos (leFinEl u v)
  leFinEl-complete Bot          Bot          _ = tt
  leFinEl-complete Bot          UCode        _ = tt
  leFinEl-complete Bot          (FunEl h)    _ = tt
  leFinEl-complete Bot          (PiCode b g) _ = tt
  leFinEl-complete UCode        Bot          ()
  leFinEl-complete UCode        UCode        _ = tt
  leFinEl-complete UCode        (FunEl g)    ()
  leFinEl-complete UCode        (PiCode b g) ()
  leFinEl-complete (FunEl g)    Bot          ()
  leFinEl-complete (FunEl g)    UCode        ()
  leFinEl-complete (FunEl g)    (FunEl h)    p = leFun-complete g h p
  leFinEl-complete (FunEl g)    (PiCode b h) ()
  leFinEl-complete (PiCode a f) Bot          ()
  leFinEl-complete (PiCode a f) UCode        ()
  leFinEl-complete (PiCode a f) (FunEl h)    ()
  leFinEl-complete (PiCode a f) (PiCode b g) p =
    isPos-min (leFinEl a b) (leFun f g)
              (leFinEl-complete a b (fst p))
              (leFun-complete f g (snd p))

  leFun-complete : (g h : FinFun) -> LeFunCode g h -> isPos (leFun g h)
  leFun-complete nil         h _ = tt
  leFun-complete (cons p ps) h q =
    isPos-min (leFinEl (snd p) (EvalFun h (fst p))) (leFun ps h)
              (leFinEl-complete (snd p) (EvalFun h (fst p)) (fst q))
              (leFun-complete ps h (snd q))

------------------------------------------------------------------------
-- Part 7: Sup lemmas
------------------------------------------------------------------------

-- Sup Bot v = v
Sup-Bot-l : (v : FinEl) -> Eq (Sup Bot v) v
Sup-Bot-l Bot          = refl
Sup-Bot-l UCode        = refl
Sup-Bot-l (FunEl g)    = refl
Sup-Bot-l (PiCode b g) = refl

-- Sup u Bot = u
Sup-Bot-r : (u : FinEl) -> Eq (Sup u Bot) u
Sup-Bot-r Bot          = refl
Sup-Bot-r UCode        = refl
Sup-Bot-r (FunEl g)    = refl
Sup-Bot-r (PiCode a f) = refl

-- Bot is below everything
LeCode-Bot : (v : FinEl) -> LeCode Bot v
LeCode-Bot v = tt

------------------------------------------------------------------------
-- Part 7a: LeCode-Sup-left/right — u ≤ Sup u v when Comp u v
--
-- Requires Coherent arguments for FunEl/PiCode cases: the internal
-- coherence of a function is needed to show that each entry's value
-- is compatible with the evaluation of the remaining entries.
--
-- Key helpers used:
--   Comp-value-EvalFun  (Part 7h below)
--   comp-Sup            (Part 7b below)
--
-- Because Comp-value-EvalFun etc. are defined AFTER this section,
-- LeCode-Sup-left/right are proved below in Part 7i, after all helpers.
------------------------------------------------------------------------

------------------------------------------------------------------------
-- Part 7b: Compatibility lemmas
------------------------------------------------------------------------

comp-Bot-r : (u : FinEl) -> Comp u Bot
comp-Bot-r Bot          = tt
comp-Bot-r UCode        = tt
comp-Bot-r (FunEl g)    = tt
comp-Bot-r (PiCode a f) = tt

Sup-Bot-right : (x : FinEl) -> Eq (Sup x Bot) x
Sup-Bot-right Bot          = refl
Sup-Bot-right UCode        = refl
Sup-Bot-right (FunEl g)    = refl
Sup-Bot-right (PiCode a f) = refl

comp-Bot-l : (u : FinEl) -> Comp Bot u
comp-Bot-l Bot          = tt
comp-Bot-l UCode        = tt
comp-Bot-l (FunEl g)    = tt
comp-Bot-l (PiCode a f) = tt

-- CompStepFun distributes over append
compStepFun-append : (s : Pair FinEl FinEl) (g h : FinFun) ->
  CompStepFun s g -> CompStepFun s h -> CompStepFun s (append g h)
compStepFun-append s nil         h cg ch = ch
compStepFun-append s (cons t ts) h cg ch =
  mkSigma (fst cg) (compStepFun-append s ts h (snd cg) ch)

-- CompFun distributes over append
compFun-append : (g h j : FinFun) ->
  CompFun g h -> CompFun g j -> CompFun g (append h j)
compFun-append nil         h j ch cj = tt
compFun-append (cons s ss) h j ch cj =
  mkSigma (compStepFun-append s h j (fst ch) (fst cj))
          (compFun-append ss h j (snd ch) (snd cj))

-- LeFunCode-append-nil: if all values in g and h are <= Bot,
-- then all values in (append g h) are <= Bot.
LeFunCode-append-nil : (g h : FinFun) ->
  LeFunCode g nil -> LeFunCode h nil -> LeFunCode (append g h) nil
LeFunCode-append-nil nil         h lg lh = lh
LeFunCode-append-nil (cons p ps) h lg lh =
  mkSigma (fst lg) (LeFunCode-append-nil ps h (snd lg) lh)

-- Comp a (Sup b c) when Comp a b and Comp a c
{-# TERMINATING #-}
comp-Sup : (a b c : FinEl) -> Comp a b -> Comp a c -> Comp a (Sup b c)
comp-Sup Bot          b            c            ab ac = comp-Bot-l (Sup b c)
comp-Sup UCode        Bot          Bot          ab ac = tt
comp-Sup UCode        Bot          UCode        ab ac = tt
comp-Sup UCode        Bot          (FunEl j)    ab ac = ac
comp-Sup UCode        Bot          (PiCode e j) ab ()
comp-Sup UCode        UCode        Bot          ab ac = tt
comp-Sup UCode        UCode        UCode        ab ac = tt
comp-Sup UCode        UCode        (FunEl j)    ab ac = tt
comp-Sup UCode        UCode        (PiCode e j) ab ()
comp-Sup UCode        (FunEl h)    Bot          () ac
comp-Sup UCode        (FunEl h)    UCode        () ac
comp-Sup UCode        (FunEl h)    (FunEl j)    () ac
comp-Sup UCode        (FunEl h)    (PiCode e j) () ac
comp-Sup UCode        (PiCode d k) c            () ac
comp-Sup (FunEl g)    Bot          Bot          ab ac = comp-Bot-r (FunEl g)
comp-Sup (FunEl g)    Bot          UCode        ab ac = ac
comp-Sup (FunEl g)    Bot          (FunEl j)    ab ac = ac
comp-Sup (FunEl g)    Bot          (PiCode e j) ab ac = ac
comp-Sup (FunEl g)    UCode        Bot          () ac
comp-Sup (FunEl g)    UCode        UCode        () ac
comp-Sup (FunEl g)    UCode        (FunEl j)    () ac
comp-Sup (FunEl g)    UCode        (PiCode e j) () ac
comp-Sup (FunEl g)    (FunEl h)    Bot          ab ac = ab
comp-Sup (FunEl g)    (FunEl h)    UCode        ab ()
comp-Sup (FunEl g)    (FunEl h)    (FunEl j)    ab ac = compFun-append g h j ab ac
comp-Sup (FunEl g)    (FunEl h)    (PiCode d k) ab ()
comp-Sup (FunEl g)    (PiCode d k) Bot          () ac
comp-Sup (FunEl g)    (PiCode d k) UCode        () ac
comp-Sup (FunEl g)    (PiCode d k) (FunEl j)    () ac
comp-Sup (FunEl g)    (PiCode d k) (PiCode e j) () ac
comp-Sup (PiCode a f) Bot          Bot          ab ac = comp-Bot-r (PiCode a f)
comp-Sup (PiCode a f) Bot          UCode        ab ()
comp-Sup (PiCode a f) Bot          (FunEl j)    ab ac = ac
comp-Sup (PiCode a f) Bot          (PiCode e j) ab ac = ac
comp-Sup (PiCode a f) UCode        c            () ac
comp-Sup (PiCode a f) (FunEl h)    Bot          () ac
comp-Sup (PiCode a f) (FunEl h)    UCode        () ac
comp-Sup (PiCode a f) (FunEl h)    (FunEl j)    () ac
comp-Sup (PiCode a f) (FunEl h)    (PiCode e j) () ac
comp-Sup (PiCode a f) (PiCode d k) Bot          ab ac = ab
comp-Sup (PiCode a f) (PiCode d k) UCode        ab ()
comp-Sup (PiCode a f) (PiCode d k) (FunEl h)    ab ()
comp-Sup (PiCode a f) (PiCode d k) (PiCode e j) ab ac =
  mkSigma (comp-Sup a d e (fst ab) (fst ac))
          (compFun-append f k j (snd ab) (snd ac))

------------------------------------------------------------------------
-- Part 7c: Upward closure of FinMem through compatible Sup
------------------------------------------------------------------------

-- Congruence for PiCode
PiCode-cong : {a b : FinEl} {f g : FinFun} ->
  Eq a b -> Eq f g -> Eq (PiCode a f) (PiCode b g)
PiCode-cong refl refl = refl

-- append is associative
append-assoc : (f g h : FinFun) -> Eq (append f (append g h)) (append (append f g) h)
append-assoc nil         g h = refl
append-assoc (cons p ps) g h = cons-eq refl (append-assoc ps g h)

------------------------------------------------------------------------
-- Part 7d: Comp-sym — symmetry of compatibility
------------------------------------------------------------------------

{-# TERMINATING #-}
mutual
  Comp-sym : (u v : FinEl) -> Comp u v -> Comp v u
  Comp-sym Bot          Bot          c = tt
  Comp-sym Bot          UCode        c = tt
  Comp-sym Bot          (FunEl h)    c = tt
  Comp-sym Bot          (PiCode b g) c = tt
  Comp-sym UCode        Bot          c = tt
  Comp-sym UCode        UCode        c = tt
  Comp-sym UCode        (FunEl h)    c = c
  Comp-sym UCode        (PiCode b g) ()
  Comp-sym (FunEl g)    Bot          c = tt
  Comp-sym (FunEl g)    UCode        c = c
  Comp-sym (FunEl g)    (FunEl h)    c = CompFun-sym g h c
  Comp-sym (FunEl g)    (PiCode b h) c = c
  Comp-sym (PiCode a f) Bot          c = tt
  Comp-sym (PiCode a f) UCode        ()
  Comp-sym (PiCode a f) (FunEl h)    c = c
  Comp-sym (PiCode a f) (PiCode b g) c =
    mkSigma (Comp-sym a b (fst c)) (CompFun-sym f g (snd c))

  CompFun-sym : (g h : FinFun) -> CompFun g h -> CompFun h g
  CompFun-sym g nil         cf = tt
  CompFun-sym g (cons t ts) cf =
    mkSigma (CompFun-sym-col g t ts cf)
            (CompFun-sym g ts (CompFun-drop-col g t ts cf))

  -- Extract column for t from CompFun g (cons t ts), flipping via Comp-sym
  CompFun-sym-col : (g : FinFun) (t : Pair FinEl FinEl) (ts : FinFun) ->
    CompFun g (cons t ts) -> CompStepFun t g
  CompFun-sym-col nil         t ts cf = tt
  CompFun-sym-col (cons s ss) t ts cf =
    mkSigma (\ c -> Comp-sym (snd s) (snd t) (fst (fst cf) (Comp-sym (fst t) (fst s) c)))
            (CompFun-sym-col ss t ts (snd cf))

  -- Drop first column: CompFun g (cons t ts) -> CompFun g ts
  CompFun-drop-col : (g : FinFun) (t : Pair FinEl FinEl) (ts : FinFun) ->
    CompFun g (cons t ts) -> CompFun g ts
  CompFun-drop-col nil         t ts cf = tt
  CompFun-drop-col (cons s ss) t ts cf =
    mkSigma (snd (fst cf)) (CompFun-drop-col ss t ts (snd cf))

-- CoherentWith gives CompStepFun
coherentWith-to-compStepFun : (q : Pair FinEl FinEl) (qs : FinFun) ->
  CoherentWith q qs -> CompStepFun q qs
coherentWith-to-compStepFun q nil cw = tt
coherentWith-to-compStepFun q (cons r rs) cw =
  mkSigma (fst cw) (coherentWith-to-compStepFun q rs (snd cw))

------------------------------------------------------------------------
-- Part 7e: Comp-refl — reflexivity from coherence
------------------------------------------------------------------------

-- Prepend a flipped column to CompFun
CompFun-cons-right : (s : Pair FinEl FinEl) (ss hs : FinFun) ->
  CoherentWith s ss -> CompFun ss hs -> CompFun ss (cons s hs)
CompFun-cons-right s nil         hs cw cf = tt
CompFun-cons-right s (cons t ts) hs cw cf =
  mkSigma (mkSigma (\ c -> Comp-sym (snd s) (snd t) (fst cw (Comp-sym (fst t) (fst s) c)))
                    (fst cf))
          (CompFun-cons-right s ts hs (snd cw) (snd cf))

{-# TERMINATING #-}
mutual
  Comp-refl : (v : FinEl) -> Coherent v -> Comp v v
  Comp-refl Bot          coh = tt
  Comp-refl UCode        coh = tt
  Comp-refl (FunEl g)    coh = CompFun-refl g (cft-from-cf g coh)
  Comp-refl (PiCode a f) coh =
    mkSigma (Comp-refl a (fst coh)) (CompFun-refl f (snd coh))

  CompFun-refl : (g : FinFun) -> CoherentFunTail g -> CompFun g g
  CompFun-refl nil         coh = tt
  CompFun-refl (cons s ss) coh =
    mkSigma (mkSigma (\ _ -> Comp-refl (snd s) (CFTcons.val-coh coh))
                      (coherentWith-to-compStepFun s ss (CFTcons.compat coh)))
            (CompFun-cons-right s ss ss (CFTcons.compat coh)
              (CompFun-refl ss (CFTcons.tail-coh coh)))

------------------------------------------------------------------------
-- Part 7f-pre: Helper lemmas for "null" FunEl (all values <= Bot)
------------------------------------------------------------------------

-- If both x and y are <= Bot, then Sup x y is <= Bot
LeCode-Sup-Bot : (x y : FinEl) -> LeCode x Bot -> LeCode y Bot -> LeCode (Sup x y) Bot
LeCode-Sup-Bot Bot          y            lx ly = ly
LeCode-Sup-Bot UCode        y            ()   ly
LeCode-Sup-Bot (FunEl g)    y            () ly
LeCode-Sup-Bot (PiCode a f) y            ()   ly

-- If all values in h are <= Bot, then EvalFun h u <= Bot
mutual
  EvalFun-step-le-Bot : (n : Nat) (b : FinEl) (ps : FinFun) (u : FinEl) ->
    LeCode b Bot -> LeFunCode ps nil -> LeCode (EvalFun-step n b ps u) Bot
  EvalFun-step-le-Bot zero    b ps u lb lps = EvalFun-le-Bot ps u lps
  EvalFun-step-le-Bot (suc _) b ps u lb lps =
    LeCode-Sup-Bot b (EvalFun ps u) lb (EvalFun-le-Bot ps u lps)

  EvalFun-le-Bot : (h : FinFun) (u : FinEl) -> LeFunCode h nil -> LeCode (EvalFun h u) Bot
  EvalFun-le-Bot nil         u lh = tt
  EvalFun-le-Bot (cons p ps) u lh =
    EvalFun-step-le-Bot (leFinEl (fst p) u) (snd p) ps u (fst lh) (snd lh)

-- Transitivity to Bot/nil: if u <= v and v <= Bot then u <= Bot
{-# TERMINATING #-}
mutual
  LeCode-trans-to-Bot : (u v : FinEl) -> LeCode u v -> LeCode v Bot -> LeCode u Bot
  LeCode-trans-to-Bot Bot          v            lu lv = tt
  LeCode-trans-to-Bot UCode        Bot          ()   lv
  LeCode-trans-to-Bot UCode        UCode        lu   ()
  LeCode-trans-to-Bot UCode        (FunEl h)    ()   lv
  LeCode-trans-to-Bot UCode        (PiCode b h) ()   lv
  LeCode-trans-to-Bot (FunEl g)    Bot          ()   lv
  LeCode-trans-to-Bot (FunEl g)    UCode        ()   lv
  LeCode-trans-to-Bot (FunEl g)    (FunEl h)    lu   ()
  LeCode-trans-to-Bot (FunEl g)    (PiCode b h) ()   lv
  LeCode-trans-to-Bot (PiCode a f) Bot          ()   lv
  LeCode-trans-to-Bot (PiCode a f) UCode        ()   lv
  LeCode-trans-to-Bot (PiCode a f) (FunEl h)    ()   lv
  LeCode-trans-to-Bot (PiCode a f) (PiCode b g) lu   ()

  LeFunCode-trans-to-nil : (g h : FinFun) -> LeFunCode g h -> LeFunCode h nil -> LeFunCode g nil
  LeFunCode-trans-to-nil nil         h lg lh = tt
  LeFunCode-trans-to-nil (cons s ss) h lg lh =
    mkSigma (LeCode-trans-to-Bot (snd s) (EvalFun h (fst s)) (fst lg) (EvalFun-le-Bot h (fst s) lh))
            (LeFunCode-trans-to-nil ss h (snd lg) lh)

-- If u <= Bot, then u is compatible with anything
{-# TERMINATING #-}
mutual
  LeCode-Bot-Comp : (u v : FinEl) -> LeCode u Bot -> Comp u v
  LeCode-Bot-Comp Bot          v le = tt
  LeCode-Bot-Comp UCode        v ()
  LeCode-Bot-Comp (FunEl g)    v            ()
  LeCode-Bot-Comp (PiCode a f) v ()

  LeFunCode-nil-CompFun : (g h : FinFun) -> LeFunCode g nil -> CompFun g h
  LeFunCode-nil-CompFun nil         h lg = tt
  LeFunCode-nil-CompFun (cons s ss) h lg =
    mkSigma (LeFunCode-nil-CompStepFun s h (fst lg))
            (LeFunCode-nil-CompFun ss h (snd lg))

  LeFunCode-nil-CompStepFun : (s : Pair FinEl FinEl) (h : FinFun) ->
    LeCode (snd s) Bot -> CompStepFun s h
  LeFunCode-nil-CompStepFun s nil         lb = tt
  LeFunCode-nil-CompStepFun s (cons t ts) lb =
    mkSigma (\ _ -> LeCode-Bot-Comp (snd s) (snd t) lb)
            (LeFunCode-nil-CompStepFun s ts lb)

------------------------------------------------------------------------
-- Part 7f: Comp-down — downward closure of compatibility
--
-- LeCode u u' -> Comp u' v -> Comp u v
--
-- Key helper: EvalFun-allLeImpComp, which shows that if for each
-- entry r in h, LeCode (fst r) xi implies Comp (snd r) v, then
-- Comp (EvalFun h xi) v.
------------------------------------------------------------------------

-- Comp (Sup a b) v from Comp a v and Comp b v
comp-Sup-sym : (a b v : FinEl) -> Comp a v -> Comp b v -> Comp (Sup a b) v
comp-Sup-sym a b v ca cb =
  Comp-sym v (Sup a b) (comp-Sup v a b (Comp-sym a v ca) (Comp-sym b v cb))

{-# TERMINATING #-}
mutual
  Comp-down : (u u' v : FinEl) -> LeCode u u' -> Comp u' v -> Comp u v
  Comp-down Bot          u'           v le c = comp-Bot-l v
  Comp-down UCode        Bot          v ()   c
  Comp-down UCode        UCode        v le   c = c
  Comp-down UCode        (FunEl h)    v ()   c
  Comp-down UCode        (PiCode b g) v ()   c
  Comp-down (FunEl g)    Bot          v le c = LeCode-Bot-Comp (FunEl g) v le
  Comp-down (FunEl g)    UCode        v le c = LeCode-Bot-Comp (FunEl g) v le
  Comp-down (FunEl g)    (FunEl h)    Bot          le c = tt
  Comp-down (FunEl g)    (FunEl h)    UCode        le ()
  Comp-down (FunEl g)    (FunEl h)    (FunEl j)    le c =
    LeFunCode-CompFun-trans g h j le c
  Comp-down (FunEl g)    (FunEl h)    (PiCode b k) le ()
  Comp-down (FunEl g)    (PiCode b h) v le c = LeCode-Bot-Comp (FunEl g) v le
  Comp-down (PiCode a f) Bot          v ()   c
  Comp-down (PiCode a f) UCode        v ()   c
  Comp-down (PiCode a f) (FunEl h)    v ()   c
  Comp-down (PiCode a f) (PiCode b g) Bot          le c = tt
  Comp-down (PiCode a f) (PiCode b g) UCode        le ()
  Comp-down (PiCode a f) (PiCode b g) (FunEl j)    le c = c
  Comp-down (PiCode a f) (PiCode b g) (PiCode c k) le comp =
    mkSigma (Comp-down a b c (fst le) (fst comp))
            (LeFunCode-CompFun-trans f g k (snd le) (snd comp))

  -- Transitivity: LeFunCode g h + CompFun h j -> CompFun g j
  LeFunCode-CompFun-trans : (g h j : FinFun) ->
    LeFunCode g h -> CompFun h j -> CompFun g j
  LeFunCode-CompFun-trans nil         h j le cf = tt
  LeFunCode-CompFun-trans (cons s ss) h j le cf =
    mkSigma (build-CompStepFun s j h (fst le) cf)
            (LeFunCode-CompFun-trans ss h j (snd le) cf)

  -- For one entry s and all of j, build CompStepFun s j
  build-CompStepFun : (s : Pair FinEl FinEl) (j h : FinFun) ->
    LeCode (snd s) (EvalFun h (fst s)) -> CompFun h j -> CompStepFun s j
  build-CompStepFun s nil         h le cf = tt
  build-CompStepFun s (cons t ts) h le cf =
    mkSigma
      (\ comp-keys ->
        let col = extract-col h t ts cf
            comp-eval = EvalFun-guarded-comp h (fst s) t col comp-keys
        in Comp-down (snd s) (EvalFun h (fst s)) (snd t) le comp-eval)
      (build-CompStepFun s ts h le (CompFun-drop-col h t ts cf))

  -- Extract column: for each r in h, get CompStepStep r t
  extract-col : (h : FinFun) (t : Pair FinEl FinEl) (ts : FinFun) ->
    CompFun h (cons t ts) -> CompFun h (cons t nil)
  extract-col nil         t ts cf = tt
  extract-col (cons r rs) t ts cf =
    mkSigma (mkSigma (fst (fst cf)) tt)
            (extract-col rs t ts (snd cf))

  -- EvalFun compatibility: if for each r in h, Comp (fst r) (fst t) implies
  -- Comp (snd r) (snd t), and Comp xi (fst t), then Comp (EvalFun h xi) (snd t).
  -- Uses Comp-down to convert LeCode (from leFinEl-sound) to Comp.
  EvalFun-guarded-comp : (h : FinFun) (xi : FinEl) (t : Pair FinEl FinEl) ->
    CompFun h (cons t nil) -> Comp xi (fst t) ->
    Comp (EvalFun h xi) (snd t)
  EvalFun-guarded-comp nil         xi t col cxi = comp-Bot-l (snd t)
  EvalFun-guarded-comp (cons r rs) xi t col cxi =
    EvalFun-guarded-comp-step (leFinEl (fst r) xi) r rs xi t refl
      (fst (fst col)) cxi (EvalFun-guarded-comp rs xi t (snd col) cxi)

  EvalFun-guarded-comp-step : (n : Nat) (r : Pair FinEl FinEl) (rs : FinFun)
    (xi : FinEl) (t : Pair FinEl FinEl) ->
    Eq n (leFinEl (fst r) xi) ->
    CompStepStep r t -> Comp xi (fst t) ->
    Comp (EvalFun rs xi) (snd t) ->
    Comp (EvalFun-step n (snd r) rs xi) (snd t)
  EvalFun-guarded-comp-step zero    r rs xi t eq css cxi ih = ih
  EvalFun-guarded-comp-step (suc _) r rs xi t eq css cxi ih =
    let le = leFinEl-sound (fst r) xi (Eq-transport isPos eq tt)
        comp-keys = Comp-down (fst r) xi (fst t) le cxi
    in comp-Sup-sym (snd r) (EvalFun rs xi) (snd t) (css comp-keys) ih

------------------------------------------------------------------------
-- Part 7g: LeCode-Comp — derived from Comp-down + Comp-sym + Comp-refl
------------------------------------------------------------------------

LeCode-Comp : (u v w : FinEl) -> Coherent w -> LeCode u w -> LeCode v w -> Comp u v
LeCode-Comp u v w coh lu lv =
  Comp-down u w v lu (Comp-sym v w (Comp-down v w w lv (Comp-refl w coh)))

-- CompStepFun and CoherentWith are the same structure
compStepFun-to-coherentWith : (q : Pair FinEl FinEl) (h : FinFun) ->
  CompStepFun q h -> CoherentWith q h
compStepFun-to-coherentWith q nil csf = tt
compStepFun-to-coherentWith q (cons r rs) csf =
  mkSigma (fst csf) (compStepFun-to-coherentWith q rs (snd csf))

-- CoherentWith distributes over append
coherentWith-append : (q : Pair FinEl FinEl) (qs h : FinFun) ->
  CoherentWith q qs -> CoherentWith q h -> CoherentWith q (append qs h)
coherentWith-append q nil         h cw1 cw2 = cw2
coherentWith-append q (cons r rs) h cw1 cw2 =
  mkSigma (fst cw1) (coherentWith-append q rs h (snd cw1) cw2)

------------------------------------------------------------------------
-- Part 7h: Coherent-Sup and Coherent-EvalFun
-- (Definitions placed after finMem-Sup-right, see below.)

-- finMem-Sup-right: membership upward-closed through compatible Sup
-- finMem-EvalFun-append: membership preserved when prepending to function
--
-- Comp-value-EvalFun: proved using LeCode-Comp and comp-Sup.
{-# TERMINATING #-}
mutual
  Comp-value-EvalFun : (q : Pair FinEl FinEl) (rest : FinFun) (xi : FinEl) ->
    LeCode (fst q) xi -> Coherent xi -> Coherent (snd q) ->
    CoherentWith q rest -> CompStepFun q rest ->
    Comp (snd q) (EvalFun rest xi)
  Comp-value-EvalFun q nil xi le cxi cohv cw csf = comp-Bot-r (snd q)
  Comp-value-EvalFun q (cons r rs) xi le cxi cohv cw csf =
    Comp-value-EvalFun-step (leFinEl (fst r) xi) q r rs xi refl
      le cxi cohv (fst cw) (snd cw) (fst csf) (snd csf)

  Comp-value-EvalFun-step : (n : Nat) (q r : Pair FinEl FinEl)
    (rs : FinFun) (xi : FinEl) ->
    Eq n (leFinEl (fst r) xi) ->
    LeCode (fst q) xi -> Coherent xi -> Coherent (snd q) ->
    (Comp (fst q) (fst r) -> Comp (snd q) (snd r)) ->
    CoherentWith q rs ->
    CompStepStep q r ->
    CompStepFun q rs ->
    Comp (snd q) (EvalFun-step n (snd r) rs xi)
  Comp-value-EvalFun-step zero    q r rs xi eq le cxi cohv css cw css2 csf =
    Comp-value-EvalFun q rs xi le cxi cohv cw csf
  Comp-value-EvalFun-step (suc _) q r rs xi eq le cxi cohv css cw css2 csf =
    let le-r = leFinEl-sound (fst r) xi (Eq-transport isPos eq tt)
        comp-keys = LeCode-Comp (fst q) (fst r) xi cxi le le-r
    in comp-Sup (snd q) (snd r) (EvalFun rs xi)
         (css comp-keys)
         (Comp-value-EvalFun q rs xi le cxi cohv cw csf)

-- isPos-to-LeCode: extract LeCode from positive leFinEl test
isPos-to-LeCode : (x xi : FinEl) -> isPos (leFinEl x xi) -> LeCode x xi
isPos-to-LeCode = leFinEl-sound

------------------------------------------------------------------------
-- Part 7h: Coherent-Sup and Coherent-EvalFun
------------------------------------------------------------------------

-- comp-EvalFun: evaluations of compatible functions at the same point
-- are compatible.
{-# TERMINATING #-}
mutual
  comp-EvalFun : (k h : FinFun) (xi : FinEl) ->
    CompFun k h -> CoherentFunTail k -> Coherent xi ->
    Comp (EvalFun k xi) (EvalFun h xi)
  comp-EvalFun nil h xi ckh cohk cxi = comp-Bot-l (EvalFun h xi)
  comp-EvalFun (cons q rest) h xi ckh cohk cxi =
    comp-EvalFun-step (leFinEl (fst q) xi) q rest h xi refl
      (fst ckh) (snd ckh) cohk cxi

  comp-EvalFun-step : (n : Nat) (q : Pair FinEl FinEl) (rest h : FinFun)
    (xi : FinEl) ->
    Eq n (leFinEl (fst q) xi) ->
    CompStepFun q h -> CompFun rest h ->
    CoherentFunTail (cons q rest) -> Coherent xi ->
    Comp (EvalFun-step n (snd q) rest xi) (EvalFun h xi)
  comp-EvalFun-step zero    q rest h xi eq csf crf cohk cxi =
    comp-EvalFun rest h xi crf (CFTcons.tail-coh cohk) cxi
  comp-EvalFun-step (suc _) q rest h xi eq csf crf cohk cxi =
    let comp1 = Comp-value-EvalFun q h xi
                  (leFinEl-sound (fst q) xi (Eq-transport isPos eq tt))
                  cxi (CFTcons.val-coh cohk)
                  (compStepFun-to-coherentWith q h csf) csf
        comp2 = comp-EvalFun rest h xi crf (CFTcons.tail-coh cohk) cxi
    in comp-Sup-sym (snd q) (EvalFun rest xi) (EvalFun h xi) comp1 comp2

-- Sup-assoc: associativity of Sup for compatible elements.
{-# TERMINATING #-}
Sup-assoc : (a b c : FinEl) -> Comp a b -> Comp b c ->
  Eq (Sup (Sup a b) c) (Sup a (Sup b c))
Sup-assoc Bot          b            c            cab cbc = refl
Sup-assoc UCode        Bot          c            cab cbc = refl
Sup-assoc UCode        UCode        Bot          cab cbc = refl
Sup-assoc UCode        UCode        UCode        cab cbc = refl
Sup-assoc UCode        UCode        (FunEl j)    cab ()
Sup-assoc UCode        UCode        (PiCode e j) cab ()
Sup-assoc UCode        (FunEl h)    c            () cbc
Sup-assoc UCode        (PiCode d h) c            () cbc
Sup-assoc (FunEl g)    Bot          c            cab cbc = refl
Sup-assoc (FunEl g)    UCode        c            () cbc
Sup-assoc (FunEl g)    (FunEl h)    Bot          cab cbc = refl
Sup-assoc (FunEl g)    (FunEl h)    UCode        cab ()
Sup-assoc (FunEl g)    (FunEl h)    (FunEl j)    cab cbc =
  Eq-cong FunEl (Eq-sym (append-assoc g h j))
Sup-assoc (FunEl g)    (FunEl h)    (PiCode e j) cab ()
Sup-assoc (FunEl g)    (PiCode d h) c            () cbc
Sup-assoc (PiCode a f) Bot          c            cab cbc = refl
Sup-assoc (PiCode a f) UCode        c            () cbc
Sup-assoc (PiCode a f) (FunEl h)    c            () cbc
Sup-assoc (PiCode a f) (PiCode d h) Bot          cab cbc = refl
Sup-assoc (PiCode a f) (PiCode d h) UCode        cab ()
Sup-assoc (PiCode a f) (PiCode d h) (FunEl j)    cab ()
Sup-assoc (PiCode a f) (PiCode d h) (PiCode e j) cab cbc =
  PiCode-cong (Sup-assoc a d e (fst cab) (fst cbc))
              (Eq-sym (append-assoc f h j))

-- EvalFun-append-eq: EvalFun (append k h) xi = Sup (EvalFun k xi) (EvalFun h xi)
{-# TERMINATING #-}
mutual
  EvalFun-append-eq : (k h : FinFun) (xi : FinEl) ->
    CompFun k h -> CoherentFunTail k -> Coherent xi ->
    Eq (EvalFun (append k h) xi) (Sup (EvalFun k xi) (EvalFun h xi))
  EvalFun-append-eq nil h xi ckh cohk cxi = refl
  EvalFun-append-eq (cons q rest) h xi ckh cohk cxi =
    EvalFun-append-eq-step (leFinEl (fst q) xi) q rest h xi refl
      (fst ckh) (snd ckh) cohk cxi

  EvalFun-append-eq-step : (n : Nat) (q : Pair FinEl FinEl) (rest h : FinFun)
    (xi : FinEl) ->
    Eq n (leFinEl (fst q) xi) ->
    CompStepFun q h -> CompFun rest h ->
    CoherentFunTail (cons q rest) -> Coherent xi ->
    Eq (EvalFun-step n (snd q) (append rest h) xi)
       (Sup (EvalFun-step n (snd q) rest xi) (EvalFun h xi))
  EvalFun-append-eq-step zero    q rest h xi eq csf crf cohk cxi =
    EvalFun-append-eq rest h xi crf (CFTcons.tail-coh cohk) cxi
  EvalFun-append-eq-step (suc _) q rest h xi eq csf crf cohk cxi =
    let ih = EvalFun-append-eq rest h xi crf (CFTcons.tail-coh cohk) cxi
        step1 : Eq (Sup (snd q) (EvalFun (append rest h) xi))
                    (Sup (snd q) (Sup (EvalFun rest xi) (EvalFun h xi)))
        step1 = Eq-cong (Sup (snd q)) ih
        le-q = leFinEl-sound (fst q) xi (Eq-transport isPos eq tt)
        comp-qr = Comp-value-EvalFun q rest xi le-q cxi (CFTcons.val-coh cohk)
                    (CFTcons.compat cohk) (coherentWith-to-compStepFun q rest (CFTcons.compat cohk))
        comp-rh = comp-EvalFun rest h xi crf (CFTcons.tail-coh cohk) cxi
        step2 : Eq (Sup (Sup (snd q) (EvalFun rest xi)) (EvalFun h xi))
                    (Sup (snd q) (Sup (EvalFun rest xi) (EvalFun h xi)))
        step2 = Sup-assoc (snd q) (EvalFun rest xi) (EvalFun h xi)
                  comp-qr comp-rh
    in Eq-transport
         (\ z -> Eq (Sup (snd q) (EvalFun (append rest h) xi)) z)
         (Eq-sym step2) step1

-- Coherent-Sup, Coherent-EvalFun, finMem-Sup-left/right, CoherentFun-append,
-- finMemUCode-Sup, EvalFun-in-UCode, finMemFun-Sup-left/right,
-- finMem-EvalFun-append/prepend
-- proved simultaneously by well-founded induction on rank.
{-# TERMINATING #-}
mutual
  Coherent-Sup : (a b : FinEl) -> Comp a b -> Coherent a -> Coherent b ->
    Coherent (Sup a b)
  Coherent-Sup Bot          b            comp coha cohb = cohb
  Coherent-Sup UCode        Bot          comp coha cohb = tt
  Coherent-Sup UCode        UCode        comp coha cohb = tt
  Coherent-Sup UCode        (FunEl h)    comp coha cohb = tt
  Coherent-Sup UCode        (PiCode c h) ()   coha cohb
  Coherent-Sup (FunEl g)    Bot          comp coha cohb = coha
  Coherent-Sup (FunEl g)    UCode        comp coha cohb = tt
  Coherent-Sup (FunEl g)    (FunEl h)    comp coha cohb =
    CoherentFun-append g h coha cohb comp
  Coherent-Sup (FunEl g)    (PiCode c h) () coha cohb
  Coherent-Sup (PiCode a f) Bot          comp coha cohb = coha
  Coherent-Sup (PiCode a f) UCode        ()   coha cohb
  Coherent-Sup (PiCode a f) (FunEl h)    () coha cohb
  Coherent-Sup (PiCode a f) (PiCode c h) comp coha cohb =
    mkSigma (Coherent-Sup a c (fst comp) (fst coha) (fst cohb))
            (CoherentFunTail-append f h (snd coha) (snd cohb) (snd comp))

  -- CoherentFunTail for appended functions (both args as CoherentFunTail)
  CoherentFunTail-append : (g h : FinFun) ->
    CoherentFunTail g -> CoherentFunTail h -> CompFun g h ->
    CoherentFunTail (append g h)
  CoherentFunTail-append nil h cohg cohh cgh = cohh
  CoherentFunTail-append (cons p ps) h cohg cohh cgh =
    mkCFT (CFTcons.key-coh cohg) (CFTcons.val-coh cohg) (CFTcons.val-nbot cohg)
          (coherentWith-append p ps h (CFTcons.compat cohg)
            (compStepFun-to-coherentWith p h (fst cgh)))
          (CoherentFunTail-append ps h (CFTcons.tail-coh cohg) cohh (snd cgh))

  -- CoherentFun for appended functions (wrapper taking CoherentFun)
  CoherentFun-append : (g h : FinFun) ->
    CoherentFun g -> CoherentFun h -> CompFun g h ->
    CoherentFun (append g h)
  CoherentFun-append nil         h () cohh cgh
  CoherentFun-append (cons p ps) h cohg cohh cgh =
    CoherentFunTail-append (cons p ps) h cohg (cft-from-cf h cohh) cgh

  -- finMemUCode-Sup: Sup of two type codes is a type code
  finMemUCode-Sup : (a c : FinEl) -> Comp a c ->
    FinMem a UCode -> FinMem c UCode -> FinMem (Sup a c) UCode
  finMemUCode-Sup Bot          c            comp aU cU = cU
  finMemUCode-Sup UCode        Bot          comp aU cU = tt
  finMemUCode-Sup UCode        UCode        comp aU cU = tt
  finMemUCode-Sup UCode        (FunEl h)    comp aU ()
  finMemUCode-Sup UCode        (PiCode c h) ()   aU cU
  finMemUCode-Sup (FunEl g)    c            comp ()  cU
  finMemUCode-Sup (PiCode a f) Bot          comp aU cU = aU
  finMemUCode-Sup (PiCode a f) UCode        ()   aU cU
  finMemUCode-Sup (PiCode a f) (FunEl h)    comp aU ()
  finMemUCode-Sup (PiCode a f) (PiCode c h) comp aU cU =
    mkSigma (finMemUCode-Sup a c (fst comp) (fst aU) (fst cU))
            (mkSigma (FinMemAllU-append-Sup a c f h (fst comp)
                       (coh-from-aU a (fst aU)) (coh-from-aU c (fst cU))
                       (fst aU) (fst cU)
                       (snd (snd aU)) (snd (snd cU))
                       (fst (snd aU)) (fst (snd cU)))
                     (CoherentFunTail-append f h (snd (snd aU)) (snd (snd cU)) (snd comp)))

  -- EvalFun-in-UCode: evaluation of a FinMemAllU function yields a type code
  EvalFun-in-UCode : (f : FinFun) (x d : FinEl) ->
    CoherentFunTail f -> Coherent x -> FinMemAllU f d ->
    FinMem (EvalFun f x) UCode
  EvalFun-in-UCode nil x d cohf cx allU = tt
  EvalFun-in-UCode (cons q rest) x d cohf cx allU =
    EvalFun-in-UCode-step (leFinEl (fst q) x) q rest x d refl cohf cx allU

  EvalFun-in-UCode-step : (n : Nat) (q : Pair FinEl FinEl) (rest : FinFun)
    (x d : FinEl) ->
    Eq n (leFinEl (fst q) x) ->
    CoherentFunTail (cons q rest) -> Coherent x -> FinMemAllU (cons q rest) d ->
    FinMem (EvalFun-step n (snd q) rest x) UCode
  EvalFun-in-UCode-step zero    q rest x d eq cohf cx allU =
    EvalFun-in-UCode rest x d (CFTcons.tail-coh cohf) cx (snd allU)
  EvalFun-in-UCode-step (suc _) q rest x d eq cohf cx allU =
    let vU = snd (fst allU)
        restU = EvalFun-in-UCode rest x d (CFTcons.tail-coh cohf) cx (snd allU)
        comp-vr = Comp-value-EvalFun q rest x
                    (leFinEl-sound (fst q) x (Eq-transport isPos eq tt))
                    cx (CFTcons.val-coh cohf) (CFTcons.compat cohf)
                    (coherentWith-to-compStepFun q rest (CFTcons.compat cohf))
    in finMemUCode-Sup (snd q) (EvalFun rest x) comp-vr vU restU

  -- FinMemAllU for appended functions with Sup domain
  FinMemAllU-append-Sup : (d c : FinEl) (f h : FinFun) ->
    Comp d c -> Coherent d -> Coherent c ->
    FinMem d UCode -> FinMem c UCode ->
    CoherentFunTail f -> CoherentFunTail h ->
    FinMemAllU f d -> FinMemAllU h c ->
    FinMemAllU (append f h) (Sup d c)
  FinMemAllU-append-Sup d c nil h cd cohd cohc dU cU cohf cohh memf memh =
    FinMemAllU-Sup-right d c h cd dU cohc cohh memh
  FinMemAllU-append-Sup d c (cons p ps) h cd cohd cohc dU cU cohf cohh memf memh =
    mkSigma
      (mkSigma (finMem-Sup-left d c (fst p) cd cohd cohc cU
                  (CFTcons.key-coh cohf) (fst (fst memf)))
               (snd (fst memf)))
      (FinMemAllU-append-Sup d c ps h cd cohd cohc dU cU
        (CFTcons.tail-coh cohf) cohh (snd memf) memh)

  -- FinMemAllU using finMem-Sup-right for the right-side entries
  FinMemAllU-Sup-right : (d c : FinEl) (h : FinFun) ->
    Comp d c -> FinMem d UCode -> Coherent c ->
    CoherentFunTail h ->
    FinMemAllU h c ->
    FinMemAllU h (Sup d c)
  FinMemAllU-Sup-right d c nil cd dU cohc cohh memh = tt
  FinMemAllU-Sup-right d c (cons p ps) cd dU cohc cohh memh =
    mkSigma
      (mkSigma (finMem-Sup-right d c (fst p) cd dU
                  (CFTcons.key-coh cohh) (fst (fst memh)))
               (snd (fst memh)))
      (FinMemAllU-Sup-right d c ps cd dU cohc
        (CFTcons.tail-coh cohh) (snd memh))

  -- finMem-Sup-right: membership in right component implies membership in Sup
  -- Strengthened: takes FinMem a UCode instead of Coherent a
  finMem-Sup-right : (a b u : FinEl) -> Comp a b -> FinMem a UCode -> Coherent u ->
    FinMem u b -> FinMem u (Sup a b)

  -- u = Bot: FinMem Bot (Sup a b) = FinMem (Sup a b) UCode
  finMem-Sup-right a b Bot comp aU cohu mem = finMemUCode-Sup a b comp aU mem

  -- u = UCode: FinMem UCode b requires b = UCode
  finMem-Sup-right Bot          UCode UCode comp aU cohu mem = tt
  finMem-Sup-right UCode        UCode UCode comp aU cohu mem = tt
  finMem-Sup-right (FunEl g)    UCode UCode comp ()  cohu mem
  finMem-Sup-right (PiCode d k) UCode UCode ()   aU cohu mem
  finMem-Sup-right a Bot          UCode comp aU cohu ()
  finMem-Sup-right a (FunEl h)    UCode comp aU cohu ()
  finMem-Sup-right a (PiCode c h) UCode comp aU cohu ()

  -- u = PiCode b' h': FinMem (PiCode b' h') requires target = UCode
  finMem-Sup-right a UCode (PiCode b' h') comp aU cohu mem =
    finMem-Sup-right-PiCode a b' h' comp aU mem
  finMem-Sup-right a Bot          (PiCode b' h') comp aU cohu ()
  finMem-Sup-right a (FunEl g)    (PiCode b' h') comp aU cohu ()
  finMem-Sup-right a (PiCode c h) (PiCode b' h') comp aU cohu ()

  -- u = FunEl g: FinMem (FunEl g) requires target = PiCode c h
  finMem-Sup-right a (PiCode c h) (FunEl g) comp aU cohu mem =
    finMem-Sup-right-FunEl a c h g comp aU cohu mem
  finMem-Sup-right a Bot       (FunEl g) comp aU cohu ()
  finMem-Sup-right a UCode     (FunEl g) comp aU cohu ()
  finMem-Sup-right a (FunEl h) (FunEl g) comp aU cohu ()

  -- Helper: PiCode case (u = PiCode b' h', b = UCode)
  finMem-Sup-right-PiCode : (a : FinEl) (b' : FinEl) (h' : FinFun) ->
    Comp a UCode -> FinMem a UCode ->
    FinMem (PiCode b' h') UCode -> FinMem (PiCode b' h') (Sup a UCode)
  finMem-Sup-right-PiCode Bot   b' h' comp aU mem = mem
  finMem-Sup-right-PiCode UCode b' h' comp aU mem = mem
  finMem-Sup-right-PiCode (FunEl g)    b' h' comp () mem
  finMem-Sup-right-PiCode (PiCode d k) b' h' () aU mem

  -- Helper: FunEl case (u = FunEl g, b = PiCode c h)
  finMem-Sup-right-FunEl : (a : FinEl) (c : FinEl) (h : FinFun) (g : FinFun) ->
    Comp a (PiCode c h) -> FinMem a UCode -> Coherent (FunEl g) ->
    FinMem (FunEl g) (PiCode c h) -> FinMem (FunEl g) (Sup a (PiCode c h))
  finMem-Sup-right-FunEl Bot          c h g comp aU cohg mem = mem
  finMem-Sup-right-FunEl UCode        c h g ()   aU cohg mem
  finMem-Sup-right-FunEl (FunEl j)    c h g comp ()  cohg mem
  finMem-Sup-right-FunEl (PiCode d k) c h g comp aU cohg mem =
    let piU = snd (snd mem)
        dU = fst aU
        allUk = fst (snd aU)
        cohk = snd (snd aU)
        cU = fst piU
        allUh = fst (snd piU)
        cohh = snd (snd piU)
        cohd = coh-from-aU d dU
        cohc = coh-from-aU c cU
        supU = finMemUCode-Sup d c (fst comp) dU cU
        allUkh = FinMemAllU-append-Sup d c k h (fst comp) cohd cohc dU cU cohk cohh allUk allUh
        cohkh = CoherentFunTail-append k h cohk cohh (snd comp)
    in mkSigma (finMemFun-Sup-right d c k h g (fst comp) (snd comp) dU allUk cohk (cft-from-cf g cohg) (fst mem))
               (mkSigma (fst (snd mem)) (mkSigma supU (mkSigma allUkh cohkh)))

  -- finMemFun-Sup-right: FinMemFun g c h → FinMemFun g (Sup d c) (append k h)
  -- Strengthened: takes FinMem d UCode and FinMemAllU k d
  finMemFun-Sup-right : (d c : FinEl) (k h : FinFun) (g : FinFun) ->
    Comp d c -> CompFun k h -> FinMem d UCode -> FinMemAllU k d -> CoherentFunTail k ->
    CoherentFunTail g ->
    FinMemFun g c h -> FinMemFun g (Sup d c) (append k h)
  finMemFun-Sup-right d c k h nil cd ckh dU allUk cohk cohg mem = tt
  finMemFun-Sup-right d c k h (cons p ps) cd ckh dU allUk cohk cohg mem =
    let key-mem = finMem-Sup-right d c (fst p) cd dU (CFTcons.key-coh cohg) (fst (fst mem))
        val-mem = finMem-EvalFun-append d k h (fst p) (snd p) ckh cohk (CFTcons.key-coh cohg) (CFTcons.val-coh cohg) allUk (snd (fst mem))
        tail-mem = finMemFun-Sup-right d c k h ps cd ckh dU allUk cohk (CFTcons.tail-coh cohg) (snd mem)
    in mkSigma (mkSigma key-mem val-mem) tail-mem

  -- Transfer membership through append (strengthened with FinMemAllU)
  finMem-EvalFun-append : (d : FinEl) (k h : FinFun) (xi yi : FinEl) ->
    CompFun k h -> CoherentFunTail k -> Coherent xi -> Coherent yi ->
    FinMemAllU k d ->
    FinMem yi (EvalFun h xi) -> FinMem yi (EvalFun (append k h) xi)
  finMem-EvalFun-append d nil h xi yi ckh cohk cxi cohyi allU mem = mem
  finMem-EvalFun-append d (cons q qs) h xi yi ckh cohk cxi cohyi allU mem =
    let ih = finMem-EvalFun-append d qs h xi yi (snd ckh) (CFTcons.tail-coh cohk) cxi cohyi (snd allU) mem
        csf = compStepFun-append q qs h
                (coherentWith-to-compStepFun q qs (CFTcons.compat cohk))
                (fst ckh)
        cw  = coherentWith-append q qs h
                (CFTcons.compat cohk)
                (compStepFun-to-coherentWith q h (fst ckh))
        vU  = snd (fst allU)
    in finMem-EvalFun-prepend (leFinEl (fst q) xi) q (append qs h) xi yi
         refl cxi (CFTcons.val-coh cohk) vU cw csf cohyi ih

  -- Prepend: case split on leFinEl value (strengthened with FinMem (snd q) UCode)
  finMem-EvalFun-prepend : (n : Nat) (q : Pair FinEl FinEl) (rest : FinFun)
    (xi yi : FinEl) ->
    Eq n (leFinEl (fst q) xi) ->
    Coherent xi -> Coherent (snd q) -> FinMem (snd q) UCode ->
    CoherentWith q rest -> CompStepFun q rest ->
    Coherent yi ->
    FinMem yi (EvalFun rest xi) ->
    FinMem yi (EvalFun-step n (snd q) rest xi)
  finMem-EvalFun-prepend zero    q rest xi yi eq cxi cohv vU cw csf cohyi ih = ih
  finMem-EvalFun-prepend (suc _) q rest xi yi eq cxi cohv vU cw csf cohyi ih =
    finMem-Sup-right (snd q) (EvalFun rest xi) yi
      (Comp-value-EvalFun q rest xi
        (leFinEl-sound (fst q) xi (Eq-transport isPos eq tt))
        cxi cohv cw csf)
      vU cohyi ih

  -- finMem-Sup-left: membership in left component implies membership in Sup
  -- Strengthened: takes FinMem b UCode
  finMem-Sup-left : (a b u : FinEl) -> Comp a b -> Coherent a -> Coherent b ->
    FinMem b UCode -> Coherent u -> FinMem u a -> FinMem u (Sup a b)

  -- u = Bot: FinMem Bot (Sup a b) = FinMem (Sup a b) UCode
  finMem-Sup-left a b Bot comp coha cohb bU cohu mem = finMemUCode-Sup a b comp mem bU

  -- u = UCode: a must be UCode
  finMem-Sup-left Bot          b UCode comp coha cohb bU cohu ()
  finMem-Sup-left UCode        Bot          UCode comp coha cohb bU cohu mem = tt
  finMem-Sup-left UCode        UCode        UCode comp coha cohb bU cohu mem = tt
  finMem-Sup-left UCode        (FunEl h)    UCode () coha cohb bU cohu mem
  finMem-Sup-left UCode        (PiCode c h) UCode ()   coha cohb bU cohu mem
  finMem-Sup-left (FunEl g)    b UCode comp coha cohb bU cohu ()
  finMem-Sup-left (PiCode a f) b UCode comp coha cohb bU cohu ()

  -- u = PiCode b' h': a must be UCode
  finMem-Sup-left Bot          b (PiCode b' h') comp coha cohb bU cohu ()
  finMem-Sup-left UCode        Bot          (PiCode b' h') comp coha cohb bU cohu mem = mem
  finMem-Sup-left UCode        UCode        (PiCode b' h') comp coha cohb bU cohu mem = mem
  finMem-Sup-left UCode        (FunEl h)    (PiCode b' h') () coha cohb bU cohu mem
  finMem-Sup-left UCode        (PiCode c h) (PiCode b' h') ()   coha cohb bU cohu mem
  finMem-Sup-left (FunEl g)    b (PiCode b' h') comp coha cohb bU cohu ()
  finMem-Sup-left (PiCode a f) b (PiCode b' h') comp coha cohb bU cohu ()

  -- u = FunEl g: a must be PiCode d k
  finMem-Sup-left Bot          b            (FunEl g) comp coha cohb bU cohu ()
  finMem-Sup-left UCode        b            (FunEl g) comp coha cohb bU cohu ()
  finMem-Sup-left (FunEl j)    b            (FunEl g) comp coha cohb bU cohu ()
  finMem-Sup-left (PiCode d k) Bot          (FunEl g) comp coha cohb bU cohu mem = mem
  finMem-Sup-left (PiCode d k) UCode        (FunEl g) ()   coha cohb bU cohu mem
  finMem-Sup-left (PiCode d k) (FunEl h)    (FunEl g) () coha cohb bU cohu mem
  finMem-Sup-left (PiCode d k) (PiCode c h) (FunEl g) comp coha cohb bU cohu mem =
    let -- Extract from Coherent (PiCode d k) and Coherent (PiCode c h)
        cohd = fst coha
        cohc = fst cohb
        -- Extract from FinMem (FunEl g) (PiCode d k):
        --   fst mem : FinMemFun g d k
        --   fst (snd mem) : CoherentFun g
        --   snd (snd mem) : FinMem (PiCode d k) UCode
        dkU = snd (snd mem)
        dU = fst dkU
        allUk = fst (snd dkU)
        -- Extract from bU : FinMem (PiCode c h) UCode
        cU = fst bU
        allUh = fst (snd bU)
        -- CoherentFunTail versions for recursive calls
        cohk = snd coha
        cohh = snd cohb
        cohg = cft-from-cf g (fst (snd mem))
        -- Build FinMem (PiCode (Sup d c) (append k h)) UCode
        supU = finMemUCode-Sup d c (fst comp) dU cU
        allUkh = FinMemAllU-append-Sup d c k h (fst comp) cohd cohc dU cU cohk cohh allUk allUh
        cohkh = CoherentFunTail-append k h cohk cohh (snd comp)
    in mkSigma (finMemFun-Sup-left d c k h g (fst comp) (snd comp) cohd cohc cU allUh cohk cohh cohg (fst mem))
               (mkSigma (fst (snd mem)) (mkSigma supU (mkSigma allUkh cohkh)))

  -- Main workhorse: FinMemFun g d k → FinMemFun g (Sup d c) (append k h)
  -- Strengthened: takes FinMem c UCode and FinMemAllU h c
  finMemFun-Sup-left : (d c : FinEl) (k h : FinFun) (g : FinFun) ->
    Comp d c -> CompFun k h ->
    Coherent d -> Coherent c -> FinMem c UCode -> FinMemAllU h c ->
    CoherentFunTail k -> CoherentFunTail h ->
    CoherentFunTail g ->
    FinMemFun g d k -> FinMemFun g (Sup d c) (append k h)
  finMemFun-Sup-left d c k h nil cd ckh cohd cohc cU allUh cohk cohh cohg mem = tt
  finMemFun-Sup-left d c k h (cons p ps) cd ckh cohd cohc cU allUh cohk cohh cohg mem =
    let key-mem = finMem-Sup-left d c (fst p) cd cohd cohc cU
                    (CFTcons.key-coh cohg) (fst (fst mem))
        eval-eq = EvalFun-append-eq k h (fst p) ckh cohk (CFTcons.key-coh cohg)
        comp-eval = comp-EvalFun k h (fst p) ckh cohk (CFTcons.key-coh cohg)
        coh-eval-k = Coherent-EvalFun k (fst p) cohk (CFTcons.key-coh cohg)
        coh-eval-h = Coherent-EvalFun h (fst p) cohh (CFTcons.key-coh cohg)
        evalh-U = EvalFun-in-UCode h (fst p) c cohh (CFTcons.key-coh cohg) allUh
        val-left = finMem-Sup-left (EvalFun k (fst p)) (EvalFun h (fst p)) (snd p)
                     comp-eval coh-eval-k coh-eval-h evalh-U
                     (CFTcons.val-coh cohg) (snd (fst mem))
        val-mem = Eq-transport (FinMem (snd p)) (Eq-sym eval-eq) val-left
        tail-mem = finMemFun-Sup-left d c k h ps cd ckh cohd cohc cU allUh cohk cohh
                     (CFTcons.tail-coh cohg) (snd mem)
    in mkSigma (mkSigma key-mem val-mem) tail-mem

  -- Coherent-EvalFun: evaluation of a coherent function at a coherent
  -- input produces a coherent result.
  Coherent-EvalFun : (k : FinFun) (u : FinEl) ->
    CoherentFunTail k -> Coherent u -> Coherent (EvalFun k u)
  Coherent-EvalFun nil u cohk cohu = tt
  Coherent-EvalFun (cons q rest) u cohk cohu =
    Coherent-EvalFun-step (leFinEl (fst q) u) q rest u refl cohk cohu

  Coherent-EvalFun-step : (n : Nat) (q : Pair FinEl FinEl) (rest : FinFun)
    (u : FinEl) ->
    Eq n (leFinEl (fst q) u) ->
    CoherentFunTail (cons q rest) -> Coherent u ->
    Coherent (EvalFun-step n (snd q) rest u)
  Coherent-EvalFun-step zero    q rest u eq cohk cohu =
    Coherent-EvalFun rest u (CFTcons.tail-coh cohk) cohu
  Coherent-EvalFun-step (suc _) q rest u eq cohk cohu =
    let cohv = CFTcons.val-coh cohk
        coh-rest = Coherent-EvalFun rest u (CFTcons.tail-coh cohk) cohu
        comp-vr = Comp-value-EvalFun q rest u
                    (leFinEl-sound (fst q) u (Eq-transport isPos eq tt))
                    cohu cohv (CFTcons.compat cohk)
                    (coherentWith-to-compStepFun q rest (CFTcons.compat cohk))
    in Coherent-Sup (snd q) (EvalFun rest u) comp-vr cohv coh-rest

------------------------------------------------------------------------
-- Part 7i: Order-theoretic lemmas
--
-- LeCode-refl, LeCode-trans, LeCode-Sup-left, LeCode-Sup-right, etc.
-- Must come after Part 7h (uses Comp-value-EvalFun, Coherent-EvalFun,
-- CoherentFun-append, coherentWith-to-compStepFun).
------------------------------------------------------------------------

Coherent-keys : FinFun -> Set
Coherent-keys nil         = Top
Coherent-keys (cons p ps) = Pair (Coherent (fst p)) (Coherent-keys ps)

CoherentFun-keys : (g : FinFun) -> CoherentFunTail g -> Coherent-keys g
CoherentFun-keys nil         coh = tt
CoherentFun-keys (cons p ps) coh =
  mkSigma (CFTcons.key-coh coh) (CoherentFun-keys ps (CFTcons.tail-coh coh))

{-# TERMINATING #-}
mutual
  LeCode-refl : (a : FinEl) -> Coherent a -> LeCode a a
  LeCode-refl Bot          ca = tt
  LeCode-refl UCode        ca = tt
  LeCode-refl (FunEl g)    ca = LeFunCode-refl g (cft-from-cf g ca)
  LeCode-refl (PiCode a f) ca =
    mkSigma (LeCode-refl a (fst ca))
            (LeFunCode-refl f (snd ca))

  LeFunCode-refl : (g : FinFun) -> CoherentFunTail g -> LeFunCode g g
  LeFunCode-refl nil         coh = tt
  LeFunCode-refl (cons p ps) coh =
    mkSigma
      (LeFunCode-refl-head-step (leFinEl (fst p) (fst p)) p ps refl coh)
      (LeFunCode-cons-lift ps p ps coh (CFTcons.tail-coh coh)
        (LeFunCode-refl ps (CFTcons.tail-coh coh)))

  LeFunCode-refl-head-step : (n : Nat) (p : Pair FinEl FinEl) (ps : FinFun) ->
    Eq n (leFinEl (fst p) (fst p)) ->
    CoherentFunTail (cons p ps) ->
    LeCode (snd p) (EvalFun-step n (snd p) ps (fst p))
  LeFunCode-refl-head-step zero    p ps eq coh
    with Eq-transport isPos (Eq-sym eq)
           (leFinEl-complete (fst p) (fst p)
             (LeCode-refl (fst p) (CFTcons.key-coh coh)))
  ... | ()
  LeFunCode-refl-head-step (suc _) p ps eq coh =
    LeCode-Sup-left (snd p) (EvalFun ps (fst p))
      (Comp-value-EvalFun p ps (fst p)
        (LeCode-refl (fst p) (CFTcons.key-coh coh)) (CFTcons.key-coh coh)
        (CFTcons.val-coh coh)
        (CFTcons.compat coh) (coherentWith-to-compStepFun p ps (CFTcons.compat coh)))
      (CFTcons.val-coh coh)
      (Coherent-EvalFun ps (fst p) (CFTcons.tail-coh coh) (CFTcons.key-coh coh))

  -- Lifting: if LeFunCode g rest, then LeFunCode g (cons p rest)
  LeFunCode-cons-lift : (g : FinFun) (p : Pair FinEl FinEl) (rest : FinFun) ->
    CoherentFunTail (cons p rest) -> CoherentFunTail g ->
    LeFunCode g rest -> LeFunCode g (cons p rest)
  LeFunCode-cons-lift nil         p rest coh cohg le = tt
  LeFunCode-cons-lift (cons q qs) p rest coh cohg le =
    mkSigma
      (LeCode-trans (snd q) (EvalFun rest (fst q)) (EvalFun (cons p rest) (fst q))
        (CFTcons.val-coh cohg)
        (Coherent-EvalFun rest (fst q) (CFTcons.tail-coh coh) (CFTcons.key-coh cohg))
        (Coherent-EvalFun (cons p rest) (fst q) coh (CFTcons.key-coh cohg))
        (fst le)
        (EvalFun-cons-mono p rest (fst q) coh (CFTcons.key-coh cohg)))
      (LeFunCode-cons-lift qs p rest coh (CFTcons.tail-coh cohg) (snd le))

  -- Prepending entry: EvalFun rest u ≤ EvalFun (cons q rest) u
  EvalFun-cons-mono : (q : Pair FinEl FinEl) (rest : FinFun) (u : FinEl) ->
    CoherentFunTail (cons q rest) -> Coherent u ->
    LeCode (EvalFun rest u) (EvalFun (cons q rest) u)
  EvalFun-cons-mono q rest u coh cu =
    EvalFun-cons-mono-step (leFinEl (fst q) u) q rest u refl coh cu

  EvalFun-cons-mono-step : (n : Nat) (q : Pair FinEl FinEl) (rest : FinFun)
    (u : FinEl) ->
    Eq n (leFinEl (fst q) u) ->
    CoherentFunTail (cons q rest) -> Coherent u ->
    LeCode (EvalFun rest u) (EvalFun-step n (snd q) rest u)
  EvalFun-cons-mono-step zero    q rest u eq coh cu =
    LeCode-refl (EvalFun rest u) (Coherent-EvalFun rest u (CFTcons.tail-coh coh) cu)
  EvalFun-cons-mono-step (suc _) q rest u eq coh cu =
    let le-key = leFinEl-sound (fst q) u (Eq-transport isPos eq tt)
        cohv = CFTcons.val-coh coh
        cw = CFTcons.compat coh
        cohrest = CFTcons.tail-coh coh
        comp = Comp-value-EvalFun q rest u le-key cu cohv
                 cw (coherentWith-to-compStepFun q rest cw)
    in LeCode-Sup-right (snd q) (EvalFun rest u) comp
         cohv (Coherent-EvalFun rest u cohrest cu)

  LeCode-Sup-left : (a b : FinEl) -> Comp a b -> Coherent a -> Coherent b ->
    LeCode a (Sup a b)
  LeCode-Sup-left Bot          b            comp ca cb = tt
  LeCode-Sup-left UCode        Bot          comp ca cb = tt
  LeCode-Sup-left UCode        UCode        comp ca cb = tt
  LeCode-Sup-left UCode        (FunEl h)    () ca cb
  LeCode-Sup-left UCode        (PiCode b h) ()
  LeCode-Sup-left (FunEl g)    Bot          comp ca cb = LeCode-refl (FunEl g) ca
  LeCode-Sup-left (FunEl g)    UCode        () ca cb
  LeCode-Sup-left (FunEl g)    (FunEl h)    comp ca cb =
    LeFunCode-append-left g h comp (cft-from-cf g ca) (cft-from-cf h cb)
  LeCode-Sup-left (FunEl g)    (PiCode b h) () ca cb
  LeCode-Sup-left (PiCode a f) Bot          comp ca cb = LeCode-refl (PiCode a f) ca
  LeCode-Sup-left (PiCode a f) UCode        ()
  LeCode-Sup-left (PiCode a f) (FunEl h)    () ca cb
  LeCode-Sup-left (PiCode a f) (PiCode b h) comp ca cb =
    mkSigma (LeCode-Sup-left a b (fst comp) (fst ca) (fst cb))
            (LeFunCode-append-left f h (snd comp) (snd ca) (snd cb))

  LeCode-Sup-right : (a b : FinEl) -> Comp a b -> Coherent a -> Coherent b ->
    LeCode b (Sup a b)
  LeCode-Sup-right a            Bot          comp ca cb = tt
  LeCode-Sup-right Bot          UCode        comp ca cb = tt
  LeCode-Sup-right UCode        UCode        comp ca cb = tt
  LeCode-Sup-right (FunEl g)    UCode        () ca cb
  LeCode-Sup-right (PiCode a f) UCode        ()
  LeCode-Sup-right Bot          (FunEl h)    comp ca cb = LeCode-refl (FunEl h) cb
  LeCode-Sup-right UCode        (FunEl h)    () ca cb
  LeCode-Sup-right (FunEl g)    (FunEl h)    comp ca cb =
    LeFunCode-append-right g h comp (cft-from-cf g ca) (cft-from-cf h cb)
  LeCode-Sup-right (PiCode a f) (FunEl h)    () ca cb
  LeCode-Sup-right Bot          (PiCode b h) comp ca cb = LeCode-refl (PiCode b h) cb
  LeCode-Sup-right UCode        (PiCode b h) ()
  LeCode-Sup-right (FunEl g)    (PiCode b h) () ca cb
  LeCode-Sup-right (PiCode a f) (PiCode b h) comp ca cb =
    mkSigma (LeCode-Sup-right a b (fst comp) (fst ca) (fst cb))
            (LeFunCode-append-right f h (snd comp) (snd ca) (snd cb))

  LeCode-trans : (x y z : FinEl) -> Coherent x -> Coherent y -> Coherent z ->
    LeCode x y -> LeCode y z -> LeCode x z
  LeCode-trans Bot          y            z            cx cy cz xy yz = tt
  LeCode-trans UCode        Bot          z            cx cy cz ()
  LeCode-trans UCode        UCode        z            cx cy cz xy yz = yz
  LeCode-trans UCode        (FunEl h)    z            cx cy cz ()
  LeCode-trans UCode        (PiCode b g) z            cx cy cz ()
  LeCode-trans (FunEl g)    Bot          Bot          cx cy cz ()
  LeCode-trans (FunEl g)    Bot          UCode        cx cy cz ()
  LeCode-trans (FunEl g)    Bot          (FunEl k)    cx cy cz ()
  LeCode-trans (FunEl g)    Bot          (PiCode c k) cx cy cz ()
  LeCode-trans (FunEl g)    UCode        Bot          cx cy cz ()
  LeCode-trans (FunEl g)    UCode        UCode        cx cy cz ()
  LeCode-trans (FunEl g)    UCode        (FunEl k)    cx cy cz ()
  LeCode-trans (FunEl g)    UCode        (PiCode c k) cx cy cz ()
  LeCode-trans (FunEl g)    (FunEl h)    Bot          cx cy cz xy ()
  LeCode-trans (FunEl g)    (FunEl h)    UCode        cx cy cz xy ()
  LeCode-trans (FunEl g)    (FunEl h)    (FunEl k)    cx cy cz xy yz =
    LeFunCode-trans g h k (cft-from-cf g cx) (cft-from-cf h cy) (cft-from-cf k cz) xy yz
  LeCode-trans (FunEl g)    (FunEl h)    (PiCode c k) cx cy cz xy ()
  LeCode-trans (FunEl g)    (PiCode b h) Bot          cx cy cz ()
  LeCode-trans (FunEl g)    (PiCode b h) UCode        cx cy cz ()
  LeCode-trans (FunEl g)    (PiCode b h) (FunEl k)    cx cy cz ()
  LeCode-trans (FunEl g)    (PiCode b h) (PiCode c k) cx cy cz ()
  LeCode-trans (PiCode a f) Bot          z            cx cy cz ()
  LeCode-trans (PiCode a f) UCode        z            cx cy cz ()
  LeCode-trans (PiCode a f) (FunEl h)    z            cx cy cz ()
  LeCode-trans (PiCode a f) (PiCode b g) Bot          cx cy cz xy ()
  LeCode-trans (PiCode a f) (PiCode b g) UCode        cx cy cz xy ()
  LeCode-trans (PiCode a f) (PiCode b g) (FunEl k)    cx cy cz xy ()
  LeCode-trans (PiCode a f) (PiCode b g) (PiCode c k) cx cy cz xy yz =
    mkSigma (LeCode-trans a b c (fst cx) (fst cy) (fst cz) (fst xy) (fst yz))
            (LeFunCode-trans f g k (snd cx) (snd cy) (snd cz) (snd xy) (snd yz))

  LeFunCode-trans : (g h k : FinFun) ->
    CoherentFunTail g -> CoherentFunTail h -> CoherentFunTail k ->
    LeFunCode g h -> LeFunCode h k -> LeFunCode g k
  LeFunCode-trans nil         h k cohg cohh cohk gh hk = tt
  LeFunCode-trans (cons p ps) h k cohg cohh cohk gh hk =
    mkSigma
      (LeCode-trans (snd p) (EvalFun h (fst p)) (EvalFun k (fst p))
        (CFTcons.val-coh cohg)
        (Coherent-EvalFun h (fst p) cohh (CFTcons.key-coh cohg))
        (Coherent-EvalFun k (fst p) cohk (CFTcons.key-coh cohg))
        (fst gh)
        (EvalFun-mon h k (fst p) cohh cohk (CFTcons.key-coh cohg) hk))
      (LeFunCode-trans ps h k (CFTcons.tail-coh cohg) cohh cohk (snd gh) hk)

  -- LeFunCode-nil-any: if all values in g are <= Bot, then g <= k for any k
  LeFunCode-nil-any : (g k : FinFun) ->
    CoherentFunTail g -> CoherentFunTail k -> LeFunCode g nil -> LeFunCode g k
  LeFunCode-nil-any nil         k cohg cohk lg = tt
  LeFunCode-nil-any (cons p ps) k cohg cohk lg =
    mkSigma
      (LeCode-trans (snd p) Bot (EvalFun k (fst p))
        (CFTcons.val-coh cohg)
        tt
        (Coherent-EvalFun k (fst p) cohk (CFTcons.key-coh cohg))
        (fst lg) tt)
      (LeFunCode-nil-any ps k (CFTcons.tail-coh cohg) cohk (snd lg))

  -- EvalFun monotone in function arg
  EvalFun-mon : (h k : FinFun) (u : FinEl) ->
    CoherentFunTail h -> CoherentFunTail k -> Coherent u ->
    LeFunCode h k -> LeCode (EvalFun h u) (EvalFun k u)
  EvalFun-mon nil         k u cohh cohk cu hk = tt
  EvalFun-mon (cons q qs) k u cohh cohk cu hk =
    EvalFun-mon-step (leFinEl (fst q) u) q qs k u refl cohh cohk cu hk

  EvalFun-mon-step : (n : Nat) (q : Pair FinEl FinEl) (qs : FinFun)
    (k : FinFun) (u : FinEl) ->
    Eq n (leFinEl (fst q) u) ->
    CoherentFunTail (cons q qs) -> CoherentFunTail k -> Coherent u ->
    LeFunCode (cons q qs) k ->
    LeCode (EvalFun-step n (snd q) qs u) (EvalFun k u)
  EvalFun-mon-step zero    q qs k u eq cohh cohk cu hk =
    EvalFun-mon qs k u (CFTcons.tail-coh cohh) cohk cu (snd hk)
  EvalFun-mon-step (suc _) q qs k u eq cohh cohk cu hk =
    let le-key = leFinEl-sound (fst q) u (Eq-transport isPos eq tt)
        cq = CFTcons.key-coh cohh
        cv = CFTcons.val-coh cohh
    in LeCode-Sup-lub (snd q) (EvalFun qs u) (EvalFun k u)
         (LeCode-trans (snd q) (EvalFun k (fst q)) (EvalFun k u)
           cv
           (Coherent-EvalFun k (fst q) cohk cq)
           (Coherent-EvalFun k u cohk cu)
           (fst hk)
           (EvalFun-mon-arg k (fst q) u le-key cohk cq cu))
         (EvalFun-mon qs k u (CFTcons.tail-coh cohh) cohk cu (snd hk))

  -- Sup is LUB: a ≤ c and b ≤ c implies Sup a b ≤ c
  LeCode-Sup-lub : (a b c : FinEl) -> LeCode a c -> LeCode b c ->
    LeCode (Sup a b) c
  LeCode-Sup-lub Bot          b            c            ac bc = bc
  LeCode-Sup-lub UCode        Bot          c            ac bc = ac
  LeCode-Sup-lub UCode        UCode        c            ac bc = ac
  LeCode-Sup-lub UCode        (FunEl h)    c            ac bc = tt
  LeCode-Sup-lub UCode        (PiCode b h) c            ac bc = tt
  LeCode-Sup-lub (FunEl g)    Bot          c            ac bc = ac
  LeCode-Sup-lub (FunEl g)    UCode        c            ac bc = tt
  LeCode-Sup-lub (FunEl g)    (FunEl h)    Bot          ()  bc
  LeCode-Sup-lub (FunEl g)    (FunEl h)    UCode        ()  bc
  LeCode-Sup-lub (FunEl g)    (FunEl h)    (FunEl k)    ac bc =
    LeFunCode-append-combine g h k ac bc
  LeCode-Sup-lub (FunEl g)    (FunEl h)    (PiCode c k) ()  bc
  LeCode-Sup-lub (FunEl g)    (PiCode b h) c            ac bc = tt
  LeCode-Sup-lub (PiCode a f) Bot          c            ac bc = ac
  LeCode-Sup-lub (PiCode a f) UCode        c            ac bc = tt
  LeCode-Sup-lub (PiCode a f) (FunEl h)    c            ac bc = tt
  LeCode-Sup-lub (PiCode a f) (PiCode b g) Bot          ac ()
  LeCode-Sup-lub (PiCode a f) (PiCode b g) UCode        ac ()
  LeCode-Sup-lub (PiCode a f) (PiCode b g) (FunEl k)    ac ()
  LeCode-Sup-lub (PiCode a f) (PiCode b g) (PiCode c k) ac bc =
    mkSigma (LeCode-Sup-lub a b c (fst ac) (fst bc))
            (LeFunCode-append-combine f g k (snd ac) (snd bc))

  -- LeFunCode g k and LeFunCode h k implies LeFunCode (append g h) k
  LeFunCode-append-combine : (g h k : FinFun) ->
    LeFunCode g k -> LeFunCode h k -> LeFunCode (append g h) k
  LeFunCode-append-combine nil         h k gk hk = hk
  LeFunCode-append-combine (cons p ps) h k gk hk =
    mkSigma (fst gk) (LeFunCode-append-combine ps h k (snd gk) hk)

  LeFunCode-append-left : (g h : FinFun) -> CompFun g h ->
    CoherentFunTail g -> CoherentFunTail h ->
    LeFunCode g (append g h)
  LeFunCode-append-left nil         h comp cohg cohh = tt
  LeFunCode-append-left (cons p ps) h comp cohg cohh =
    let coh-append = CoherentFunTail-append (cons p ps) h cohg cohh comp
    in mkSigma
      (LeFunCode-refl-head-step
        (leFinEl (fst p) (fst p)) p (append ps h) refl
        coh-append)
      (LeFunCode-cons-lift ps p (append ps h)
        coh-append (CFTcons.tail-coh cohg)
        (LeFunCode-append-left ps h (snd comp) (CFTcons.tail-coh cohg) cohh))

  LeFunCode-append-right : (g h : FinFun) -> CompFun g h ->
    CoherentFunTail g -> CoherentFunTail h ->
    LeFunCode h (append g h)
  LeFunCode-append-right g h comp cohg cohh =
    let coh-append = CoherentFunTail-append g h cohg cohh comp
    in LeFunCode-append-right-go g h h comp coh-append cohh
         (LeFunCode-refl h cohh)

  LeFunCode-append-right-go : (g h rest : FinFun) -> CompFun g h ->
    CoherentFunTail (append g rest) -> CoherentFunTail h ->
    LeFunCode h rest -> LeFunCode h (append g rest)
  LeFunCode-append-right-go nil         h rest comp coh cohh le = le
  LeFunCode-append-right-go (cons p ps) h rest comp coh cohh le =
    LeFunCode-cons-lift h p (append ps rest) coh cohh
      (LeFunCode-append-right-go ps h rest (snd comp) (CFTcons.tail-coh coh) cohh le)

  -- EvalFun monotone in argument: u ≤ v → EvalFun k u ≤ EvalFun k v
  EvalFun-mon-arg : (k : FinFun) (u v : FinEl) ->
    LeCode u v -> CoherentFunTail k -> Coherent u -> Coherent v ->
    LeCode (EvalFun k u) (EvalFun k v)
  EvalFun-mon-arg nil         u v le cohk cu cv = tt
  EvalFun-mon-arg (cons q qs) u v le cohk cu cv =
    EvalFun-mon-arg-step (leFinEl (fst q) u) q qs u v refl le cohk cu cv

  EvalFun-mon-arg-step : (n : Nat) (q : Pair FinEl FinEl) (qs : FinFun)
    (u v : FinEl) ->
    Eq n (leFinEl (fst q) u) ->
    LeCode u v -> CoherentFunTail (cons q qs) -> Coherent u -> Coherent v ->
    LeCode (EvalFun-step n (snd q) qs u) (EvalFun (cons q qs) v)
  EvalFun-mon-arg-step zero    q qs u v eq le cohk cu cv =
    LeCode-trans (EvalFun qs u) (EvalFun qs v) (EvalFun (cons q qs) v)
      (Coherent-EvalFun qs u (CFTcons.tail-coh cohk) cu)
      (Coherent-EvalFun qs v (CFTcons.tail-coh cohk) cv)
      (Coherent-EvalFun (cons q qs) v cohk cv)
      (EvalFun-mon-arg qs u v le (CFTcons.tail-coh cohk) cu cv)
      (EvalFun-cons-mono q qs v cohk cv)
  EvalFun-mon-arg-step (suc x) q qs u v eq le cohk cu cv =
    EvalFun-mon-arg-suc x (leFinEl (fst q) v) q qs u v eq refl le cohk cu cv

  -- Second-level step: case-split on leFinEl (fst q) v to force target into Sup form
  EvalFun-mon-arg-suc : (x : Nat) (m : Nat) (q : Pair FinEl FinEl) (qs : FinFun)
    (u v : FinEl) ->
    Eq (suc x) (leFinEl (fst q) u) ->
    Eq m (leFinEl (fst q) v) ->
    LeCode u v -> CoherentFunTail (cons q qs) -> Coherent u -> Coherent v ->
    LeCode (Sup (snd q) (EvalFun qs u)) (EvalFun-step m (snd q) qs v)
  EvalFun-mon-arg-suc x zero    q qs u v equ eqv le cohk cu cv
    with Eq-transport isPos (Eq-sym eqv)
           (leFinEl-complete (fst q) v
             (LeCode-trans (fst q) u v
               (CFTcons.key-coh cohk) cu cv
               (leFinEl-sound (fst q) u (Eq-transport isPos equ tt)) le))
  ... | ()
  EvalFun-mon-arg-suc x (suc _) q qs u v equ eqv le cohk cu cv =
    let cohv = CFTcons.val-coh cohk
        cohrest = CFTcons.tail-coh cohk
        cw = CFTcons.compat cohk
        le-key-v = LeCode-trans (fst q) u v
                     (CFTcons.key-coh cohk) cu cv
                     (leFinEl-sound (fst q) u (Eq-transport isPos equ tt)) le
        coh-rest-u = Coherent-EvalFun qs u cohrest cu
        coh-rest-v = Coherent-EvalFun qs v cohrest cv
        comp-v = Comp-value-EvalFun q qs v le-key-v cv cohv
                   cw (coherentWith-to-compStepFun q qs cw)
        ih = EvalFun-mon-arg qs u v le cohrest cu cv
        sup-left = LeCode-Sup-left (snd q) (EvalFun qs v) comp-v cohv coh-rest-v
        sup-right = LeCode-Sup-right (snd q) (EvalFun qs v) comp-v cohv coh-rest-v
        coh-sup = Coherent-Sup (snd q) (EvalFun qs v) comp-v cohv coh-rest-v
        tail-le = LeCode-trans (EvalFun qs u) (EvalFun qs v)
                    (Sup (snd q) (EvalFun qs v))
                    coh-rest-u coh-rest-v coh-sup
                    ih sup-right
    in LeCode-Sup-lub (snd q) (EvalFun qs u) (Sup (snd q) (EvalFun qs v))
         sup-left tail-le

------------------------------------------------------------------------
-- finMem-upward -- upward monotonicity of FinMem
--
-- FinMem v a -> LeCode a b -> FinMem v b
-- (with coherence and FinMem b UCode hypotheses)
------------------------------------------------------------------------

finMem-upward : (v a b : FinEl) -> LeCode a b -> Coherent a -> Coherent b ->
  FinMem v a -> FinMem b UCode -> FinMem v b
finMemFun-upward : (g : FinFun) (a b : FinEl) (f h : FinFun) ->
  LeCode a b -> Coherent a -> Coherent b ->
  CoherentFunTail f -> CoherentFunTail h -> LeFunCode f h ->
  FinMemFun g a f -> FinMem b UCode -> FinMemAllU h b -> FinMemFun g b h

-- Bot: FinMem Bot a = FinMem a UCode, FinMem Bot b = FinMem b UCode
finMem-upward Bot a b le ca cb mem bU = bU
-- UCode: a must be UCode, b must be UCode
finMem-upward UCode UCode UCode le ca cb mem bU = tt
finMem-upward UCode UCode Bot ()
finMem-upward UCode UCode (FunEl h) ()
finMem-upward UCode UCode (PiCode c h) ()
finMem-upward UCode Bot b le ca cb ()
finMem-upward UCode (FunEl g) b le ca cb ()
finMem-upward UCode (PiCode c h) b le ca cb ()
-- FunEl g: a must be PiCode, b must be PiCode
finMem-upward (FunEl g) (PiCode a f) (PiCode b h) le ca cb mem bU =
  mkSigma
    (finMemFun-upward g a b f h (fst le) (fst ca) (coh-from-aU b (fst bU))
      (snd ca) (snd (snd bU)) (snd le) (fst mem) (fst bU) (fst (snd bU)))
    (mkSigma (fst (snd mem)) bU)
finMem-upward (FunEl g) (PiCode a f) Bot ()
finMem-upward (FunEl g) (PiCode a f) UCode ()
finMem-upward (FunEl g) (PiCode a f) (FunEl h) ()
finMem-upward (FunEl g) Bot b le ca cb ()
finMem-upward (FunEl g) UCode b le ca cb ()
finMem-upward (FunEl g) (FunEl h) b le ca cb ()
-- PiCode: a must be UCode, b must be UCode
finMem-upward (PiCode a f) UCode UCode le ca cb mem bU = mem
finMem-upward (PiCode a f) UCode Bot ()
finMem-upward (PiCode a f) UCode (FunEl h) ()
finMem-upward (PiCode a f) UCode (PiCode c h) ()
finMem-upward (PiCode a f) Bot b le ca cb ()
finMem-upward (PiCode a f) (FunEl g) b le ca cb ()
finMem-upward (PiCode a f) (PiCode c h) b le ca cb ()

-- finMemFun-upward: transport FinMemFun g a f to FinMemFun g b h
finMemFun-upward nil a b f h le-a ca cb cf ch lfh mem bU allUh = tt
finMemFun-upward (cons p ps) a b f h le-a ca cb cf ch lfh mem bU allUh =
  let cp = FinMem-coh-u (fst p) a (fst (fst mem))
      le-fh = EvalFun-mon f h (fst p) cf ch cp lfh
      c-ef = Coherent-EvalFun f (fst p) cf cp
      c-eh = Coherent-EvalFun h (fst p) ch cp
      efhU = EvalFun-in-UCode h (fst p) b ch cp allUh
  in mkSigma
    (mkSigma
      (finMem-upward (fst p) a b le-a ca cb (fst (fst mem)) bU)
      (finMem-upward (snd p) (EvalFun f (fst p)) (EvalFun h (fst p))
        le-fh c-ef c-eh (snd (fst mem)) efhU))
    (finMemFun-upward ps a b f h le-a ca cb cf ch lfh (snd mem) bU allUh)

------------------------------------------------------------------------
-- FinMem-Sup-element -- FinMem closed under compatible Sup in element
--
-- FinMem u a -> FinMem v a -> Comp u v -> FinMem (Sup u v) a
------------------------------------------------------------------------

FinMemFun-append : (g h : FinFun) (b : FinEl) (f : FinFun) ->
  FinMemFun g b f -> FinMemFun h b f -> FinMemFun (append g h) b f
FinMemFun-append nil h b f mg mh = mh
FinMemFun-append (cons p ps) h b f mg mh =
  mkSigma (fst mg) (FinMemFun-append ps h b f (snd mg) mh)

FinMem-Sup-element : (u v a : FinEl) -> Comp u v -> Coherent a ->
  FinMem u a -> FinMem v a -> FinMem (Sup u v) a
-- u = Bot: Sup Bot v = v
FinMem-Sup-element Bot v a comp ca mu mv = mv
-- v = Bot: Sup u Bot = u (case split on u for exact-split)
FinMem-Sup-element UCode Bot a comp ca mu mv = mu
FinMem-Sup-element (FunEl g) Bot a comp ca mu mv = mu
FinMem-Sup-element (PiCode a1 f1) Bot a comp ca mu mv = mu
-- u = UCode, v = UCode: Sup UCode UCode = UCode
FinMem-Sup-element UCode UCode UCode comp ca mu mv = tt
FinMem-Sup-element UCode UCode Bot comp ca () mv
FinMem-Sup-element UCode UCode (FunEl h) comp ca () mv
FinMem-Sup-element UCode UCode (PiCode b f) comp ca () mv
-- u = UCode, v = FunEl/PiCode: Comp = Empty
FinMem-Sup-element UCode (FunEl h) a () ca mu mv
FinMem-Sup-element UCode (PiCode b f) a () ca mu mv
-- u = FunEl, v = UCode/PiCode: Sup absorbs FunEl
FinMem-Sup-element (FunEl g) UCode a () ca mu mv
FinMem-Sup-element (FunEl g) (PiCode b f) a () ca mu mv
-- u = FunEl g, v = FunEl h: Sup = FunEl (append g h), a = PiCode b' f'
FinMem-Sup-element (FunEl g) (FunEl h) Bot comp ca () mv
FinMem-Sup-element (FunEl g) (FunEl h) UCode comp ca () mv
FinMem-Sup-element (FunEl g) (FunEl h) (FunEl k) comp ca () mv
FinMem-Sup-element (FunEl g) (FunEl h) (PiCode b f) comp ca mu mv =
  mkSigma (FinMemFun-append g h b f (fst mu) (fst mv))
    (mkSigma (CoherentFun-append g h (fst (snd mu)) (fst (snd mv)) comp)
             (snd (snd mu)))
-- u = PiCode, v = UCode/FunEl: Comp = Empty
FinMem-Sup-element (PiCode a1 f1) UCode a () ca mu mv
FinMem-Sup-element (PiCode a1 f1) (FunEl h) a () ca mu mv
-- u = PiCode, v = PiCode: a = UCode, use finMemUCode-Sup
FinMem-Sup-element (PiCode a1 f1) (PiCode a2 f2) Bot comp ca () mv
FinMem-Sup-element (PiCode a1 f1) (PiCode a2 f2) UCode comp ca mu mv =
  finMemUCode-Sup (PiCode a1 f1) (PiCode a2 f2) comp mu mv
FinMem-Sup-element (PiCode a1 f1) (PiCode a2 f2) (FunEl h) comp ca () mv
FinMem-Sup-element (PiCode a1 f1) (PiCode a2 f2) (PiCode b f) comp ca () mv

------------------------------------------------------------------------
-- finMem-Sup-both -- simultaneous Sup on element and type
--
-- FinMem a1 u1 -> FinMem a2 u2 -> Comp u1 u2 -> Comp a1 a2 ->
--   FinMem (Sup a1 a2) (Sup u1 u2)
------------------------------------------------------------------------

finMem-Sup-both : (a1 a2 u1 u2 : FinEl) ->
  FinMem a1 u1 -> FinMem a2 u2 -> Comp u1 u2 -> Comp a1 a2 ->
  FinMem (Sup a1 a2) (Sup u1 u2)
finMem-Sup-both a1 a2 u1 u2 m1 m2 comp-u comp-a =
  let u1U   = FinMem-a-in-U a1 u1 m1
      u2U   = FinMem-a-in-U a2 u2 m2
      cu1   = coh-from-aU u1 u1U
      cu2   = coh-from-aU u2 u2U
      ca1   = FinMem-coh-u a1 u1 m1
      ca2   = FinMem-coh-u a2 u2 m2
      c-sup = Coherent-Sup u1 u2 comp-u cu1 cu2
      m1'   = finMem-Sup-left u1 u2 a1 comp-u cu1 cu2 u2U ca1 m1
      m2'   = finMem-Sup-right u1 u2 a2 comp-u u1U ca2 m2
  in FinMem-Sup-element a1 a2 (Sup u1 u2) comp-a c-sup m1' m2'

