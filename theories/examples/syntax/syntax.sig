-- Regenerate syntax.v with:
--   autosubst -o syntax.v -s rocq -v ge813 -no-static syntax.sig

Tm(var) : Type 
abs     : Tm -> (bind Tm in Tm) -> Tm
app     : Tm -> Tm -> Tm
zero    : Tm
succ    : Tm -> Tm 
ncase   : Tm -> Tm -> (bind Tm in Tm) -> Tm
tnat    : Tm
tpi     : Tm -> (bind Tm in Tm) -> Tm
tuniv   : Tm   
fix_    : Tm -> Tm


tid     : Tm -> Tm -> Tm -> Tm
rfl     : Tm -> Tm
jcase   : Tm -> Tm -> Tm -> Tm


-- Sigma fragment (Agda SigmaProp/).  Only tsig binds; the pair and its two
-- projections are binder-free.
tsig    : Tm -> (bind Tm in Tm) -> Tm
mkpair  : Tm -> Tm -> Tm
pfst    : Tm -> Tm
psnd    : Tm -> Tm

-- Prop fragment (Agda SigmaProp/).  The second sort: binder-free, a leaf like
-- tuniv.  All its content is in the judgments (Prop : U, Prop-to-U subtyping,
-- Pi-into-Prop, and proof irrelevance) and in wt, where a type whose code is a
-- member of tprop has only bot as a member (wt_prop_bot).
tprop   : Tm

-- Unit fragment (unit_extension_plan.md).  Both binder-free leaves: tunit is
-- the type, tstar its element.  star has no informative realizer -- bot is the
-- only member of the code tunit (wt_unit_bot) -- which is exactly what makes
-- eta for unit (c_unit_eta) hold.
tunit   : Tm
tstar   : Tm
