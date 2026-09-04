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
