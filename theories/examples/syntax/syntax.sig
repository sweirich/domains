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


