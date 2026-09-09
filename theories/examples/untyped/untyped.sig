nat : Type

Tm(var) : Type 
abs     : (bind Tm in Tm) -> Tm
app     : Tm -> Tm -> Tm
zero    : Tm
succ    : Tm -> Tm 
ifzero  : Tm -> (bind Tm in Tm) -> Tm -> Tm
nrec    : (bind Tm in Tm) -> Tm -> Tm -> Tm
disp    : nat -> Tm -> Tm 
aabs    : nat -> (bind Tm in Tm) -> Tm


