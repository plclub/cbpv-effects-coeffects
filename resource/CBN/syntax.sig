Ty : Type
Tm : Type
Q : Type

Unit : Ty
Sum : Ty -> Ty -> Ty
With : Ty -> Ty -> Ty
Abs : Q -> Ty -> Ty -> Ty
Box : Q -> Ty -> Ty

abs : Q -> (Tm -> Tm) -> Tm
app : Tm -> Tm -> Tm
unit : Tm
seq : Tm -> Tm -> Tm
inl : Tm -> Tm
inr : Tm -> Tm
prod : Tm -> Tm -> Tm
fst : Tm -> Tm
snd : Tm -> Tm
case : Q -> Tm -> (Tm -> Tm) -> (Tm -> Tm) -> Tm
box : Q -> Tm -> Tm
unbox : Q -> Tm -> (Tm -> Tm) -> Tm
