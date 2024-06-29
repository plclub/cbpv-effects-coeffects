Ty : Type
Tm : Type

Q : Type

Unit : Ty
Pair : Ty -> Ty -> Ty
Sum : Ty -> Ty -> Ty
Abs : Q -> Ty -> Ty -> Ty
Box : Q -> Ty -> Ty

abs : Q -> (Tm -> Tm) -> Tm
app : Q -> Tm -> Tm -> Tm
unit : Tm
seq : Tm -> Tm -> Tm
pair : Tm -> Tm -> Tm
split : Q -> Tm -> (Tm -> Tm -> Tm) -> Tm
inl : Tm -> Tm
inr : Tm -> Tm
case : Q -> Tm -> (Tm -> Tm) -> (Tm -> Tm) -> Tm
box : Q -> Tm -> Tm
unbox : Q -> Tm -> (Tm -> Tm) -> Tm
