Ty : Type
Tm : Type

E : Type

Unit : Ty
Pair : Ty -> Ty -> Ty
Sum : Ty -> Ty -> Ty
Abs : Ty -> Ty -> Ty
Mon : E -> Ty -> Ty

abs : (Tm -> Tm) -> Tm
app : Tm -> Tm -> Tm
unit : Tm
seq : Tm -> Tm -> Tm
pair : Tm -> Tm -> Tm
split : Tm -> (Tm -> Tm -> Tm) -> Tm
inl : Tm -> Tm
inr : Tm -> Tm
case : Tm -> (Tm -> Tm) -> (Tm -> Tm) -> Tm
ret :  Tm -> Tm
bind : Tm -> (Tm -> Tm) -> Tm
coerce : Tm -> Tm
tickT : Tm
