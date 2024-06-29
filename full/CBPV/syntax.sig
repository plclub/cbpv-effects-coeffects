ValTy : Type
CompTy : Type
Val : Type
Comp : Type
Q : Type
E : Type

VUnit : ValTy
VThunk : E -> CompTy -> ValTy
VPair : ValTy -> ValTy -> ValTy
VSum : ValTy -> ValTy -> ValTy

CAbs : Q -> ValTy -> CompTy -> CompTy
CF : Q -> ValTy -> CompTy
CPair : CompTy -> CompTy -> CompTy

vUnit : Val
vThunk : Comp -> Val
vPair : Val -> Val -> Val
vInl : Val -> Val
vInr : Val -> Val

cAbs : Q -> (Val -> Comp) -> Comp
cApp : Comp -> Val -> Comp
cForce : Val -> Comp
cSplit : Q -> Val -> (Val -> Val -> Comp) -> Comp
cRet : Q -> Val -> Comp
cLet : Q -> Comp -> (Val -> Comp) -> Comp
cPair : Comp -> Comp -> Comp
cFst : Comp -> Comp
cSnd : Comp -> Comp
cSeq : Val -> Comp -> Comp
cCase : Q -> Val -> (Val -> Comp) -> (Val -> Comp) -> Comp
cTick : Comp
cLet0 : Comp -> (Val -> Comp) -> Comp
