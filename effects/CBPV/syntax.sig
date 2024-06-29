ValTy : Type
CompTy : Type
Val : Type
Comp : Type
E : Type

VUnit : ValTy
VThunk : E -> CompTy -> ValTy
VPair : ValTy -> ValTy -> ValTy
VSum : ValTy -> ValTy -> ValTy

CAbs : ValTy -> CompTy -> CompTy
CF : ValTy -> CompTy
CPair : CompTy -> CompTy -> CompTy

vUnit : Val
vThunk : Comp -> Val
vPair : Val -> Val -> Val
vInl : Val -> Val
vInr : Val -> Val

cAbs : (Val -> Comp) -> Comp
cApp : Comp -> Val -> Comp
cForce : Val -> Comp
cSplit : Val -> (Val -> Val -> Comp) -> Comp
cRet : Val -> Comp
cLet : Comp -> (Val -> Comp) -> Comp
cPair : Comp -> Comp -> Comp
cFst : Comp -> Comp
cSnd : Comp -> Comp
cSeq : Val -> Comp -> Comp
cCase : Val -> (Val -> Comp) -> (Val -> Comp) -> Comp
cTick : Comp
