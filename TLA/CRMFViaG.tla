------------------------------- MODULE CRMFViaG -------------------------------
EXTENDS MessageConcrete

LEMMA CRMFViaG ==
  ASSUME NEW F(_,_), NEW R(_), NEW z
  PROVE  CRecursiveFunc(F, R, z) = CGFun(F, R)[CMinLevel(z)][z]
BY DEF CRecursiveFunc, CGFun
=============================================================================
