Class Field := {
  R0    : Type;
  zeroR : R0;
  oneR  : R0;
  addR  : R0 -> R0 -> R0;
  mulR  : R0 -> R0 -> R0;
  oppR  : R0 -> R0;
  addR_comm  : forall x y, addR x y = addR y x;
  addR_assoc : forall x y z, addR (addR x y) z = addR x (addR y z);
  addR_zero  : forall x, addR x zeroR = x;
  addR_opp   : forall x, addR x (oppR x) = zeroR;
  mulR_comm  : forall x y, mulR x y = mulR y x;
  mulR_assoc : forall x y z, mulR (mulR x y) z = mulR x (mulR y z);
  mulR_one   : forall x, mulR x oneR = x;
  distR_l    : forall a x y, mulR a (addR x y) = addR (mulR a x) (mulR a y)
}.

Section Lin.
  Context {F : Field}.
  Infix "+R" := addR (at level 65).
  Infix "*R" := mulR (at level 70).
  Notation "-R x" := (oppR x) (at level 100).

  Class VSpace := {
    V0    : Type;
    zeroV : V0;
    addV  : V0 -> V0 -> V0;
    oppV  : V0 -> V0;
    smul  : R0 -> V0 -> V0;
    addV_comm  : forall u v, addV u v = addV v u;
    addV_assoc : forall u v w, addV (addV u v) w = addV u (addV v w);
    addV_zero  : forall u, addV u zeroV = u;
    addV_opp   : forall u, addV u (oppV u) = zeroV;
    smul_addV  : forall a u v, smul a (addV u v) = addV (smul a u) (smul a v);
    addR_smul  : forall a b u, smul (a +R b) u = addV (smul a u) (smul b u);
    mul_smul   : forall a b u, smul (a *R b) u = smul a (smul b u);
    one_smul   : forall u, smul oneR u = u;
    smul_zeroV : forall a, smul a zeroV = zeroV
  }.

  Infix "+V" := addV (at level 65).
  Notation "a •V x" := (smul a x) (at level 70).

  Record Lin `{VS1 : VSpace} `{VS2 : VSpace} := {
    toFun    : V0 -> V0;
    map_add  : forall u v, toFun (u +V v) = addV (toFun u) (toFun v);
    map_smul : forall a u, toFun (a •V u) = smul a (toFun u)
  }.

  Definition ker `{VS1 : VSpace} `{VS2 : VSpace} (L : Lin) : V0 -> Prop :=
    fun x => toFun L x = zeroV.
  Definition im  `{VS1 : VSpace} `{VS2 : VSpace} (L : Lin) : V0 -> Prop :=
    fun y => exists x, toFun L x = y.

  Lemma ker_add `{VS1 : VSpace} `{VS2 : VSpace}
    (L : Lin) (x y : V0) :
    ker L x -> ker L y -> ker L (x +V y).
Proof.
Admitted.

  Lemma ker_smul `{VS1 : VSpace} `{VS2 : VSpace}
    (L : Lin) (a : R0) (x : V0) : ker L x -> ker L (a •V x).
Proof.
Admitted.

  Lemma im_add `{VS1 : VSpace} `{VS2 : VSpace}
    (L : Lin) (y z : V0) :
    im L y -> im L z -> im L (y +V z).
Proof.
Admitted.

  Lemma im_smul `{VS1 : VSpace} `{VS2 : VSpace}
    (L : Lin) (a : R0) (y : V0) :
    im L y -> im L (a •V y).
Proof.
Admitted.

End Lin.
