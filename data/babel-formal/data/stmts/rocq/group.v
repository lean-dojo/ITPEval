Class Group (G : Type) := {
  inv : G -> G;
  one : G;
  mul : G -> G -> G;
  mul_assoc : forall a b c, mul a (mul b  c) = mul (mul a b) c;
  mul_one   : forall a, mul a one = a;
  one_mul   : forall a, mul one a = a;
  mul_inv_l : forall a, mul (inv a) a = one;
  mul_inv_r : forall a, mul a (inv a) = one
}.

Infix "*" := mul (at level 40, left associativity).
Notation "1" := one.
Notation "x ^-1" := (inv x) (at level 35, right associativity).


Class GroupComm   (G : Type) `{Group G} := {
  mul_comm : forall a b, a * b = b * a
}.

Section MulRotate.
  Variable G : Type.
  Context `{GroupComm G}.

  Lemma mul_rotate' (a b c : G) : a * (b * c) = b * (c * a).
Proof.
Admitted.
End MulRotate.

Section GroupLemmas.
  Context {G : Type} `{Group G}.

  Lemma mul_left_cancel (a b c : G) :
        a * b = a * c -> b = c.
Proof.
Admitted.

  Lemma mul_right_cancel (a b c : G) :
        b * a = c * a -> b = c.
Proof.
Admitted.

  Lemma inv_inv (a : G) : (a^-1)^-1 = a.
Proof.
Admitted.

  Lemma inv_mul (a b : G) :
        (a * b)^-1 = b^-1 * a^-1.
Proof.
Admitted.

  Lemma inv_eq_of_mul_eq_one (a b : G) :
        a * b = 1 -> b = a^-1.
Proof.
Admitted.

End GroupLemmas.

Class Act (G X : Type) `{Group G}:= 
{
  act : G -> X -> X;
  act_one : forall x, act 1 x = x;
  act_mul : forall g h x, act (g * h) x = act g  (act h x)

}.
Infix "•" := act (at level 50, left associativity).


Section ActionLemmas.
  Context {G X : Type} `{Act G X}.

  Lemma act_inv (g : G) (x : X) :
        g^-1 • (g • x) = x.
Proof.
Admitted.

  Lemma act_inv_r (g : G) (x : X) :
        g • (g^-1 • x) = x.
Proof.
Admitted.

  Definition orbit (x : X) : X -> Prop :=
    fun y => exists g : G, g • x = y.

  Definition stabilizer (x : X) : G -> Prop :=
    fun g => g • x = x.

  Lemma orbit_refl (x : X) : orbit x x.
Proof.
Admitted.

  Lemma orbit_sym (x y : X) :
        orbit x y -> orbit y x.
Proof.
Admitted.

  Lemma orbit_trans (x y z : X) :
        orbit x y -> orbit y z -> orbit x z.
Proof.
Admitted.

  Lemma orbit_partition (x y : X) :
        orbit x y -> forall z, orbit x z <-> orbit y z.
Proof.
Admitted.

  Lemma stabilizer_mul (x : X) (g h : G) :
        stabilizer x g -> stabilizer x h -> stabilizer x (g * h).
Proof.
Admitted.

  Lemma stabilizer_inv (x : X) (g : G) :
        stabilizer x g -> stabilizer x (g^-1).
Proof.
Admitted.

  Lemma stabilizer_one (x : X) :
        stabilizer x 1.
Proof.
Admitted.

  Lemma stabilizer_conjugate (x : X) (g h : G) :
        stabilizer x h -> stabilizer (g • x) (g * h * g^-1).
Proof.
Admitted.

  Lemma stabilizer_conjugate_orbit (x y : X) (g : G) :
        g • x = y ->
        forall h, stabilizer y h <-> stabilizer x (g^-1 * h * g).
Proof.
Admitted.

End ActionLemmas.
