(*
  Statement-only formalization of Thousand Theorems corpus artifact Q288465
  (thousand-theorems__rocq__Q288465), "Orbit-stabilizer theorem": for an
  arbitrary group action, the orbit of a point is equivalent to the quotient
  of the acting group by that point's stabilizer. This file contains no proof.
*)

Set Universe Polymorphism.
Unset Implicit Arguments.

Record q288465_group (G : Type) : Type := {
  q288465_mul : G -> G -> G;
  q288465_one : G;
  q288465_inv : G -> G;
  q288465_mul_assoc :
    forall x y z : G,
      q288465_mul x (q288465_mul y z) =
      q288465_mul (q288465_mul x y) z;
  q288465_one_mul :
    forall x : G, q288465_mul q288465_one x = x;
  q288465_mul_one :
    forall x : G, q288465_mul x q288465_one = x;
  q288465_inv_mul :
    forall x : G, q288465_mul (q288465_inv x) x = q288465_one;
  q288465_mul_inv :
    forall x : G, q288465_mul x (q288465_inv x) = q288465_one
}.

Arguments q288465_mul {G} _ _ _.
Arguments q288465_one {G} _.
Arguments q288465_inv {G} _ _.

Record q288465_mul_action
    (G X : Type)
    (grp : q288465_group G) : Type := {
  q288465_act : G -> X -> X;
  q288465_one_act :
    forall x : X, q288465_act (q288465_one grp) x = x;
  q288465_mul_act :
    forall (g h : G) (x : X),
      q288465_act (q288465_mul grp g h) x =
      q288465_act g (q288465_act h x)
}.

Arguments q288465_act {G X grp} _ _ _.

Definition q288465_orbit
    {G X : Type}
    {grp : q288465_group G}
    (action : q288465_mul_action G X grp)
    (b y : X) : Prop :=
  exists g : G, q288465_act action g b = y.

Definition q288465_stabilizer
    {G X : Type}
    {grp : q288465_group G}
    (action : q288465_mul_action G X grp)
    (b : X)
    (g : G) : Prop :=
  q288465_act action g b = b.

Definition q288465_orbit_type
    {G X : Type}
    {grp : q288465_group G}
    (action : q288465_mul_action G X grp)
    (b : X) : Type :=
  { y : X | q288465_orbit action b y }.

Definition q288465_orbit_equal
    {G X : Type}
    {grp : q288465_group G}
    {action : q288465_mul_action G X grp}
    {b : X}
    (x y : q288465_orbit_type action b) : Prop :=
  proj1_sig x = proj1_sig y.

Definition q288465_quotient_equal
    {G X : Type}
    (grp : q288465_group G)
    (action : q288465_mul_action G X grp)
    (b : X)
    (g h : G) : Prop :=
  q288465_stabilizer action b
    (q288465_mul grp (q288465_inv grp g) h).

Definition q288465_setoid_equivalent
    (A B : Type)
    (equalA : A -> A -> Prop)
    (equalB : B -> B -> Prop) : Prop :=
  exists forward : A -> B, exists backward : B -> A,
    (forall x y : A,
      equalA x y -> equalB (forward x) (forward y)) /\
    (forall x y : B,
      equalB x y -> equalA (backward x) (backward y)) /\
    (forall x : A, equalA (backward (forward x)) x) /\
    (forall y : B, equalB (forward (backward y)) y).

Theorem MulAction_orbitEquivQuotientStabilizer :
  forall (G X : Type)
         (grp : q288465_group G)
         (action : q288465_mul_action G X grp)
         (b : X),
    q288465_setoid_equivalent
      (q288465_orbit_type action b)
      G
      q288465_orbit_equal
      (q288465_quotient_equal grp action b).
Admitted.
