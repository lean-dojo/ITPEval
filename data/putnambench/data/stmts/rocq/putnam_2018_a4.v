(* Statement-only formalization of PutnamBench corpus artifact putnam_2018_a4:
   a coprime floor-difference word in two elements of an arbitrary group
   implies that the two elements commute. This file contains no proof. *)

From Stdlib Require Import Reals ZArith Arith.PeanoNat.

Open Scope R_scope.

Record putnam_2018_a4_group (G : Type) : Type := {
  putnam_2018_a4_mul : G -> G -> G;
  putnam_2018_a4_one : G;
  putnam_2018_a4_inv : G -> G;
  putnam_2018_a4_assoc :
    forall x y z : G,
      putnam_2018_a4_mul x (putnam_2018_a4_mul y z) =
      putnam_2018_a4_mul (putnam_2018_a4_mul x y) z;
  putnam_2018_a4_left_identity :
    forall x : G, putnam_2018_a4_mul putnam_2018_a4_one x = x;
  putnam_2018_a4_right_identity :
    forall x : G, putnam_2018_a4_mul x putnam_2018_a4_one = x;
  putnam_2018_a4_left_inverse :
    forall x : G,
      putnam_2018_a4_mul (putnam_2018_a4_inv x) x =
      putnam_2018_a4_one;
  putnam_2018_a4_right_inverse :
    forall x : G,
      putnam_2018_a4_mul x (putnam_2018_a4_inv x) =
      putnam_2018_a4_one
}.

Arguments putnam_2018_a4_mul {G} _ _ _.
Arguments putnam_2018_a4_one {G} _.
Arguments putnam_2018_a4_inv {G} _ _.

Fixpoint putnam_2018_a4_nat_pow
    {G : Type}
    (grp : putnam_2018_a4_group G)
    (x : G)
    (n : nat) : G :=
  match n with
  | O => putnam_2018_a4_one grp
  | S k =>
      putnam_2018_a4_mul grp x
        (putnam_2018_a4_nat_pow grp x k)
  end.

Definition putnam_2018_a4_zpow
    {G : Type}
    (grp : putnam_2018_a4_group G)
    (x : G)
    (n : Z) : G :=
  match n with
  | Z0 => putnam_2018_a4_one grp
  | Zpos p =>
      putnam_2018_a4_nat_pow grp x (Pos.to_nat p)
  | Zneg p =>
      putnam_2018_a4_inv grp
        (putnam_2018_a4_nat_pow grp x (Pos.to_nat p))
  end.

Fixpoint putnam_2018_a4_product_from
    {G : Type}
    (grp : putnam_2018_a4_group G)
    (term : nat -> G)
    (start count : nat) : G :=
  match count with
  | O => putnam_2018_a4_one grp
  | S remaining =>
      putnam_2018_a4_mul grp
        (term start)
        (putnam_2018_a4_product_from
          grp term (S start) remaining)
  end.

Theorem putnam_2018_a4
    (m n : nat)
    (a : nat -> Z)
    (G : Type)
    (grp : putnam_2018_a4_group G)
    (g h : G)
    (mnpos : (0 < m)%nat /\ (0 < n)%nat)
    (mngcd : Nat.gcd m n = 1%nat)
    (ha :
      forall k : nat,
        (1 <= k <= n)%nat ->
        a k =
          (Zfloor ((INR m * INR k / INR n)%R) -
           Zfloor ((INR m * INR (Nat.pred k) / INR n)%R))%Z)
    (ghprod :
      putnam_2018_a4_product_from
        grp
        (fun k : nat =>
          putnam_2018_a4_mul grp g
            (putnam_2018_a4_zpow grp h (a k)))
        1%nat n =
      putnam_2018_a4_one grp) :
  putnam_2018_a4_mul grp g h =
  putnam_2018_a4_mul grp h g.
Admitted.
