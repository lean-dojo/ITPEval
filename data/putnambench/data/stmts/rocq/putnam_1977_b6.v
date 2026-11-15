(* Statement-only formalization of PutnamBench artifact putnam_1977_b6:
   a finite subgroup H and an element a satisfying (x a)^3 = 1 yield at most
   3 h^2 nonempty products x1 a x2 a ... xn a. This file contains no proof. *)

From Stdlib Require Import Lists.List Arith.PeanoNat Ensembles Finite_sets.

Record putnam_1977_b6_group (G : Type) : Type := {
  putnam_1977_b6_mul : G -> G -> G;
  putnam_1977_b6_one : G;
  putnam_1977_b6_inv : G -> G;
  putnam_1977_b6_assoc :
    forall x y z : G,
      putnam_1977_b6_mul x (putnam_1977_b6_mul y z) =
      putnam_1977_b6_mul (putnam_1977_b6_mul x y) z;
  putnam_1977_b6_left_identity :
    forall x : G, putnam_1977_b6_mul putnam_1977_b6_one x = x;
  putnam_1977_b6_right_identity :
    forall x : G, putnam_1977_b6_mul x putnam_1977_b6_one = x;
  putnam_1977_b6_left_inverse :
    forall x : G,
      putnam_1977_b6_mul (putnam_1977_b6_inv x) x =
      putnam_1977_b6_one;
  putnam_1977_b6_right_inverse :
    forall x : G,
      putnam_1977_b6_mul x (putnam_1977_b6_inv x) =
      putnam_1977_b6_one
}.

Arguments putnam_1977_b6_mul {G} _ _ _.
Arguments putnam_1977_b6_one {G} _.
Arguments putnam_1977_b6_inv {G} _ _.

Definition putnam_1977_b6_is_subgroup
    {G : Type}
    (grp : putnam_1977_b6_group G)
    (H : Ensemble G) : Prop :=
  H (putnam_1977_b6_one grp) /\
  (forall x y : G,
    H x ->
    H y ->
    H (putnam_1977_b6_mul grp x y)) /\
  (forall x : G,
    H x ->
    H (putnam_1977_b6_inv grp x)).

Fixpoint putnam_1977_b6_power
    {G : Type}
    (grp : putnam_1977_b6_group G)
    (x : G)
    (n : nat) : G :=
  match n with
  | O => putnam_1977_b6_one grp
  | S k =>
      putnam_1977_b6_mul grp x (putnam_1977_b6_power grp x k)
  end.

Definition putnam_1977_b6_product
    {G : Type}
    (grp : putnam_1977_b6_group G)
    (a : G)
    (xs : list G) : G :=
  fold_right
    (fun x product : G =>
      putnam_1977_b6_mul grp
        (putnam_1977_b6_mul grp x a)
        product)
    (putnam_1977_b6_one grp)
    xs.

Theorem putnam_1977_b6
    (G : Type)
    (grp : putnam_1977_b6_group G)
    (H P : Ensemble G)
    (h : nat)
    (a : G)
    (hHsubgroup : putnam_1977_b6_is_subgroup grp H)
    (hHcard : cardinal G H h)
    (ha :
      forall x : G,
        H x ->
        putnam_1977_b6_power
          grp
          (putnam_1977_b6_mul grp x a)
          3 =
        putnam_1977_b6_one grp)
    (hP :
      forall g : G,
        P g <->
        exists xs : list G,
          xs <> nil /\
          Forall H xs /\
          g = putnam_1977_b6_product grp a xs) :
  Finite G P /\
  exists p : nat,
    cardinal G P p /\
    (p <= 3 * h ^ 2)%nat.
Admitted.
