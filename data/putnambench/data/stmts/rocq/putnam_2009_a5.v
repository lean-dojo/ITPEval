(* Statement-only formalization of PutnamBench corpus artifact putnam_2009_a5:
   nonexistence of a finite abelian group whose element orders have product
   2^2009; this file contains no proof. *)

From Stdlib Require Import Lists.List Arith.PeanoNat.

Record putnam_2009_a5_comm_group (G : Type) : Type := {
  putnam_2009_a5_mul : G -> G -> G;
  putnam_2009_a5_one : G;
  putnam_2009_a5_inv : G -> G;
  putnam_2009_a5_assoc :
    forall x y z : G,
      putnam_2009_a5_mul x (putnam_2009_a5_mul y z) =
      putnam_2009_a5_mul (putnam_2009_a5_mul x y) z;
  putnam_2009_a5_left_identity :
    forall x : G, putnam_2009_a5_mul putnam_2009_a5_one x = x;
  putnam_2009_a5_right_identity :
    forall x : G, putnam_2009_a5_mul x putnam_2009_a5_one = x;
  putnam_2009_a5_left_inverse :
    forall x : G,
      putnam_2009_a5_mul (putnam_2009_a5_inv x) x =
      putnam_2009_a5_one;
  putnam_2009_a5_right_inverse :
    forall x : G,
      putnam_2009_a5_mul x (putnam_2009_a5_inv x) =
      putnam_2009_a5_one;
  putnam_2009_a5_commutative :
    forall x y : G,
      putnam_2009_a5_mul x y = putnam_2009_a5_mul y x
}.

Arguments putnam_2009_a5_mul {G} _ _ _.
Arguments putnam_2009_a5_one {G} _.

Fixpoint putnam_2009_a5_pow
    {G : Type}
    (grp : putnam_2009_a5_comm_group G)
    (x : G)
    (n : nat) : G :=
  match n with
  | O => putnam_2009_a5_one grp
  | S k =>
      putnam_2009_a5_mul grp x
        (putnam_2009_a5_pow grp x k)
  end.

Definition putnam_2009_a5_has_order
    {G : Type}
    (grp : putnam_2009_a5_comm_group G)
    (x : G)
    (n : nat) : Prop :=
  (0 < n)%nat /\
  putnam_2009_a5_pow grp x n = putnam_2009_a5_one grp /\
  forall k : nat,
    (0 < k < n)%nat ->
    putnam_2009_a5_pow grp x k <> putnam_2009_a5_one grp.

Definition putnam_2009_a5_order_product
    {G : Type}
    (enumeration : list G)
    (ord : G -> nat) : nat :=
  fold_right Nat.mul 1 (map ord enumeration).

Definition putnam_2009_a5_solution : Prop := False.

Theorem putnam_2009_a5 :
  (exists
      (G : Type)
      (grp : putnam_2009_a5_comm_group G)
      (enumeration : list G)
      (ord : G -> nat),
    NoDup enumeration /\
    (forall g : G, In g enumeration) /\
    (forall g : G, putnam_2009_a5_has_order grp g (ord g)) /\
    putnam_2009_a5_order_product enumeration ord = Nat.pow 2 2009)
  <-> putnam_2009_a5_solution.
Admitted.
