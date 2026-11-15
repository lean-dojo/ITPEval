(* Statement-only formalization over an arbitrary group. *)

From Coq Require Import Arith.PeanoNat.

Record putnam_1972_b3_group (G : Type) : Type := {
  putnam_1972_b3_mul : G -> G -> G;
  putnam_1972_b3_one : G;
  putnam_1972_b3_inv : G -> G;
  putnam_1972_b3_assoc :
    forall x y z : G,
      putnam_1972_b3_mul x (putnam_1972_b3_mul y z) =
      putnam_1972_b3_mul (putnam_1972_b3_mul x y) z;
  putnam_1972_b3_left_identity :
    forall x : G, putnam_1972_b3_mul putnam_1972_b3_one x = x;
  putnam_1972_b3_right_identity :
    forall x : G, putnam_1972_b3_mul x putnam_1972_b3_one = x;
  putnam_1972_b3_left_inverse :
    forall x : G,
      putnam_1972_b3_mul (putnam_1972_b3_inv x) x =
      putnam_1972_b3_one;
  putnam_1972_b3_right_inverse :
    forall x : G,
      putnam_1972_b3_mul x (putnam_1972_b3_inv x) =
      putnam_1972_b3_one
}.

Arguments putnam_1972_b3_mul {G} _ _ _.
Arguments putnam_1972_b3_one {G} _.

Fixpoint putnam_1972_b3_pow
    {G : Type}
    (grp : putnam_1972_b3_group G)
    (x : G)
    (n : nat) : G :=
  match n with
  | O => putnam_1972_b3_one grp
  | S k => putnam_1972_b3_mul grp x (putnam_1972_b3_pow grp x k)
  end.

Theorem putnam_1972_b3
    (G : Type)
    (grp : putnam_1972_b3_group G)
    (A B : G)
    (hab :
      putnam_1972_b3_mul grp (putnam_1972_b3_mul grp A B) A =
        putnam_1972_b3_mul grp
          (putnam_1972_b3_mul grp B (putnam_1972_b3_pow grp A 2))
          B /\
      putnam_1972_b3_pow grp A 3 = putnam_1972_b3_one grp /\
      exists n : nat,
        n > 0 /\
        putnam_1972_b3_pow grp B (2 * n - 1) =
          putnam_1972_b3_one grp) :
  B = putnam_1972_b3_one grp.
Admitted.
