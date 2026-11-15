(* Statement-only formalization of PutnamBench artifact putnam_2007_a5:
   in a finite group, the number of elements of a given prime order is zero
   or one less than a multiple of that prime. This file contains no proof. *)

From mathcomp Require Import all_ssreflect.

Record putnam_2007_a5_group (G : finType) : Type := {
  group_mul : G -> G -> G;
  group_one : G;
  group_inv : G -> G;
  group_assoc :
    forall x y z : G,
      group_mul x (group_mul y z) = group_mul (group_mul x y) z;
  group_left_identity :
    forall x : G, group_mul group_one x = x;
  group_right_identity :
    forall x : G, group_mul x group_one = x;
  group_left_inverse :
    forall x : G, group_mul (group_inv x) x = group_one;
  group_right_inverse :
    forall x : G, group_mul x (group_inv x) = group_one
}.

Arguments group_mul {G} _ _ _.
Arguments group_one {G} _.

Fixpoint group_pow
    {G : finType}
    (grp : putnam_2007_a5_group G)
    (x : G)
    (k : nat) : G :=
  match k with
  | 0 => group_one grp
  | k'.+1 => group_mul grp x (group_pow grp x k')
  end.

Definition has_order
    {G : finType}
    (grp : putnam_2007_a5_group G)
    (x : G)
    (p : nat) : bool :=
  (group_pow grp x p == group_one grp) &&
  all
    (fun k : nat => group_pow grp x k != group_one grp)
    (iota 1 p.-1).

Theorem putnam_2007_a5
    (G : finType)
    (grp : putnam_2007_a5_group G)
    (p n : nat)
    (hp : prime p)
    (hn : n = #|[set g : G | has_order grp g p]|) :
  n = 0 \/ p %| n.+1.
Admitted.
