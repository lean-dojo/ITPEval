(* Statement-only formalization of PutnamBench artifact putnam_1990_b4:
   a cyclic walk of length twice the order of a finite two-generated group,
   using right multiplication by either generator and visiting every element
   exactly twice. This file contains no proof. *)

From Stdlib Require Import Lists.List Arith.PeanoNat.

Record putnam_1990_b4_group (G : Type) : Type := {
  putnam_1990_b4_mul : G -> G -> G;
  putnam_1990_b4_one : G;
  putnam_1990_b4_inv : G -> G;
  putnam_1990_b4_assoc :
    forall x y z : G,
      putnam_1990_b4_mul x (putnam_1990_b4_mul y z) =
      putnam_1990_b4_mul (putnam_1990_b4_mul x y) z;
  putnam_1990_b4_left_identity :
    forall x : G, putnam_1990_b4_mul putnam_1990_b4_one x = x;
  putnam_1990_b4_right_identity :
    forall x : G, putnam_1990_b4_mul x putnam_1990_b4_one = x;
  putnam_1990_b4_left_inverse :
    forall x : G,
      putnam_1990_b4_mul (putnam_1990_b4_inv x) x =
      putnam_1990_b4_one;
  putnam_1990_b4_right_inverse :
    forall x : G,
      putnam_1990_b4_mul x (putnam_1990_b4_inv x) =
      putnam_1990_b4_one
}.

Arguments putnam_1990_b4_mul {G} _ _ _.
Arguments putnam_1990_b4_one {G} _.
Arguments putnam_1990_b4_inv {G} _ _.

Inductive putnam_1990_b4_generated
    {G : Type}
    (grp : putnam_1990_b4_group G)
    (S : G -> Prop) : G -> Prop :=
  | putnam_1990_b4_generated_one :
      putnam_1990_b4_generated grp S (putnam_1990_b4_one grp)
  | putnam_1990_b4_generated_member :
      forall x : G,
        S x ->
        putnam_1990_b4_generated grp S x
  | putnam_1990_b4_generated_mul :
      forall x y : G,
        putnam_1990_b4_generated grp S x ->
        putnam_1990_b4_generated grp S y ->
        putnam_1990_b4_generated grp S
          (putnam_1990_b4_mul grp x y)
  | putnam_1990_b4_generated_inv :
      forall x : G,
        putnam_1990_b4_generated grp S x ->
        putnam_1990_b4_generated grp S
          (putnam_1990_b4_inv grp x).

Definition putnam_1990_b4_exactly_twice
    {G : Type}
    (n : nat)
    (g : nat -> G)
    (x : G) : Prop :=
  exists i j : nat,
    (i < 2 * n)%nat /\
    (j < 2 * n)%nat /\
    i <> j /\
    g i = x /\
    g j = x /\
    forall k : nat,
      (k < 2 * n)%nat ->
      g k = x ->
      k = i \/ k = j.

Definition putnam_1990_b4_solution : Prop := True.

Theorem putnam_1990_b4 :
  (forall
      (G : Type)
      (grp : putnam_1990_b4_group G)
      (enumeration : list G)
      (n : nat)
      (a b : G),
    NoDup enumeration ->
    (forall x : G, In x enumeration) ->
    n = length enumeration ->
    (forall x : G,
      putnam_1990_b4_generated grp (fun y => y = a \/ y = b) x) ->
    ~ (forall x : G,
      putnam_1990_b4_generated grp (fun y => y = a) x) ->
    ~ (forall x : G,
      putnam_1990_b4_generated grp (fun y => y = b) x) ->
    exists g : nat -> G,
      (forall x : G, putnam_1990_b4_exactly_twice n g x) /\
      forall i : nat,
        (i < 2 * n)%nat ->
        g ((S i) mod (2 * n)) = putnam_1990_b4_mul grp (g i) a \/
        g ((S i) mod (2 * n)) = putnam_1990_b4_mul grp (g i) b)
  <-> putnam_1990_b4_solution.
Admitted.
