(* Statement-only formalization of PutnamBench corpus artifact putnam_2012_a4:
   integers selected from a real interval by a congruence condition form a
   finite arithmetic progression when the interval-length product is small;
   this file contains no proof. *)

From Stdlib Require Import Reals ZArith Arith.PeanoNat.

Open Scope R_scope.

Definition putnam_2012_a4_in_interval
    (lower upper : R) (x : Z) : Prop :=
  lower <= IZR x <= upper.

Definition putnam_2012_a4_T
    (q : Z) (B0 B1 : R) (x : Z) : Prop :=
  exists b m : Z,
    putnam_2012_a4_in_interval B0 B1 b /\
    x = (b + m * q)%Z.

Definition putnam_2012_a4_S
    (q r : Z) (A0 A1 B0 B1 : R) (a : Z) : Prop :=
  putnam_2012_a4_in_interval A0 A1 a /\
  putnam_2012_a4_T q B0 B1 (r * a)%Z.

Definition putnam_2012_a4_finite_arithmetic_progression
    (P : Z -> Prop) : Prop :=
  exists (n : nat) (a d : Z),
    (0 < d)%Z /\
    forall x : Z,
      P x <->
      exists i : nat,
        (i < n)%nat /\
        x = (a + Z.of_nat i * d)%Z.

Theorem putnam_2012_a4
    (q r : Z)
    (A0 A1 B0 B1 : R)
    (qpos : (0 < q)%Z)
    (ABlt : A0 < A1 /\ B0 < B1)
    (prod_lt : (A1 - A0) * (B1 - B0) < IZR q) :
  putnam_2012_a4_finite_arithmetic_progression
    (fun x : Z =>
      putnam_2012_a4_S q r A0 A1 B0 B1 x /\
      putnam_2012_a4_in_interval A0 A1 x).
Admitted.
