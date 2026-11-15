(* Statement-only formalization of PutnamBench artifact putnam_2000_a5:
   three distinct integer lattice points on a circle have two points separated
   by at least the real cube root of the radius. This file contains no proof. *)

From Stdlib Require Import Vectors.Fin Reals ZArith.

Open Scope R_scope.

Definition putnam_2000_a5_point := (R * R)%type.

Definition putnam_2000_a5_distance
    (p q : putnam_2000_a5_point) : R :=
  sqrt ((fst p - fst q) ^ 2 + (snd p - snd q) ^ 2).

Definition putnam_2000_a5_integer_point
    (p : putnam_2000_a5_point) : Prop :=
  exists a b : Z,
    fst p = IZR a /\ snd p = IZR b.

Theorem putnam_2000_a5
    (r : R)
    (z : putnam_2000_a5_point)
    (p : Fin.t 3 -> putnam_2000_a5_point)
    (rpos : r > 0)
    (pdiff :
      forall n m : Fin.t 3,
        n <> m -> p n <> p m)
    (pint :
      forall n : Fin.t 3,
        putnam_2000_a5_integer_point (p n))
    (pcirc :
      forall n : Fin.t 3,
        putnam_2000_a5_distance (p n) z = r) :
  exists n m : Fin.t 3,
    n <> m /\
    putnam_2000_a5_distance (p n) (p m) >= Rpower r (1 / 3).
Admitted.
