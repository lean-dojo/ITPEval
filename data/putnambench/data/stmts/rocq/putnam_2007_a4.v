Require Import Reals Zpower Coquelicot.Coquelicot.

Definition putnam_2007_a4_solution (f : R -> R) : Prop :=
  exists (c : Z) (d : nat),
    (1 - Z.of_nat d <= c)%Z /\
    forall x : R,
      f x = (powerRZ 10 c * (9 * x + 1) ^ d - 1) / 9.

Theorem putnam_2007_a4
    (repunit : R -> Prop := fun n => n = IZR (floor n) /\ n > 0 /\ exists (m: nat), n = sum_n (fun i => 10 ^ i) m)
    (c: nat -> R)
    (n: nat)
    (f : R -> R := fun x => sum_n (fun i => c i * x ^ i) n)
    : (forall (n: nat), repunit (INR n) -> repunit (f (INR n))) <-> putnam_2007_a4_solution f.
Proof. Admitted.
