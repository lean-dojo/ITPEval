Require Import Reals Coquelicot.Coquelicot.
Definition putnam_2022_a1_solution : R -> R -> Prop :=
  fun a b =>
    (a = 0 /\ b = 0) \/
    Rabs a >= 1 \/
    (0 < Rabs a < 1 /\
      let rm := (1 - sqrt (1 - a ^ 2)) / a in
      let rp := (1 + sqrt (1 - a ^ 2)) / a in
      (b < ln (1 + rm ^ 2) - a * rm \/
       b > ln (1 + rp ^ 2) - a * rp)).

Theorem putnam_2022_a1 
    : forall a b : R,
      (exists! x : R, a * x + b = ln (1 + x ^ 2)) <->
      putnam_2022_a1_solution a b.
Proof. Admitted.
