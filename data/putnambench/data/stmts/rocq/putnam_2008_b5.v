Require Import Reals QArith Coquelicot.Coquelicot. From mathcomp Require Import div.
Open Scope R.
Definition putnam_2008_b5_solution (f : R -> R) := exists n : Z, f = (fun x => x + IZR n) \/ f = (fun x => -x + IZR n).
Theorem putnam_2008_b5
    (f: R -> R)
    (hf : (forall x: R, ex_derive f x) /\ continuity (Derive f))
    : (forall q : Q,
        exists p : Q,
          Q2R p = f (Q2R q) /\
          Qden (Qred p) = Qden (Qred q)) <->
      putnam_2008_b5_solution f.
Proof. Admitted.
