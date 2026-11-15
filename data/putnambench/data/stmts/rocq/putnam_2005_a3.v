Require Import Reals Coquelicot.Coquelicot. From Coqtail Require Import Cpow Canalysis_def.
Theorem putnam_2005_a3
    (csqrt : C -> C)
    (c : nat -> C)
    (n : nat)
    (hn : gt n 0)
    (hdegree : c n <> 0)
    (p : C -> C := fun z : C => sum_n (fun i => c i * z^i) n)
    (g : C -> C := fun z : C => p z / csqrt (z^n))
    (pzeros : forall z : C, p z = 0 -> norm z = 1%R)
    (hcsqrt : forall z : C, (csqrt z)^2 = z /\ Re (csqrt z) >= 0 /\ (Re (csqrt z) = 0%R -> Im (csqrt z) >= 0%R)) 
    : forall z : C,
      z <> 0 ->
      Canalysis_def.derivable_pt_lim g z 0 ->
      norm z = 1%R.
Proof. Admitted.
