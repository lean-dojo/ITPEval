Require Import Factorial Reals Coquelicot.Coquelicot.
Definition putnam_2008_b2_solution := -1.

Theorem putnam_2008_b2
    (F : nat -> R -> R)
    (hF0 : forall x : R, x > 0 -> F 0%nat x = ln x)
    (hFn : forall (n : nat) (x : R),
      x > 0 ->
      is_RInt_gen (F n) (at_right 0) (at_point x) (F (S n) x)) :
  is_lim_seq
    (fun n => INR (fact n) * F n 1 / ln (INR n))
    putnam_2008_b2_solution.
Proof. Admitted.
