Require Import Nat.
Require Import Arith.
Require Import ZArith.


Definition is_prime (p : nat) := 
  p > 1 /\ forall n, 1 < n < p -> ~(exists k, n * k = p).


(* Products live in Z because the factors on the right are integer
   differences and must not use truncated natural subtraction. *)
Fixpoint zprod_from_1_to (f : nat -> Z) (n : nat) : Z :=
  match n with
  | 0 => 1%Z
  | S m => (zprod_from_1_to f m * f (S m))%Z
  end.


Theorem imo_1967_p3 :
  forall (k m n : nat) (c : nat -> nat),
    0 < k /\ 0 < m /\ 0 < n ->
    (forall s, c s = s * (s + 1)) ->
    is_prime (k + m + 1) ->
    n + 1 < k + m + 1 ->
    Z.divide
      (zprod_from_1_to (fun i => Z.of_nat (c i)) n)
      (zprod_from_1_to
        (fun i => (Z.of_nat (c ((m + i)%nat)) - Z.of_nat (c k))%Z) n).

Proof.
