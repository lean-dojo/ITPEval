(* Statement-only formalization of PutnamBench corpus artifact putnam_2011_b2:
   the primes occurring in at least seven prime-coefficient quadratic triples
   that admit a rational root; this file contains no proof. *)

From Stdlib Require Import Arith.PeanoNat Lists.List QArith ZArith.Znumtheory.

Open Scope Q_scope.

Record putnam_2011_b2_triple : Type := {
  putnam_2011_b2_p : nat;
  putnam_2011_b2_q : nat;
  putnam_2011_b2_r : nat
}.

Definition putnam_2011_b2_prime (n : nat) : Prop :=
  prime (Z.of_nat n).

Definition putnam_2011_b2_has_rational_root
    (s : putnam_2011_b2_triple) : Prop :=
  exists x : Q,
    inject_Z (Z.of_nat (putnam_2011_b2_p s)) * x ^ 2 +
    inject_Z (Z.of_nat (putnam_2011_b2_q s)) * x +
    inject_Z (Z.of_nat (putnam_2011_b2_r s)) = 0.

Definition putnam_2011_b2_contains
    (s : putnam_2011_b2_triple) (t : nat) : Prop :=
  putnam_2011_b2_p s = t \/
  putnam_2011_b2_q s = t \/
  putnam_2011_b2_r s = t.

Definition putnam_2011_b2_has_at_least
    {A : Type} (P : A -> Prop) (minimum : nat) : Prop :=
  exists witnesses : list A,
    length witnesses = minimum /\
    NoDup witnesses /\
    Forall P witnesses.

Definition putnam_2011_b2_solution (t : nat) : Prop :=
  t = 2%nat \/ t = 5%nat.

Theorem putnam_2011_b2
    (S : putnam_2011_b2_triple -> Prop)
    (t : nat)
    (hS :
      forall s : putnam_2011_b2_triple,
        S s <->
        putnam_2011_b2_prime (putnam_2011_b2_p s) /\
        putnam_2011_b2_prime (putnam_2011_b2_q s) /\
        putnam_2011_b2_prime (putnam_2011_b2_r s) /\
        putnam_2011_b2_has_rational_root s) :
  (putnam_2011_b2_prime t /\
   putnam_2011_b2_has_at_least
     (fun s : putnam_2011_b2_triple =>
        S s /\ putnam_2011_b2_contains s t)
     7%nat) <->
  putnam_2011_b2_solution t.
Admitted.
