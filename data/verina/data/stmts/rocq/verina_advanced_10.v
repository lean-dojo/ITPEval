(* Statement-only formalization of VERINA corpus artifact verina_advanced_10,
   catalog title "findExponents": executable extraction of the exponent of
   each supplied prime in a positive natural number's factorization, together
   with its reconstruction contract. This file contains no proof. *)

From Stdlib Require Import Arith.PeanoNat Lists.List.

Import ListNotations.

Fixpoint removePrimeFactor_fuel
    (fuel n p : nat) : nat :=
  match fuel with
  | O => n
  | S fuel' =>
      if Nat.ltb 1 p then
        if Nat.ltb 0 n then
          if Nat.eqb (Nat.modulo n p) 0 then
            removePrimeFactor_fuel fuel' (Nat.div n p) p
          else n
        else n
      else n
  end.

Definition removePrimeFactor (n p : nat) : nat :=
  removePrimeFactor_fuel n n p.

Definition removeAllPrimeFactors
    (n : nat) (primes : list nat) : nat :=
  fold_left
    (fun current p => removePrimeFactor current p)
    primes n.

Definition findExponents_prime (p : nat) : Prop :=
  (2 <= p)%nat /\
  forall d : nat, Nat.divide d p -> d = 1%nat \/ d = p.

Definition findExponents_precond
    (n : nat) (primes : list nat) : Prop :=
  (0 < n)%nat /\
  (0 < length primes)%nat /\
  Forall findExponents_prime primes /\
  NoDup primes /\
  removeAllPrimeFactors n primes = 1%nat.

Fixpoint findExponents_countFactor_fuel
    (fuel n p count : nat) : nat * nat :=
  match fuel with
  | O => (count, n)
  | S fuel' =>
      if Nat.ltb 0 n then
        if Nat.ltb 1 p then
          if Nat.eqb (Nat.modulo n p) 0 then
            findExponents_countFactor_fuel
              fuel' (Nat.div n p) p (S count)
          else (count, n)
        else (count, n)
      else (count, 0%nat)
  end.

Definition findExponents_countFactor
    (n p count : nat) : nat * nat :=
  findExponents_countFactor_fuel n n p count.

Fixpoint findExponents_countFactors
    (n : nat) (primes : list nat) : list (nat * nat) :=
  match primes with
  | [] => []
  | p :: ps =>
      let '(count, n') := findExponents_countFactor n p 0%nat in
      (p, count) :: findExponents_countFactors n' ps
  end.

Definition findExponents
    (n : nat)
    (primes : list nat)
    (_h_precond : findExponents_precond n primes)
    : list (nat * nat) :=
  findExponents_countFactors n primes.

Definition findExponents_reconstruct
    (result : list (nat * nat)) : nat :=
  fold_left
    (fun acc pe => acc * Nat.pow (fst pe) (snd pe))
    result 1%nat.

Definition findExponents_postcond
    (n : nat)
    (primes : list nat)
    (result : list (nat * nat))
    (_h_precond : findExponents_precond n primes) : Prop :=
  n = findExponents_reconstruct result /\
  Forall (fun pe => In (fst pe) primes) result /\
  Forall
    (fun p =>
      exists pe : nat * nat,
        In pe result /\ fst pe = p)
    primes.

Theorem findExponents_spec_satisfied
    (n : nat)
    (primes : list nat)
    (h_precond : findExponents_precond n primes) :
  findExponents_postcond
    n primes (findExponents n primes h_precond) h_precond.
Admitted.
