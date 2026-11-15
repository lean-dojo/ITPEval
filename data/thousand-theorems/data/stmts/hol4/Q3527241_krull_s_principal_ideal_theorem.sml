(*
  Statement-only formalization of the Thousand Theorems corpus artifact
  Q3527241, "Krull's principal ideal theorem": in a commutative Noetherian
  ring, every prime ideal minimal over a principal ideal has height at most
  one. This file contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory pred_setTheory;

val q3527241_comm_ring_def = new_definition (
  "q3527241_comm_ring_def",
  ``q3527241_comm_ring
      (zero : 'r) (oneR : 'r)
      (add : 'r -> 'r -> 'r) (mul : 'r -> 'r -> 'r)
      (neg : 'r -> 'r) <=>
      (!x y z. add (add x y) z = add x (add y z)) /\
      (!x y. add x y = add y x) /\
      (!x. add zero x = x) /\
      (!x. add (neg x) x = zero) /\
      (!x y z. mul (mul x y) z = mul x (mul y z)) /\
      (!x y. mul x y = mul y x) /\
      (!x. mul oneR x = x) /\
      (!x y z. mul x (add y z) = add (mul x y) (mul x z))``);

val q3527241_ideal_def = new_definition (
  "q3527241_ideal_def",
  ``q3527241_ideal
      (zero : 'r) (add : 'r -> 'r -> 'r)
      (mul : 'r -> 'r -> 'r) (neg : 'r -> 'r)
      (ideal : 'r set) <=>
      zero IN ideal /\
      (!x y. x IN ideal /\ y IN ideal ==> add x y IN ideal) /\
      (!x. x IN ideal ==> neg x IN ideal) /\
      (!a x. x IN ideal ==> mul a x IN ideal)``);

val q3527241_span_def = new_definition (
  "q3527241_span_def",
  ``q3527241_span
      (zero : 'r) (add : 'r -> 'r -> 'r)
      (mul : 'r -> 'r -> 'r) (neg : 'r -> 'r)
      (s : 'r set) =
      {x |
        !other : 'r set.
          q3527241_ideal zero add mul neg other /\
          s SUBSET other
          ==>
          x IN other}``);

val q3527241_noetherian_def = new_definition (
  "q3527241_noetherian_def",
  ``q3527241_noetherian
      (zero : 'r) (add : 'r -> 'r -> 'r)
      (mul : 'r -> 'r -> 'r) (neg : 'r -> 'r) <=>
      !ideal : 'r set.
        q3527241_ideal zero add mul neg ideal
        ==>
        ?s : 'r set.
          FINITE s /\
          q3527241_span zero add mul neg s = ideal``);

val q3527241_principal_def = new_definition (
  "q3527241_principal_def",
  ``q3527241_principal
      (zero : 'r) (add : 'r -> 'r -> 'r)
      (mul : 'r -> 'r -> 'r) (neg : 'r -> 'r)
      (ideal : 'r set) <=>
      ?a : 'r.
        ideal = q3527241_span zero add mul neg {a}``);

val q3527241_prime_ideal_def = new_definition (
  "q3527241_prime_ideal_def",
  ``q3527241_prime_ideal
      (zero : 'r) (oneR : 'r)
      (add : 'r -> 'r -> 'r) (mul : 'r -> 'r -> 'r)
      (neg : 'r -> 'r) (p : 'r set) <=>
      q3527241_ideal zero add mul neg p /\
      ~(oneR IN p) /\
      (!x y. mul x y IN p ==> x IN p \/ y IN p)``);

val q3527241_minimal_prime_over_def = new_definition (
  "q3527241_minimal_prime_over_def",
  ``q3527241_minimal_prime_over
      (zero : 'r) (oneR : 'r)
      (add : 'r -> 'r -> 'r) (mul : 'r -> 'r -> 'r)
      (neg : 'r -> 'r) (ideal : 'r set) (p : 'r set) <=>
      q3527241_prime_ideal zero oneR add mul neg p /\
      ideal SUBSET p /\
      (!q : 'r set.
        q3527241_prime_ideal zero oneR add mul neg q /\
        ideal SUBSET q /\
        q SUBSET p
        ==>
        p SUBSET q)``);

val q3527241_height_le_one_def = new_definition (
  "q3527241_height_le_one_def",
  ``q3527241_height_le_one
      (zero : 'r) (oneR : 'r)
      (add : 'r -> 'r -> 'r) (mul : 'r -> 'r -> 'r)
      (neg : 'r -> 'r) (p : 'r set) <=>
      ~(?q r : 'r set.
        q3527241_prime_ideal zero oneR add mul neg q /\
        q3527241_prime_ideal zero oneR add mul neg r /\
        r PSUBSET q /\
        q PSUBSET p)``);

val Ideal_height_le_one_of_isPrincipal_of_mem_minimalPrimes =
  ``!(zero : 'r) (oneR : 'r)
      (add : 'r -> 'r -> 'r) (mul : 'r -> 'r -> 'r)
      (neg : 'r -> 'r) (ideal : 'r set) (p : 'r set).
      q3527241_comm_ring zero oneR add mul neg /\
      q3527241_noetherian zero add mul neg /\
      q3527241_ideal zero add mul neg ideal /\
      q3527241_principal zero add mul neg ideal /\
      q3527241_minimal_prime_over zero oneR add mul neg ideal p
      ==>
      q3527241_height_le_one zero oneR add mul neg p``;
