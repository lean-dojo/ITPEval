(*
  Statement-only formalization of the Thousand Theorems corpus artifact
  Q2379132, "Going-up and going-down theorems". It states the two indexed
  going-up results, the prime-spectrum characterization of going-down, and
  the localized-spectrum surjectivity criterion. This file contains no proof.
*)

open HolKernel Parse boolLib;
open listTheory;

val q2379132_comm_ring_def = new_definition (
  "q2379132_comm_ring_def",
  ``q2379132_comm_ring
      (zero : 'a) (oneA : 'a)
      (add : 'a -> 'a -> 'a) (mul : 'a -> 'a -> 'a)
      (neg : 'a -> 'a) <=>
      (!x y z. add (add x y) z = add x (add y z)) /\
      (!x y. add x y = add y x) /\
      (!x. add zero x = x) /\
      (!x. add (neg x) x = zero) /\
      (!x y z. mul (mul x y) z = mul x (mul y z)) /\
      (!x y. mul x y = mul y x) /\
      (!x. mul oneA x = x) /\
      (!x y z. mul x (add y z) = add (mul x y) (mul x z))``);

val q2379132_integral_domain_def = new_definition (
  "q2379132_integral_domain_def",
  ``q2379132_integral_domain
      (zero : 'a) (oneA : 'a)
      (add : 'a -> 'a -> 'a) (mul : 'a -> 'a -> 'a)
      (neg : 'a -> 'a) <=>
      q2379132_comm_ring zero oneA add mul neg /\
      zero <> oneA /\
      (!x y. mul x y = zero ==> x = zero \/ y = zero)``);

val q2379132_ring_hom_def = new_definition (
  "q2379132_ring_hom_def",
  ``q2379132_ring_hom
      (Rzero : 'r) (Rone : 'r)
      (Radd : 'r -> 'r -> 'r) (Rmul : 'r -> 'r -> 'r)
      (Szero : 's) (Sone : 's)
      (Sadd : 's -> 's -> 's) (Smul : 's -> 's -> 's)
      (f : 'r -> 's) <=>
      f Rzero = Szero /\
      f Rone = Sone /\
      (!x y. f (Radd x y) = Sadd (f x) (f y)) /\
      (!x y. f (Rmul x y) = Smul (f x) (f y))``);

val q2379132_ideal_def = new_definition (
  "q2379132_ideal_def",
  ``q2379132_ideal
      (zero : 'a) (add : 'a -> 'a -> 'a)
      (mul : 'a -> 'a -> 'a) (neg : 'a -> 'a)
      (idealA : 'a -> bool) <=>
      idealA zero /\
      (!x y. idealA x /\ idealA y ==> idealA (add x y)) /\
      (!x. idealA x ==> idealA (neg x)) /\
      (!a x. idealA x ==> idealA (mul a x))``);

val q2379132_prime_ideal_def = new_definition (
  "q2379132_prime_ideal_def",
  ``q2379132_prime_ideal
      (zero : 'a) (oneA : 'a)
      (add : 'a -> 'a -> 'a) (mul : 'a -> 'a -> 'a)
      (neg : 'a -> 'a) (idealA : 'a -> bool) <=>
      q2379132_ideal zero add mul neg idealA /\
      ~idealA oneA /\
      (!x y. idealA (mul x y) ==> idealA x \/ idealA y)``);

val q2379132_poly_eval_def = new_definition (
  "q2379132_poly_eval_def",
  ``q2379132_poly_eval
      (Szero : 's) (Sadd : 's -> 's -> 's)
      (Smul : 's -> 's -> 's) (f : 'r -> 's)
      (coeff : 'r list) (x : 's) =
      FOLDR (\c acc. Sadd (f c) (Smul x acc)) Szero coeff``);

val q2379132_integral_extension_def = new_definition (
  "q2379132_integral_extension_def",
  ``q2379132_integral_extension
      (Rone : 'r)
      (Szero : 's) (Sadd : 's -> 's -> 's)
      (Smul : 's -> 's -> 's) (f : 'r -> 's) <=>
      !x : 's.
        ?coeff : 'r list.
          coeff <> [] /\
          LAST coeff = Rone /\
          q2379132_poly_eval Szero Sadd Smul f coeff x = Szero``);

val q2379132_ideal_included_def = new_definition (
  "q2379132_ideal_included_def",
  ``q2379132_ideal_included
      (smaller : 'a -> bool) (larger : 'a -> bool) <=>
      !x. smaller x ==> larger x``);

val q2379132_contraction_equal_def = new_definition (
  "q2379132_contraction_equal_def",
  ``q2379132_contraction_equal
      (f : 'r -> 's) (upstairs : 's -> bool)
      (downstairs : 'r -> bool) <=>
      !r. upstairs (f r) <=> downstairs r``);

val q2379132_contraction_included_in_ideal_def = new_definition (
  "q2379132_contraction_included_in_ideal_def",
  ``q2379132_contraction_included_in_ideal
      (f : 'r -> 's) (upstairs : 's -> bool)
      (downstairs : 'r -> bool) <=>
      !r. upstairs (f r) ==> downstairs r``);

val q2379132_ideal_below_contraction_def = new_definition (
  "q2379132_ideal_below_contraction_def",
  ``q2379132_ideal_below_contraction
      (f : 'r -> 's) (downstairs : 'r -> bool)
      (upstairs : 's -> bool) <=>
      !r. downstairs r ==> upstairs (f r)``);

val q2379132_has_going_down_def = new_definition (
  "q2379132_has_going_down_def",
  ``q2379132_has_going_down
      (Rzero : 'r) (Rone : 'r)
      (Radd : 'r -> 'r -> 'r) (Rmul : 'r -> 'r -> 'r)
      (Rneg : 'r -> 'r)
      (Szero : 's) (Sone : 's)
      (Sadd : 's -> 's -> 's) (Smul : 's -> 's -> 's)
      (Sneg : 's -> 's) (f : 'r -> 's) <=>
      !p q : 'r -> bool.
        q2379132_prime_ideal Rzero Rone Radd Rmul Rneg p /\
        q2379132_prime_ideal Rzero Rone Radd Rmul Rneg q /\
        q2379132_ideal_included p q
        ==>
        !Q : 's -> bool.
          q2379132_prime_ideal Szero Sone Sadd Smul Sneg Q /\
          q2379132_contraction_equal f Q q
          ==>
          ?P : 's -> bool.
            q2379132_prime_ideal Szero Sone Sadd Smul Sneg P /\
            q2379132_ideal_included P Q /\
            q2379132_contraction_equal f P p``);

val q2379132_generalizing_prime_spectrum_comap_def = new_definition (
  "q2379132_generalizing_prime_spectrum_comap_def",
  ``q2379132_generalizing_prime_spectrum_comap
      (Rzero : 'r) (Rone : 'r)
      (Radd : 'r -> 'r -> 'r) (Rmul : 'r -> 'r -> 'r)
      (Rneg : 'r -> 'r)
      (Szero : 's) (Sone : 's)
      (Sadd : 's -> 's -> 's) (Smul : 's -> 's -> 's)
      (Sneg : 's -> 's) (f : 'r -> 's) <=>
      !Q : 's -> bool.
        q2379132_prime_ideal Szero Sone Sadd Smul Sneg Q
        ==>
        !p : 'r -> bool.
          q2379132_prime_ideal Rzero Rone Radd Rmul Rneg p /\
          q2379132_ideal_below_contraction f p Q
          ==>
          ?P : 's -> bool.
            q2379132_prime_ideal Szero Sone Sadd Smul Sneg P /\
            q2379132_ideal_included P Q /\
            q2379132_contraction_equal f P p``);

val q2379132_local_prime_spectrum_comap_surjective_def = new_definition (
  "q2379132_local_prime_spectrum_comap_surjective_def",
  ``q2379132_local_prime_spectrum_comap_surjective
      (Rzero : 'r) (Rone : 'r)
      (Radd : 'r -> 'r -> 'r) (Rmul : 'r -> 'r -> 'r)
      (Rneg : 'r -> 'r)
      (Szero : 's) (Sone : 's)
      (Sadd : 's -> 's -> 's) (Smul : 's -> 's -> 's)
      (Sneg : 's -> 's) (f : 'r -> 's)
      (Q : 's -> bool) <=>
      !p : 'r -> bool.
        q2379132_prime_ideal Rzero Rone Radd Rmul Rneg p /\
        q2379132_ideal_below_contraction f p Q
        ==>
        ?P : 's -> bool.
          q2379132_prime_ideal Szero Sone Sadd Smul Sneg P /\
          q2379132_ideal_included P Q /\
          q2379132_contraction_equal f P p``);

val exists_ideal_over_prime_of_isIntegral_of_isDomain =
  ``!(Rzero : 'r) (Rone : 'r)
      (Radd : 'r -> 'r -> 'r) (Rmul : 'r -> 'r -> 'r)
      (Rneg : 'r -> 'r)
      (Szero : 's) (Sone : 's)
      (Sadd : 's -> 's -> 's) (Smul : 's -> 's -> 's)
      (Sneg : 's -> 's) (f : 'r -> 's) (P : 'r -> bool).
      q2379132_comm_ring Rzero Rone Radd Rmul Rneg /\
      q2379132_integral_domain Szero Sone Sadd Smul Sneg /\
      q2379132_ring_hom
        Rzero Rone Radd Rmul Szero Sone Sadd Smul f /\
      q2379132_integral_extension Rone Szero Sadd Smul f /\
      q2379132_prime_ideal Rzero Rone Radd Rmul Rneg P /\
      (!r. f r = Szero ==> P r)
      ==>
      ?Q : 's -> bool.
        q2379132_prime_ideal Szero Sone Sadd Smul Sneg Q /\
        q2379132_contraction_equal f Q P``;

val exists_ideal_over_prime_of_isIntegral_of_isPrime =
  ``!(Rzero : 'r) (Rone : 'r)
      (Radd : 'r -> 'r -> 'r) (Rmul : 'r -> 'r -> 'r)
      (Rneg : 'r -> 'r)
      (Szero : 's) (Sone : 's)
      (Sadd : 's -> 's -> 's) (Smul : 's -> 's -> 's)
      (Sneg : 's -> 's) (f : 'r -> 's)
      (P : 'r -> bool) (I : 's -> bool).
      q2379132_comm_ring Rzero Rone Radd Rmul Rneg /\
      q2379132_comm_ring Szero Sone Sadd Smul Sneg /\
      q2379132_ring_hom
        Rzero Rone Radd Rmul Szero Sone Sadd Smul f /\
      q2379132_integral_extension Rone Szero Sadd Smul f /\
      q2379132_prime_ideal Rzero Rone Radd Rmul Rneg P /\
      q2379132_prime_ideal Szero Sone Sadd Smul Sneg I /\
      q2379132_contraction_included_in_ideal f I P
      ==>
      ?Q : 's -> bool.
        q2379132_ideal_included I Q /\
        q2379132_prime_ideal Szero Sone Sadd Smul Sneg Q /\
        q2379132_contraction_equal f Q P``;

val has_going_down_iff_generalizing_prime_spectrum_comap =
  ``!(Rzero : 'r) (Rone : 'r)
      (Radd : 'r -> 'r -> 'r) (Rmul : 'r -> 'r -> 'r)
      (Rneg : 'r -> 'r)
      (Szero : 's) (Sone : 's)
      (Sadd : 's -> 's -> 's) (Smul : 's -> 's -> 's)
      (Sneg : 's -> 's) (f : 'r -> 's).
      q2379132_comm_ring Rzero Rone Radd Rmul Rneg /\
      q2379132_comm_ring Szero Sone Sadd Smul Sneg /\
      q2379132_ring_hom
        Rzero Rone Radd Rmul Szero Sone Sadd Smul f
      ==>
      (q2379132_has_going_down
         Rzero Rone Radd Rmul Rneg
         Szero Sone Sadd Smul Sneg f
       <=>
       q2379132_generalizing_prime_spectrum_comap
         Rzero Rone Radd Rmul Rneg
         Szero Sone Sadd Smul Sneg f)``;

val has_going_down_of_local_prime_spectrum_comap_surjective =
  ``!(Rzero : 'r) (Rone : 'r)
      (Radd : 'r -> 'r -> 'r) (Rmul : 'r -> 'r -> 'r)
      (Rneg : 'r -> 'r)
      (Szero : 's) (Sone : 's)
      (Sadd : 's -> 's -> 's) (Smul : 's -> 's -> 's)
      (Sneg : 's -> 's) (f : 'r -> 's).
      q2379132_comm_ring Rzero Rone Radd Rmul Rneg /\
      q2379132_comm_ring Szero Sone Sadd Smul Sneg /\
      q2379132_ring_hom
        Rzero Rone Radd Rmul Szero Sone Sadd Smul f /\
      (!Q : 's -> bool.
        q2379132_prime_ideal Szero Sone Sadd Smul Sneg Q
        ==>
        q2379132_local_prime_spectrum_comap_surjective
          Rzero Rone Radd Rmul Rneg
          Szero Sone Sadd Smul Sneg f Q)
      ==>
      q2379132_has_going_down
        Rzero Rone Radd Rmul Rneg
        Szero Sone Sadd Smul Sneg f``;
