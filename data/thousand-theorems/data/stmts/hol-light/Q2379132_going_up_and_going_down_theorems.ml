(*
  Statement-only formalization of Thousand Theorems corpus artifact Q2379132,
  "Going-up and going-down theorems". It states the two indexed going-up
  results, the prime-spectrum characterization of going-down, and the
  localized-spectrum surjectivity criterion. This file contains no proof.
*)

let Q2379132_GOING_UP =
  `let is_commring_R =
     \(zeroR:R) (oneR:R) (addR:R->R->R) (mulR:R->R->R)
      (negR:R->R).
       (!x. addR zeroR x = x) /\
       (!x. addR (negR x) x = zeroR) /\
       (!x y. addR x y = addR y x) /\
       (!x y z. addR x (addR y z) = addR (addR x y) z) /\
       (!x. mulR oneR x = x) /\
       (!x y. mulR x y = mulR y x) /\
       (!x y z. mulR x (mulR y z) = mulR (mulR x y) z) /\
       (!x y z. mulR x (addR y z) =
                addR (mulR x y) (mulR x z)) in
   let is_commring_S =
     \(zeroS:S) (oneS:S) (addS:S->S->S) (mulS:S->S->S)
      (negS:S->S).
       (!x. addS zeroS x = x) /\
       (!x. addS (negS x) x = zeroS) /\
       (!x y. addS x y = addS y x) /\
       (!x y z. addS x (addS y z) = addS (addS x y) z) /\
       (!x. mulS oneS x = x) /\
       (!x y. mulS x y = mulS y x) /\
       (!x y z. mulS x (mulS y z) = mulS (mulS x y) z) /\
       (!x y z. mulS x (addS y z) =
                addS (mulS x y) (mulS x z)) in
   let is_domain_S =
     \(zeroS:S) (oneS:S) (mulS:S->S->S).
       ~(zeroS = oneS) /\
       (!x y. mulS x y = zeroS ==> x = zeroS \/ y = zeroS) in
   let is_ring_hom =
     \(zeroR:R) (oneR:R) (addR:R->R->R) (mulR:R->R->R)
      (zeroS:S) (oneS:S) (addS:S->S->S) (mulS:S->S->S)
      (f:R->S).
       f zeroR = zeroS /\
       f oneR = oneS /\
       (!x y. f (addR x y) = addS (f x) (f y)) /\
       (!x y. f (mulR x y) = mulS (f x) (f y)) in
   let is_ideal_R =
     \(zeroR:R) (addR:R->R->R) (mulR:R->R->R)
      (negR:R->R) (P:R->bool).
       P zeroR /\
       (!x. P x ==> P (negR x)) /\
       (!x y. P x /\ P y ==> P (addR x y)) /\
       (!a x. P x ==> P (mulR a x)) in
   let is_ideal_S =
     \(zeroS:S) (addS:S->S->S) (mulS:S->S->S)
      (negS:S->S) (Q:S->bool).
       Q zeroS /\
       (!x. Q x ==> Q (negS x)) /\
       (!x y. Q x /\ Q y ==> Q (addS x y)) /\
       (!a x. Q x ==> Q (mulS a x)) in
   let is_prime_R =
     \(zeroR:R) (oneR:R) (addR:R->R->R) (mulR:R->R->R)
      (negR:R->R) (P:R->bool).
       is_ideal_R zeroR addR mulR negR P /\
       ~(P oneR) /\
       (!x y. P (mulR x y) ==> P x \/ P y) in
   let is_prime_S =
     \(zeroS:S) (oneS:S) (addS:S->S->S) (mulS:S->S->S)
      (negS:S->S) (Q:S->bool).
       is_ideal_S zeroS addS mulS negS Q /\
       ~(Q oneS) /\
       (!x y. Q (mulS x y) ==> Q x \/ Q y) in
   let power_S =
     \(oneS:S) (mulS:S->S->S) (x:S) (n:num).
       ITLIST mulS (REPLICATE n x) oneS in
   let polynomial_eval =
     \(zeroR:R) (addS:S->S->S) (mulS:S->S->S)
      (oneS:S) (f:R->S) (p:num->R) (x:S).
       iterate addS {n | ~(p n = zeroR)}
         (\n. mulS (f (p n)) (power_S oneS mulS x n)) in
   let is_integral =
     \(zeroR:R) (oneR:R) (zeroS:S) (oneS:S)
      (addS:S->S->S) (mulS:S->S->S) (f:R->S).
       !x:S.
         ?p:num->R.
           FINITE {n | ~(p n = zeroR)} /\
           (?d:num.
              p d = oneR /\
              (!n:num. d < n ==> p n = zeroR)) /\
           polynomial_eval zeroR addS mulS oneS f p x = zeroS in
   !zeroR oneR:R. !addR mulR:R->R->R. !negR:R->R.
   !zeroS oneS:S. !addS mulS:S->S->S. !negS:S->S.
   !f:R->S. !P:R->bool.
     is_commring_R zeroR oneR addR mulR negR /\
     is_commring_S zeroS oneS addS mulS negS /\
     is_domain_S zeroS oneS mulS /\
     is_ring_hom zeroR oneR addR mulR
       zeroS oneS addS mulS f /\
     is_integral zeroR oneR zeroS oneS addS mulS f /\
     is_prime_R zeroR oneR addR mulR negR P /\
     (!x:R. f x = zeroS ==> P x)
     ==>
     ?Q:S->bool.
       is_prime_S zeroS oneS addS mulS negS Q /\
       (!x:R. Q (f x) <=> P x)`;;

let q2379132_commring = new_definition
 `q2379132_commring
    (zero:A) (oneA:A) (add:A->A->A) (mul:A->A->A) (neg:A->A) <=>
    (!x:A. add zero x = x) /\
    (!x:A. add (neg x) x = zero) /\
    (!x y:A. add x y = add y x) /\
    (!x y z:A. add x (add y z) = add (add x y) z) /\
    (!x:A. mul oneA x = x) /\
    (!x y:A. mul x y = mul y x) /\
    (!x y z:A. mul x (mul y z) = mul (mul x y) z) /\
    (!x y z:A. mul x (add y z) = add (mul x y) (mul x z))`;;

let q2379132_ring_hom = new_definition
 `q2379132_ring_hom
    (zeroR:R) (oneR:R) (addR:R->R->R) (mulR:R->R->R)
    (zeroS:S) (oneS:S) (addS:S->S->S) (mulS:S->S->S)
    (f:R->S) <=>
    f zeroR = zeroS /\
    f oneR = oneS /\
    (!x y:R. f (addR x y) = addS (f x) (f y)) /\
    (!x y:R. f (mulR x y) = mulS (f x) (f y))`;;

let q2379132_ideal = new_definition
 `q2379132_ideal
    (zero:A) (add:A->A->A) (mul:A->A->A) (neg:A->A)
    (ideal:A->bool) <=>
    ideal zero /\
    (!x:A. ideal x ==> ideal (neg x)) /\
    (!x y:A. ideal x /\ ideal y ==> ideal (add x y)) /\
    (!a x:A. ideal x ==> ideal (mul a x))`;;

let q2379132_prime_ideal = new_definition
 `q2379132_prime_ideal
    (zero:A) (oneA:A) (add:A->A->A) (mul:A->A->A) (neg:A->A)
    (ideal:A->bool) <=>
    q2379132_ideal zero add mul neg ideal /\
    ~(ideal oneA) /\
    (!x y:A. ideal (mul x y) ==> ideal x \/ ideal y)`;;

let q2379132_polynomial_eval = new_definition
 `q2379132_polynomial_eval
    (zeroS:S) (addS:S->S->S) (mulS:S->S->S)
    (f:R->S) (coefficients:R list) (x:S) =
    ITLIST (\c acc. addS (f c) (mulS x acc)) coefficients zeroS`;;

let q2379132_integral_extension = new_definition
 `q2379132_integral_extension
    (oneR:R) (zeroS:S) (addS:S->S->S) (mulS:S->S->S)
    (f:R->S) <=>
    !x:S.
      ?coefficients:R list.
        ~(coefficients = []) /\
        LAST coefficients = oneR /\
        q2379132_polynomial_eval
          zeroS addS mulS f coefficients x = zeroS`;;

let q2379132_ideal_included = new_definition
 `q2379132_ideal_included (smaller:A->bool) (larger:A->bool) <=>
    !x:A. smaller x ==> larger x`;;

let q2379132_contraction_equal = new_definition
 `q2379132_contraction_equal
    (f:R->S) (upstairs:S->bool) (downstairs:R->bool) <=>
    !x:R. upstairs (f x) <=> downstairs x`;;

let q2379132_contraction_included_in_ideal = new_definition
 `q2379132_contraction_included_in_ideal
    (f:R->S) (upstairs:S->bool) (downstairs:R->bool) <=>
    !x:R. upstairs (f x) ==> downstairs x`;;

let q2379132_ideal_below_contraction = new_definition
 `q2379132_ideal_below_contraction
    (f:R->S) (downstairs:R->bool) (upstairs:S->bool) <=>
    !x:R. downstairs x ==> upstairs (f x)`;;

let q2379132_has_going_down = new_definition
 `q2379132_has_going_down
    (zeroR:R) (oneR:R) (addR:R->R->R) (mulR:R->R->R) (negR:R->R)
    (zeroS:S) (oneS:S) (addS:S->S->S) (mulS:S->S->S) (negS:S->S)
    (f:R->S) <=>
    !p q:R->bool.
      q2379132_prime_ideal zeroR oneR addR mulR negR p /\
      q2379132_prime_ideal zeroR oneR addR mulR negR q /\
      q2379132_ideal_included p q
      ==>
      !Q:S->bool.
        q2379132_prime_ideal zeroS oneS addS mulS negS Q /\
        q2379132_contraction_equal f Q q
        ==>
        ?P:S->bool.
          q2379132_prime_ideal zeroS oneS addS mulS negS P /\
          q2379132_ideal_included P Q /\
          q2379132_contraction_equal f P p`;;

let q2379132_generalizing_prime_spectrum_comap = new_definition
 `q2379132_generalizing_prime_spectrum_comap
    (zeroR:R) (oneR:R) (addR:R->R->R) (mulR:R->R->R) (negR:R->R)
    (zeroS:S) (oneS:S) (addS:S->S->S) (mulS:S->S->S) (negS:S->S)
    (f:R->S) <=>
    !Q:S->bool.
      q2379132_prime_ideal zeroS oneS addS mulS negS Q
      ==>
      !p:R->bool.
        q2379132_prime_ideal zeroR oneR addR mulR negR p /\
        q2379132_ideal_below_contraction f p Q
        ==>
        ?P:S->bool.
          q2379132_prime_ideal zeroS oneS addS mulS negS P /\
          q2379132_ideal_included P Q /\
          q2379132_contraction_equal f P p`;;

let q2379132_local_prime_spectrum_comap_surjective = new_definition
 `q2379132_local_prime_spectrum_comap_surjective
    (zeroR:R) (oneR:R) (addR:R->R->R) (mulR:R->R->R) (negR:R->R)
    (zeroS:S) (oneS:S) (addS:S->S->S) (mulS:S->S->S) (negS:S->S)
    (f:R->S) (Q:S->bool) <=>
    !p:R->bool.
      q2379132_prime_ideal zeroR oneR addR mulR negR p /\
      q2379132_ideal_below_contraction f p Q
      ==>
      ?P:S->bool.
        q2379132_prime_ideal zeroS oneS addS mulS negS P /\
        q2379132_ideal_included P Q /\
        q2379132_contraction_equal f P p`;;

let Q2379132_GENERAL_GOING_UP =
 `!zeroR oneR:R. !addR mulR:R->R->R. !negR:R->R.
  !zeroS oneS:S. !addS mulS:S->S->S. !negS:S->S.
  !f:R->S. !P:R->bool. !upstairsIdeal:S->bool.
    q2379132_commring zeroR oneR addR mulR negR /\
    q2379132_commring zeroS oneS addS mulS negS /\
    q2379132_ring_hom
      zeroR oneR addR mulR zeroS oneS addS mulS f /\
    q2379132_integral_extension oneR zeroS addS mulS f /\
    q2379132_prime_ideal zeroR oneR addR mulR negR P /\
    q2379132_prime_ideal
      zeroS oneS addS mulS negS upstairsIdeal /\
    q2379132_contraction_included_in_ideal f upstairsIdeal P
    ==>
    ?Q:S->bool.
      q2379132_ideal_included upstairsIdeal Q /\
      q2379132_prime_ideal zeroS oneS addS mulS negS Q /\
      q2379132_contraction_equal f Q P`;;

let Q2379132_GOING_DOWN_IFF_GENERALIZING =
 `!zeroR oneR:R. !addR mulR:R->R->R. !negR:R->R.
  !zeroS oneS:S. !addS mulS:S->S->S. !negS:S->S.
  !f:R->S.
    q2379132_commring zeroR oneR addR mulR negR /\
    q2379132_commring zeroS oneS addS mulS negS /\
    q2379132_ring_hom
      zeroR oneR addR mulR zeroS oneS addS mulS f
    ==>
    (q2379132_has_going_down
       zeroR oneR addR mulR negR zeroS oneS addS mulS negS f
     <=>
     q2379132_generalizing_prime_spectrum_comap
       zeroR oneR addR mulR negR zeroS oneS addS mulS negS f)`;;

let Q2379132_GOING_DOWN_FROM_LOCAL_SURJECTIVITY =
 `!zeroR oneR:R. !addR mulR:R->R->R. !negR:R->R.
  !zeroS oneS:S. !addS mulS:S->S->S. !negS:S->S.
  !f:R->S.
    q2379132_commring zeroR oneR addR mulR negR /\
    q2379132_commring zeroS oneS addS mulS negS /\
    q2379132_ring_hom
      zeroR oneR addR mulR zeroS oneS addS mulS f /\
    (!Q:S->bool.
      q2379132_prime_ideal zeroS oneS addS mulS negS Q
      ==>
      q2379132_local_prime_spectrum_comap_surjective
        zeroR oneR addR mulR negR
        zeroS oneS addS mulS negS f Q)
    ==>
    q2379132_has_going_down
      zeroR oneR addR mulR negR zeroS oneS addS mulS negS f`;;
