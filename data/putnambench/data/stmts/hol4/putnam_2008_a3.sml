(*
  Statement-only formalization of PutnamBench corpus artifact putnam_2008_a3:
  termination and choice-independence of the final positive-integer sequence
  under admissible pairwise gcd/lcm replacements. This file contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory dividesTheory gcdTheory;

val putnam_2008_a3 =
  ``!n : num.
    !a : num -> num.
    !cont : (num -> num) -> bool.
    !init : (num -> num -> num) -> bool.
    !trans : (num -> num -> num) -> bool.
      0 < n /\
      (!i : num. i < n ==> 0 < a i) /\
      (!s : num -> num.
        cont s <=>
        ?j k : num.
          j < n /\ k < n /\ j < k /\ ~divides (s j) (s k)) /\
      (!P : num -> num -> num.
        init P <=> !i : num. i < n ==> P 0 i = a i) /\
      (!P : num -> num -> num.
        trans P <=>
        !t : num.
          cont (P t)
          ==>
          ?j k : num.
            j < n /\
            k < n /\
            j < k /\
            ~divides (P t j) (P t k) /\
            P (t + 1) j = gcd (P t j) (P t k) /\
            P (t + 1) k = lcm (P t j) (P t k) /\
            !i : num.
              i < n /\ i <> j /\ i <> k
              ==>
              P (t + 1) i = P t i)
      ==>
      ?f : num -> num.
        !P : num -> num -> num.
          init P /\ trans P
          ==>
          ?t : num.
            ~cont (P t) /\
            !i : num. i < n ==> P t i = f i``;
