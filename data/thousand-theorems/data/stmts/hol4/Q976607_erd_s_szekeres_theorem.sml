(*
  Statement-only formalization of the Thousand Theorems corpus artifact
  Q976607, "Erdős–Szekeres theorem": if the finite linearly ordered domain of
  an injective map into a linearly ordered type has cardinality greater than
  r*s, there is a strictly increasing finite subset of cardinality greater
  than r or a strictly decreasing one of cardinality greater than s. This
  file contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory pred_setTheory;

val erdos_szekeres =
  ``let is_linear_order_a =
      \(le : 'a -> 'a -> bool).
        (!x. le x x) /\
        (!x y. le x y /\ le y x ==> x = y) /\
        (!x y z. le x y /\ le y z ==> le x z) /\
        (!x y. le x y \/ le y x)
    in
    let is_linear_order_b =
      \(le : 'b -> 'b -> bool).
        (!x. le x x) /\
        (!x y. le x y /\ le y x ==> x = y) /\
        (!x y z. le x y /\ le y z ==> le x z) /\
        (!x y. le x y \/ le y x)
    in
    let strict_mono_on =
      \(leA : 'a -> 'a -> bool) (leB : 'b -> 'b -> bool)
       (f : 'a -> 'b) (t : 'a set).
        !x y.
          x IN t /\ y IN t /\ leA x y /\ x <> y
          ==>
          leB (f x) (f y) /\ f x <> f y
    in
    let strict_anti_on =
      \(leA : 'a -> 'a -> bool) (leB : 'b -> 'b -> bool)
       (f : 'a -> 'b) (t : 'a set).
        !x y.
          x IN t /\ y IN t /\ leA x y /\ x <> y
          ==>
          leB (f y) (f x) /\ f x <> f y
    in
      !(leA : 'a -> 'a -> bool) (leB : 'b -> 'b -> bool)
        (r : num) (s : num) (f : 'a -> 'b).
        is_linear_order_a leA /\
        is_linear_order_b leB /\
        FINITE (UNIV : 'a set) /\
        INJ f UNIV UNIV /\
        r * s < CARD (UNIV : 'a set)
        ==>
        (?t : 'a set.
           FINITE t /\
           r < CARD t /\
           strict_mono_on leA leB f t) \/
        (?t : 'a set.
           FINITE t /\
           s < CARD t /\
           strict_anti_on leA leB f t)``;
