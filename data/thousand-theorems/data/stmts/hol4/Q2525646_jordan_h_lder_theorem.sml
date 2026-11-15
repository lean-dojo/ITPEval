(*
  Statement-only formalization of the Thousand Theorems corpus artifact
  Q2525646, "Jordan–Hölder theorem": finite composition series with common
  endpoints in a Jordan–Hölder lattice have isomorphic factors up to a
  bijection of their step indices. This file contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory;

val q2525646_jordan_holder_lattice_def = new_definition (
  "q2525646_jordan_holder_lattice_def",
  ``q2525646_jordan_holder_lattice
      (leq : 'a -> 'a -> bool)
      (meet : 'a -> 'a -> 'a) (join : 'a -> 'a -> 'a)
      (is_maximal : 'a -> 'a -> bool)
      (iso : ('a # 'a) -> ('a # 'a) -> bool) <=>
      (!x. leq x x) /\
      (!x y z. leq x y /\ leq y z ==> leq x z) /\
      (!x y. leq x y /\ leq y x ==> x = y) /\
      (!x y. leq (meet x y) x /\ leq (meet x y) y) /\
      (!x y z. leq z x /\ leq z y ==> leq z (meet x y)) /\
      (!x y. leq x (join x y) /\ leq y (join x y)) /\
      (!x y z. leq x z /\ leq y z ==> leq (join x y) z) /\
      (!x y. is_maximal x y ==> leq x y /\ x <> y) /\
      (!x y z.
         is_maximal x z /\ is_maximal y z /\ x <> y ==>
         join x y = z) /\
      (!x y.
         is_maximal x (join x y) /\ is_maximal y (join x y) ==>
         is_maximal (meet x y) x) /\
      (!p q. iso p q ==> iso q p) /\
      (!p q r. iso p q /\ iso q r ==> iso p r) /\
      (!x y.
         is_maximal x (join x y) ==>
         iso (x, join x y) (meet x y, y))``);

val q2525646_composition_series_def = new_definition (
  "q2525646_composition_series_def",
  ``q2525646_composition_series
      (is_maximal : 'a -> 'a -> bool) (n : num) (s : num -> 'a) <=>
      !i. i < n ==> is_maximal (s i) (s (SUC i))``);

val q2525646_equivalent_def = new_definition (
  "q2525646_equivalent_def",
  ``q2525646_equivalent
      (iso : ('a # 'a) -> ('a # 'a) -> bool)
      (n1 : num) (s1 : num -> 'a) (n2 : num) (s2 : num -> 'a) <=>
      ?e : num -> num.
        (!i. i < n1 ==> e i < n2) /\
        (!i j. i < n1 /\ j < n1 /\ e i = e j ==> i = j) /\
        (!j. j < n2 ==> ?i. i < n1 /\ e i = j) /\
        (!i.
           i < n1 ==>
           iso (s1 i, s1 (SUC i))
             (s2 (e i), s2 (SUC (e i))))``);

val CompositionSeries_jordan_holder =
  ``!(leq : 'a -> 'a -> bool)
      (meet : 'a -> 'a -> 'a) (join : 'a -> 'a -> 'a)
      (is_maximal : 'a -> 'a -> bool)
      (iso : ('a # 'a) -> ('a # 'a) -> bool)
      (n1 : num) (s1 : num -> 'a) (n2 : num) (s2 : num -> 'a).
      q2525646_jordan_holder_lattice leq meet join is_maximal iso /\
      q2525646_composition_series is_maximal n1 s1 /\
      q2525646_composition_series is_maximal n2 s2 /\
      s1 0 = s2 0 /\
      s1 n1 = s2 n2
      ==>
      q2525646_equivalent iso n1 s1 n2 s2``;
