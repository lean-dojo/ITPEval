(*
  Statement-only formalization of miniF2F valid problem aime_1996_p5: distinct roots of one
  complex cubic determine the constant term of a second cubic whose roots are their pairwise
  sums. This file contains no proof.
*)

open HolKernel Parse boolLib;
open complexTheory;

val aime_1996_p5 =
  ``!a b c r s t : complex. !f g : complex -> complex.
      (!x : complex. f x = x pow 3 + 3 * x pow 2 + 4 * x - 11) /\
      (!x : complex. g x = x pow 3 + r * x pow 2 + s * x + t) /\
      f a = 0 /\
      f b = 0 /\
      f c = 0 /\
      g (a + b) = 0 /\
      g (b + c) = 0 /\
      g (c + a) = 0 /\
      a <> b /\
      b <> c /\
      c <> a
      ==>
      t = 23``;
