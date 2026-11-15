(*
  Statement-only formalization of PutnamBench corpus artifact putnam_1986_b2:
  the complex difference triples arising from the given cyclic system are
  exactly four specified triples. This file contains no proof.
*)

open HolKernel Parse boolLib;
open complexTheory;

val putnam_1986_b2 =
  ``!T : (complex # complex) # complex.
      (T = ((0, 0), 0) \/
       T = ((0, ~1), 1) \/
       T = ((1, 0), ~1) \/
       T = ((~1, 1), 0))
      <=>
      ?x y z : complex.
        T = ((x - y, y - z), z - x) /\
        x * (x - 1) + 2 * y * z =
          y * (y - 1) + 2 * z * x /\
        y * (y - 1) + 2 * z * x =
          z * (z - 1) + 2 * x * y``;
