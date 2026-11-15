(*
  Statement-only formalization of PutnamBench corpus artifact putnam_1998_b6:
  for every integer cubic with leading coefficient 1, some positive integer
  input gives a value that is not an integer square. This file contains no proof.
*)

open HolKernel Parse boolLib;
open integerTheory;

val putnam_1998_b6 =
  ``!a b c : int.
      ?n : int.
        0 < n /\
        ~(?k : int.
            n * n * n + a * n * n + b * n + c = k * k)``;
