(*
  Statement-only formalization of PutnamBench corpus artifact putnam_2000_b1:
  an integer linear combination of triples with an odd coordinate is odd on
  at least four sevenths of the finite index set. This file contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory integerTheory pred_setTheory;

val putnam_2000_b1 =
  ``!N : num. !a b c : num -> int.
      1 <= N /\
      (!j : num.
         j < N ==>
         (?k : int. a j = 2 * k + 1) \/
         (?k : int. b j = 2 * k + 1) \/
         (?k : int. c j = 2 * k + 1))
      ==>
      ?r s t : int.
        4 * N <=
        7 *
        CARD
          {j : num |
             j < N /\
             ?k : int.
               r * a j + s * b j + t * c j = 2 * k + 1}``;
