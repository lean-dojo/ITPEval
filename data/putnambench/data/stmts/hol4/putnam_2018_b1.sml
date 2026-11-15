(*
  Statement-only formalization of PutnamBench corpus artifact putnam_2018_b1:
  classification of the integer vectors whose removal from a rectangular
  lattice set leaves a partition into equal-sized parts with equal vector
  sums. This file contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory integerTheory pairTheory pred_setTheory;

val putnam_2018_b1 =
  ``let lattice =
      {w : int # int |
         0 <= FST w /\ FST w <= 2 /\
         0 <= SND w /\ SND w <= 100}
    in
      !v : int # int.
        (v IN lattice /\
         ?q r : (int # int) set.
           q UNION r = lattice DELETE v /\
           DISJOINT q r /\
           CARD q = CARD r /\
           ITSET (\w acc. FST w + acc) q 0 =
             ITSET (\w acc. FST w + acc) r 0 /\
           ITSET (\w acc. SND w + acc) q 0 =
             ITSET (\w acc. SND w + acc) r 0)
        <=>
        ?b : int.
          0 <= b /\ b <= 100 /\
          (?k : int. b = 2 * k) /\
          v = (1, b)``;
