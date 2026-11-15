(*
  Statement-only formalization of PutnamBench corpus artifact putnam_2012_b1:
  closure under pointwise multiplication for a class of functions from the
  nonnegative reals to themselves containing exp(x) - 1 and ln(x + 1), and
  closed under sum, composition, and nonnegative difference. This file
  contains no proof.
*)

open HolKernel Parse boolLib;
open pairTheory realTheory transcTheory;

val putnam_2012_b1 =
  ``!S : ((real # real) -> bool) -> bool.
      let nnfun =
        \r : (real # real) -> bool.
          (!x y : real.
             r (x, y) ==> 0 <= x /\ 0 <= y) /\
          (!x : real.
             0 <= x
             ==>
             ?y : real.
               r (x, y) /\
               !z : real. r (x, z) ==> z = y)
      in
      let f1 =
        \p : real # real.
          0 <= FST p /\ SND p = exp (FST p) - 1
      in
      let f2 =
        \p : real # real.
          0 <= FST p /\ SND p = ln (FST p + 1)
      in
      let sum_graph =
        \r : (real # real) -> bool.
        \s : (real # real) -> bool.
        \p : real # real.
          ?a b : real.
            r (FST p, a) /\
            s (FST p, b) /\
            SND p = a + b
      in
      let compose_graph =
        \r : (real # real) -> bool.
        \s : (real # real) -> bool.
        \p : real # real.
          ?a : real.
            s (FST p, a) /\
            r (a, SND p)
      in
      let difference_admissible =
        \r : (real # real) -> bool.
        \s : (real # real) -> bool.
          !x a b : real.
            r (x, a) /\ s (x, b) ==> b <= a
      in
      let difference_graph =
        \r : (real # real) -> bool.
        \s : (real # real) -> bool.
        \p : real # real.
          ?a b : real.
            r (FST p, a) /\
            s (FST p, b) /\
            SND p = a - b
      in
      let product_graph =
        \r : (real # real) -> bool.
        \s : (real # real) -> bool.
        \p : real # real.
          ?a b : real.
            r (FST p, a) /\
            s (FST p, b) /\
            SND p = a * b
      in
        ((!r : (real # real) -> bool. S r ==> nnfun r) /\
         S f1 /\
         S f2 /\
         (!r s : (real # real) -> bool.
            S r /\ S s ==> S (sum_graph r s)) /\
         (!r s : (real # real) -> bool.
            S r /\ S s ==> S (compose_graph r s)) /\
         (!r s : (real # real) -> bool.
            S r /\
            S s /\
            difference_admissible r s
            ==>
            S (difference_graph r s)))
        ==>
        !r s : (real # real) -> bool.
          S r /\ S s ==> S (product_graph r s)``;
