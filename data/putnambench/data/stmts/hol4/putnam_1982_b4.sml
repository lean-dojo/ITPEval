(*
  Statement-only formalization of PutnamBench corpus artifact putnam_1982_b4:
  truth of both claims about finite nonempty sets of distinct integers whose
  product divides the product of every integer translate. This file contains
  no proof.
*)

open HolKernel Parse boolLib;
open integerTheory pred_setTheory;

val putnam_1982_b4 =
  ``let int_product =
      \s : int set.
      \f : int -> int.
        ITSET (\i acc. f i * acc) s (1 : int)
    in
    let admissible =
      \n : int set.
        FINITE n /\
        n <> {} /\
        (!k : int.
           int_product n (\i : int. i) int_divides
           int_product n (\i : int. i + k))
    in
    let putnam_1982_b4_solution = (T, T)
    in
      (((!n : int set.
           admissible n
           ==>
           1 IN n \/ -1 IN n)
        <=>
        FST putnam_1982_b4_solution) /\
       ((!n : int set.
           admissible n /\
           (!i : int. i IN n ==> 0 < i)
           ==>
           n = {i : int | 1 <= i /\ i <= &(CARD n)})
        <=>
        SND putnam_1982_b4_solution))``;
