(*
  Statement-only formalization of PutnamBench corpus artifact putnam_1989_a6:
  a binary-zero-block formal power series over a field of two elements
  satisfies a cubic equation. This file contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory listTheory numposrepTheory pred_setTheory;
open groupTheory ringTheory;

val putnam_1989_a6 =
  ``!(r : 'a ring) (alpha : num -> 'a).
      let series_zero =
        \n : num. r.sum.id
      in
      let series_one =
        \n : num. if n = 0 then r.prod.id else r.sum.id
      in
      let series_X =
        \n : num. if n = 1 then r.prod.id else r.sum.id
      in
      let series_add =
        \f g : num -> 'a. \n : num. r.sum.op (f n) (g n)
      in
      let series_mul =
        \f g : num -> 'a. \n : num.
          ITSET
            (\i acc.
               r.sum.op (r.prod.op (f i) (g (n - i))) acc)
            (count (SUC n))
            r.sum.id
      in
      let coefficient =
        \n : num.
          let digits =
            if n = 0 then [] else REVERSE (num_to_bin_list n)
          in
          let bin = [1] ++ digits ++ [1]
          in
            if
              !i j : num.
                i < LENGTH bin /\
                j < LENGTH bin /\
                i < j /\
                EL i bin = 1 /\
                EL j bin = 1 /\
                (!k : num.
                   i < k /\ k < j ==> EL k bin = 0)
                ==>
                EVEN (j - i - 1)
            then r.prod.id
            else r.sum.id
      in
        Ring r /\
        Group (r.prod excluding r.sum.id) /\
        FINITE r.carrier /\
        CARD r.carrier = 2 /\
        (!n : num. alpha n = coefficient n)
        ==>
        series_add
          (series_add
             (series_mul (series_mul alpha alpha) alpha)
             (series_mul series_X alpha))
          series_one =
        series_zero``;
