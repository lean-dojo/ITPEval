(*
  Statement-only formalization of miniF2F valid problem amc12a_2009_p15: the complex finite
  sum from k = 1 through n of k times i^k determines the positive natural number n as 97. This
  file contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory pred_setTheory realTheory complexTheory;

val _ = new_theory "hello";

val amc12a_2009_p15 =
  ``!n : num.
      0 < n /\
      ITSET
        (\k acc. complex_of_real (&k) * i pow k + acc)
        (IMAGE SUC (count n))
        0 = 48 + 49 * i
      ==>
      n = 97``;

val _ = export_theory();
