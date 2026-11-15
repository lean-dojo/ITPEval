(*
  Statement-only formalization of PutnamBench corpus artifact putnam_2003_a5:
  a one-to-one correspondence between Dyck n-paths with no even-length return
  and Dyck (n - 1)-paths. This file contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory integerTheory pred_setTheory;

val putnam_2003_a5 =
  ``let path_sum =
      \p : num -> int. \r : num.
        ITSET
          (\k : num. \acc : int. p k + acc)
          (count r)
          (0 : int)
    in
    let dyckpath =
      \m : num. \p : num -> int.
        (!k : num. 2 * m <= k ==> p k = 0) /\
        (!k : num. k < 2 * m ==> p k = 1 \/ p k = ~1) /\
        path_sum p (2 * m) = 0 /\
        (!j : num. j < 2 * m ==> 0 <= path_sum p (SUC j))
    in
    let noevenreturn =
      \m : num. \p : num -> int.
        ~(?i j : num.
            i < j /\
            j < 2 * m /\
            p i = 1 /\
            (!k : num. i < k /\ k <= j ==> p k = ~1) /\
            EVEN (j - i) /\
            path_sum p (SUC j) = 0)
    in
      !n : num.
        0 < n
        ==>
        ?f : (num -> int) -> (num -> int).
          !y : num -> int.
            dyckpath (n - 1) y
            ==>
            ?!x : num -> int.
              dyckpath n x /\
              noevenreturn n x /\
              f x = y``;
