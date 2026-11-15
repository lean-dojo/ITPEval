(*
  Statement-only formalization of PutnamBench corpus artifact putnam_2003_a5:
  a bijection between Dyck n-paths with no even-length return and Dyck
  (n-1)-paths. This file contains no proof.
*)

let statement =
  `let dyckpath =
     \m:num. \p:int list.
       LENGTH p = 2 * m /\
       (!k:num.
          k < LENGTH p
          ==> EL k p = &1 \/ EL k p = -- &1) /\
       isum {k:num | k < LENGTH p} (\k. EL k p) = &0 /\
       (!j:num.
          j < LENGTH p
          ==> &0 <= isum {k:num | k <= j} (\k. EL k p)) in
   let noevenreturn =
     \m:num. \p:int list.
       LENGTH p = 2 * m /\
       ~(?i j:num.
           i < j /\
           j < LENGTH p /\
           EL i p = &1 /\
           (!k:num.
              i < k /\ k <= j
              ==> EL k p = -- &1) /\
           EVEN (j - i) /\
           isum {k:num | k <= j} (\k. EL k p) = &0) in
   !n:num.
     0 < n
     ==> ?f:int list->int list.
           (!x:int list.
              LENGTH x = 2 * n
              ==> LENGTH (f x) = 2 * (n - 1)) /\
           (!y:int list.
              dyckpath (n - 1) y
              ==> ?!x:int list.
                    dyckpath n x /\
                    noevenreturn n x /\
                    f x = y)`;;
