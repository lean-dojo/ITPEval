(*
  Statement-only formalization of miniF2F test problem imo_1985_p6: a
  recursively defined real-valued sequence family has a unique nonnegative
  parameter whose positive-index terms are positive, strictly increasing, and
  bounded above by 1. This file contains no proof.
*)

let statement =
  `!f:num->real->real.
     (!x. &0 <= x ==> f 1 x = x) /\
     (!x n. &0 <= x
            ==> f (n + 1) x =
                f n x * (f n x + &1 / &n))
     ==> ?!a. &0 <= a /\
               (!n. 0 < n
                    ==> &0 < f n a /\
                        f n a < f (n + 1) a /\
                        f (n + 1) a < &1)`;;
