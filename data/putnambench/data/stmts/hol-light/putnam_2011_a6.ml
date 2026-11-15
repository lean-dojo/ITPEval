(*
  Statement-only formalization of PutnamBench corpus artifact putnam_2011_a6:
  exponential convergence of the product distribution of a uniform die on a
  proper generating subset of a finite abelian group to the uniform
  distribution. This file contains no proof.
*)

let analysis_output = open_out "/dev/null";;
let analysis_formatter = Format.formatter_of_out_channel analysis_output;;
let analysis_loaded =
  Toploop.use_file analysis_formatter "Library/analysis.ml";;
Format.pp_print_flush analysis_formatter ();;
close_out analysis_output;;
if not analysis_loaded then failwith "failed to load Library/analysis.ml";;

let statement =
  `let is_commutative_group =
     \(gmul:A->A->A) (ginv:A->A) (gid:A).
       (!x y z:A.
          gmul x (gmul y z) = gmul (gmul x y) z) /\
       (!x:A. gmul gid x = x /\ gmul x gid = x) /\
       (!x:A.
          gmul (ginv x) x = gid /\ gmul x (ginv x) = gid) /\
       (!x y:A. gmul x y = gmul y x) in
   !gmul:A->A->A. !ginv:A->A. !gid:A.
   !n k:num. !gset:A->bool. !mgprob:num->A->real.
     is_commutative_group gmul ginv gid /\
     FINITE (UNIV:A->bool) /\
     n = CARD (UNIV:A->bool) /\
     FINITE gset /\
     CARD gset = k /\
     k < n /\
     gid IN gset /\
     (!x:A.
        ?l:A list.
          (!y:A. MEM y l ==> y IN gset) /\
          ITLIST gmul l gid = x) /\
     mgprob =
       (\m x.
          &(CARD {l:A list |
                    LENGTH l = m /\
                    (!y:A. MEM y l ==> y IN gset) /\
                    ITLIST gmul l gid = x}) /
          (&k) pow m)
     ==>
     ?b:real.
       &0 < b /\ b < &1 /\
       ?C:real.
         &0 < C /\
         (\m:num.
            (&1 / b pow (2 * m)) *
            sum (UNIV:A->bool)
              (\x:A. (mgprob m x - &1 / &n) pow 2))
         tends_num_real C`;;
