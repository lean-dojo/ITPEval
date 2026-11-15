(*
  Statement-only formalization of PutnamBench corpus artifact putnam_1997_a6:
  the values of a recursively defined real sequence at the largest parameter
  making its (n + 1)-st term zero. This file contains no proof.
*)

let binomial_output = open_out "/dev/null";;
let binomial_formatter = Format.formatter_of_out_channel binomial_output;;
let binomial_loaded =
  Toploop.use_file binomial_formatter "Library/binomial.ml";;
Format.pp_print_flush binomial_formatter ();;
close_out binomial_output;;
if not binomial_loaded then failwith "failed to load Library/binomial.ml";;

let statement =
  `!n:num maxc:real x:real->num->real.
     0 < n /\
     (!c:real. x c 0 = &0) /\
     (!c:real. x c 1 = &1) /\
     (!c:real. !k:num.
        x c (k + 2) =
        (c * x c (k + 1) - &(n - k) * x c k) / &(k + 1)) /\
     x maxc (n + 1) = &0 /\
     (!c:real. x c (n + 1) = &0 ==> c <= maxc)
     ==>
     !k:num.
       1 <= k /\ k <= n
       ==> x maxc k = &(binom (n - 1,k - 1))`;;
