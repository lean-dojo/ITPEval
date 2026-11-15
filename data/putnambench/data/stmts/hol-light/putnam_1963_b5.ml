(*
  Statement-only formalization of PutnamBench artifact putnam_1963_b5:
  convergence of a real series with dyadic interval bounds implies that the
  integer-indexed sequence n times a(n) tends to zero. This file contains no proof.
*)

let analysis_output = open_out "/dev/null";;
let analysis_formatter = Format.formatter_of_out_channel analysis_output;;
let analysis_loaded =
  Toploop.use_file analysis_formatter "Library/analysis.ml";;
Format.pp_print_flush analysis_formatter ();;
close_out analysis_output;;
if not analysis_loaded then failwith "failed to load Library/analysis.ml";;

let statement =
  `!a:int->real.
     (!n:int.
        (&1:int) <= n
        ==> !k:int.
              n <= k /\ k <= (&2:int) * n
              ==> &0 <= a k /\ a k <= &100 * a n) /\
     summable (\m:num. a (&m))
     ==> !e:real.
           &0 < e
           ==> ?N:int.
                 !n:int.
                   N <= n
                   ==> abs (real_of_int n * a n) < e`;;
