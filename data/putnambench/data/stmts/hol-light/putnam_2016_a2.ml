(*
  Statement-only formalization of PutnamBench corpus artifact putnam_2016_a2:
  the limit of the largest positive natural number satisfying a binomial
  coefficient inequality, normalized by its index. This file contains no proof.
*)

let library_output = open_out "/dev/null";;
let library_formatter = Format.formatter_of_out_channel library_output;;
let binomial_loaded =
  Toploop.use_file library_formatter "Library/binomial.ml";;
let analysis_loaded =
  Toploop.use_file library_formatter "Library/analysis.ml";;
Format.pp_print_flush library_formatter ();;
close_out library_output;;
if not binomial_loaded then failwith "failed to load Library/binomial.ml";;
if not analysis_loaded then failwith "failed to load Library/analysis.ml";;

let statement =
  `let qualifies =
     \n m:num.
       0 < m /\ binom (m,n - 1) > binom (m - 1,n) in
   !M:num->num.
     (!n:num.
        0 < n
        ==> qualifies n (M n) /\
            (!m:num. qualifies n m ==> m <= M n))
     ==>
     (\n:num. &(M n) / &n)
     tends_num_real ((&3 + sqrt (&5)) / &2)`;;
