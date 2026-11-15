(*
  Statement-only formalization of PutnamBench corpus artifact putnam_2015_b4:
  the sum of 2^a/(3^b 5^c) over positive integer side lengths of triangles
  is the reduced rational number 17/21. This file contains no proof.
*)

let analysis_output = open_out "/dev/null";;
let analysis_formatter = Format.formatter_of_out_channel analysis_output;;
let analysis_loaded =
  Toploop.use_file analysis_formatter "Library/analysis.ml";;
Format.pp_print_flush analysis_formatter ();;
close_out analysis_output;;
if not analysis_loaded then failwith "failed to load Library/analysis.ml";;

let statement =
  `let triangle_term =
     \a b c:num.
       if 0 < a /\ 0 < b /\ 0 < c /\
          a < b + c /\ b < c + a /\ c < a + b
       then (&2 pow a) / ((&3 pow b) * (&5 pow c))
       else &0 in
   coprime(17,21) /\
   (\N:num.
      sum (1..N)
        (\a:num.
           sum (1..N)
             (\b:num.
                sum (1..N)
                  (\c:num. triangle_term a b c))))
   tends_num_real (&17 / &21)`;;
