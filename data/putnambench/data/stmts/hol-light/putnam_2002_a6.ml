(*
  Statement-only formalization of PutnamBench corpus artifact putnam_2002_a6:
  the recursively defined real series converges exactly for base 2 among
  integer bases at least 2. This file contains no proof.
*)

let analysis_output = open_out "/dev/null";;
let analysis_formatter = Format.formatter_of_out_channel analysis_output;;
let analysis_loaded =
  Toploop.use_file analysis_formatter "Library/analysis.ml";;
Format.pp_print_flush analysis_formatter ();;
close_out analysis_output;;
if not analysis_loaded then failwith "failed to load Library/analysis.ml";;

let statement =
  `let digitlength =
     \b n:num.
       if b < 2 then 0
       else @k:num.
              n < b EXP k /\
              !j:num. j < k ==> ~(n < b EXP j) in
   !f:num->num->real.
     (!b:num.
        f b 1 = &1 /\
        f b 2 = &2 /\
        (!n:num.
           3 <= n
           ==> f b n = &n * f b (digitlength b n)))
     ==>
     {b:num |
        2 <= b /\
        ?L:real.
          (\m:num. sum (1..m) (\n:num. &1 / f b n))
          tends_num_real L} =
     {b:num | b = 2}`;;
