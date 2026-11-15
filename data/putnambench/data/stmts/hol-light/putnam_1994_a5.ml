(*
  Statement-only formalization of PutnamBench corpus artifact putnam_1994_a5:
  sums of 1994 terms at strictly increasing indices from a positive real
  sequence tending to zero leave a nonempty gap in every nonempty interval.
  This file contains no proof.
*)

let analysis_output = open_out "/dev/null";;
let analysis_formatter = Format.formatter_of_out_channel analysis_output;;
let analysis_loaded =
  Toploop.use_file analysis_formatter "Library/analysis.ml";;
Format.pp_print_flush analysis_formatter ();;
close_out analysis_output;;
if not analysis_loaded then failwith "failed to load Library/analysis.ml";;

let statement =
  `!r:num->real. !S:real->bool.
     (!n:num. &0 < r n) /\
     r tends_num_real &0 /\
     S =
       {x:real |
          ?i:num->num.
            (!j k:num.
               j <= 1993 /\ k <= 1993 /\ j < k
               ==> i j < i k) /\
            x = sum (0..1993) (\j:num. r (i j))}
     ==> !a b:real.
           a < b
           ==> ?c d:real.
                 a <= c /\
                 c < d /\
                 d <= b /\
                 {x:real | c < x /\ x < d} INTER S = {}`;;
