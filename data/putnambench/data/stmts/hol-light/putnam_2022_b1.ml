(*
  Statement-only formalization of PutnamBench corpus artifact putnam_2022_b1
  (putnambench__hol-light__putnam_2022_b1): nonvanishing of every coefficient
  in the exponential power series of an integer polynomial with zero constant
  term and odd linear coefficient. This file contains no proof.
*)

let analysis_output = open_out "/dev/null";;
let analysis_formatter = Format.formatter_of_out_channel analysis_output;;
let analysis_loaded =
  Toploop.use_file analysis_formatter "Library/transc.ml";;
Format.pp_print_flush analysis_formatter ();;
close_out analysis_output;;
if not analysis_loaded then failwith "failed to load Library/transc.ml";;

let statement =
  `!P:num->int. !b:num->real.
     (?N:num.
        (!k:num. N < k ==> P k = &0) /\
        P 0 = &0 /\
        (?m:int. P 1 = &2 * m + &1) /\
        (!x:real.
           (\k:num. b k * x pow k) sums
           exp (sum (0..N)
                    (\k:num. real_of_int (P k) * x pow k))))
     ==>
     !k:num. ~(b k = &0)`;;
