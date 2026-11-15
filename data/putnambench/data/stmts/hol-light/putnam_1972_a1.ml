(*
  Statement-only formalization of PutnamBench artifact putnam_1972_a1:
  no four consecutive binomial coefficients with positive admissible indices
  form an arithmetic progression. This file contains no proof.
*)

let binomial_output = open_out "/dev/null";;
let binomial_formatter = Format.formatter_of_out_channel binomial_output;;
let binomial_loaded =
  Toploop.use_file binomial_formatter "Library/binomial.ml";;
Format.pp_print_flush binomial_formatter ();;
close_out binomial_output;;
if not binomial_loaded then failwith "failed to load Library/binomial.ml";;

let statement =
  `let fourAP =
     \n1 n2 n3 n4:int.
       n4 - n3 = n3 - n2 /\ n3 - n2 = n2 - n1 in
   !n:num.
     0 < n
     ==> ~(?r:num.
              0 < r /\
              r + 3 <= n /\
              fourAP (&(binom (n,r)))
                     (&(binom (n,r + 1)))
                     (&(binom (n,r + 2)))
                     (&(binom (n,r + 3))))`;;
