(*
  Statement-only formalization of PutnamBench corpus artifact putnam_1987_b5:
  surjectivity onto real vectors of the real part of a complex rectangular
  matrix map under the stated row-kernel condition. This file contains no proof.
*)

let complex_output = open_out "/dev/null";;
let complex_formatter = Format.formatter_of_out_channel complex_output;;
let complex_loaded =
  Toploop.use_file complex_formatter "Complex/complexnumbers.ml";;
Format.pp_print_flush complex_formatter ();;
close_out complex_output;;
if not complex_loaded then
  failwith "failed to load Complex/complexnumbers.ml";;

let statement =
  `!n:num. !M:num->num->complex.
     0 < n /\
     (!z:num->complex.
        (!j:num.
           j < n
           ==>
           iterate ((+):complex->complex->complex)
             {i:num | i < 2 * n} (\i. z i * M i j) =
           Cx(&0))
        ==>
        (~(!i:num. i < 2 * n ==> z i = Cx(&0))
         ==>
         ?i:num. i < 2 * n /\ ~(Im (z i) = &0)))
     ==>
     !r:num->real.
       ?w:num->complex.
         !i:num.
           i < 2 * n
           ==>
           Re
             (iterate ((+):complex->complex->complex)
                {j:num | j < n} (\j. M i j * w j)) =
           r i`;;
