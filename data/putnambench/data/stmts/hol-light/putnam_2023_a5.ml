(*
  Statement-only formalization of PutnamBench corpus artifact putnam_2023_a5
  (putnambench__hol-light__putnam_2023_a5): the three complex zeros of the
  finite power sum weighted by counts of ones in base 3. This file contains
  no proof.
*)

let complex_output = open_out "/dev/null";;
let complex_formatter = Format.formatter_of_out_channel complex_output;;
let previous_file_loader = !Hol_loader.file_loader;;
Hol_loader.file_loader :=
  (fun path -> Toploop.use_file complex_formatter path);;
let complex_loaded =
  Toploop.use_file complex_formatter "Complex/complexnumbers.ml";;
Hol_loader.file_loader := previous_file_loader;;
Format.pp_print_flush complex_formatter ();;
close_out complex_output;;
if not complex_loaded then
  failwith "failed to load Complex/complexnumbers.ml";;

let statement =
  `let num_ones =
     \k:num.
       CARD
         {j:num |
            (k DIV (3 EXP j)) MOD 3 = 1} in
   let center =
     --(Cx(&(3 EXP 1010) - &1) / Cx(&2)) in
   let offset =
     Cx(sqrt(&(9 EXP 1010) - &1)) * ii / Cx(&4) in
   !z:complex.
     (iterate ((+):complex->complex->complex)
        (0..3 EXP 1010 - 1)
        (\k:num.
           Cx(-- &2) pow (num_ones k) *
           (z + Cx(&k)) pow 2023) = Cx(&0)
      <=>
      z = center \/
      z = center + offset \/
      z = center - offset)`;;
