(*
  Statement-only formalization of PutnamBench corpus artifact putnam_2007_b6:
  asymptotic upper and lower bounds for the number of unordered collections
  of factorial-valued coins summing to n factorial. This file contains no proof.
*)

let transc_output = open_out "/dev/null";;
let transc_formatter = Format.formatter_of_out_channel transc_output;;
let previous_file_loader = !Hol_loader.file_loader;;
Hol_loader.file_loader :=
  (fun path -> Toploop.use_file transc_formatter path);;
let transc_loaded =
  Toploop.use_file transc_formatter "Library/transc.ml";;
Hol_loader.file_loader := previous_file_loader;;
Format.pp_print_flush transc_formatter ();;
close_out transc_output;;
if not transc_loaded then failwith "failed to load Library/transc.ml";;

let statement =
  `let f =
     \n:num.
       CARD
         {m:num->num |
            (!x:num.
               ~(x IN IMAGE FACT (1..n))
               ==> m x = 0) /\
            nsum (IMAGE FACT (1..n))
              (\x:num. m x * x) = FACT n} in
   let rpow =
     \x p:real. if x = &0 then &0 else exp (p * ln x) in
   ?C:real.
     !n:num.
       2 <= n
       ==>
       rpow (&n) (((&n) pow 2) / &2 - C * &n) *
         exp ((--((&n) pow 2)) / &4) <= &(f n) /\
       &(f n) <=
         rpow (&n) (((&n) pow 2) / &2 + C * &n) *
         exp ((--((&n) pow 2)) / &4)`;;
