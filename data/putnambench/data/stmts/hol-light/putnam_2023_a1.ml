(*
  Statement-only formalization of PutnamBench corpus artifact putnam_2023_a1
  (putnambench__hol-light__putnam_2023_a1): the least positive integer for
  which the absolute second derivative at zero of a finite cosine product
  exceeds 2023. This file contains no proof.
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
  `let deriv =
     \(g:real->real) (x:real). @d. (g diffl d) x in
   let f =
     \(n:num) (x:real).
       product (1..n) (\i:num. cos (&i * x)) in
   let qualifies =
     \n:num.
       0 < n /\
       abs (deriv (deriv (f n)) (&0)) > &2023 in
   qualifies 18 /\
   (!n:num. qualifies n ==> 18 <= n)`;;
