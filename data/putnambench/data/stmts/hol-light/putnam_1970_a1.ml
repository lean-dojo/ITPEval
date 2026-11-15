(*
  Statement-only formalization of PutnamBench artifact putnam_1970_a1:
  for positive real a and b, the zero coefficients in the local power-series
  expansion of exp(a * x) * cos(b * x) are either absent or infinite. This
  file contains no proof.
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
  `!a b:real. !f:real->real. !p:num->real. !S:num->bool.
     f = (\x:real. exp (a * x) * cos (b * x)) /\
     S = {n:num | p n = &0} /\
     a > &0 /\
     b > &0 /\
     (?c:real.
        c > &0 /\
        !x:real.
          abs x < c
          ==> (\n:num. p n * x pow n) sums (f x))
     ==> S = {} \/ INFINITE S`;;
