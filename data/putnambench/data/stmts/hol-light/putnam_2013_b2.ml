(*
  Statement-only formalization of PutnamBench corpus artifact putnam_2013_b2:
  the maximum value at zero of a nonnegative cosine polynomial whose
  coefficients at positive multiples of 3 vanish is 3, and it is attained.
  This file contains no proof.
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
  `let cosine_polynomial =
     \(f:real->real).
       ?N:num. ?a:num->real.
         1 <= N /\
         (!x:real.
            f x =
            &1 + sum (1..N)
              (\n:num. a n * cos (&2 * pi * &n * x))) /\
         (!x:real. &0 <= f x) /\
         (!n:num. n IN (1..N) /\ 3 divides n ==> a n = &0) in
   let values_at_zero =
     {y:real |
        ?f:real->real. cosine_polynomial f /\ y = f (&0)} in
   &3 IN values_at_zero /\
   (!y:real. y IN values_at_zero ==> y <= &3)`;;
