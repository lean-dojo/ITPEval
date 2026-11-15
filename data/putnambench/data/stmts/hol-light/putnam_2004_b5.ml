(*
  Statement-only formalization of PutnamBench corpus artifact putnam_2004_b5:
  evaluation as 2/e of the left-hand limit at 1 of an infinite product with
  real exponents. This file contains no proof.
*)

let analysis_output = open_out "/dev/null";;
let analysis_formatter = Format.formatter_of_out_channel analysis_output;;
let previous_file_loader = !Hol_loader.file_loader;;
let previous_verbose = !verbose;;
verbose := false;;
Hol_loader.file_loader :=
  (fun path -> Toploop.use_file analysis_formatter path);;
let analysis_loaded =
  Toploop.use_file analysis_formatter "Library/transc.ml";;
Hol_loader.file_loader := previous_file_loader;;
verbose := previous_verbose;;
Format.pp_print_flush analysis_formatter ();;
close_out analysis_output;;
if not analysis_loaded then failwith "failed to load Library/transc.ml";;

let statement =
  `let rpow =
     \a p:real. exp (p * ln a) in
   let tends_at_left =
     \(f:real->real) (a:real) (l:real).
       !e:real.
         &0 < e
         ==> ?d:real.
               &0 < d /\
               !x:real.
                 x < a /\ abs (x - a) < d
                 ==> abs (f x - l) < e in
   !xprod:real->real.
     (!x:real.
        &0 < x /\ x < &1
        ==>
        (\N:num.
           product {n:num | n < N}
             (\n:num.
                rpow
                  ((&1 + x pow (n + 1)) /
                   (&1 + x pow n))
                  (x pow n)))
        tends_num_real
        (xprod x))
     ==>
     tends_at_left xprod (&1) (&2 / exp (&1))`;;
