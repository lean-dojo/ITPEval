(*
  Statement-only formalization of PutnamBench artifact putnam_2021_a2
  (putnambench__hol-light__putnam_2021_a2): the limit at positive infinity
  of g(x)/x, where g(x) is defined for positive x by a right-hand real-power
  limit at zero, is exp(1). This file contains no proof.
*)

let transc_output = open_out "/dev/null";;
let transc_formatter = Format.formatter_of_out_channel transc_output;;
let previous_file_loader = !Hol_loader.file_loader;;
let previous_verbose = !verbose;;
let previous_type_invention_warning = !type_invention_warning;;
verbose := false;;
type_invention_warning := false;;
Hol_loader.file_loader :=
  (fun path -> Toploop.use_file transc_formatter path);;
let transc_loaded =
  Toploop.use_file transc_formatter "Library/transc.ml";;
Hol_loader.file_loader := previous_file_loader;;
verbose := previous_verbose;;
type_invention_warning := previous_type_invention_warning;;
Format.pp_print_flush transc_formatter ();;
close_out transc_output;;
if not transc_loaded then failwith "failed to load Library/transc.ml";;

let statement =
  `let rpow =
     \a p:real. exp (p * ln a) in
   let tends_at_right_zero =
     \(f:real->real) (l:real).
       !e:real.
         &0 < e
         ==> ?d:real.
               &0 < d /\
               !r:real.
                 &0 < r /\ r < d ==> abs (f r - l) < e in
   let tends_at_posinfinity =
     \(f:real->real) (l:real).
       !e:real.
         &0 < e
         ==> ?B:real.
               !x:real. B <= x ==> abs (f x - l) < e in
   !g:real->real.
     (!x:real.
        &0 < x
        ==>
        tends_at_right_zero
          (\r:real.
             rpow
               (rpow (x + &1) (r + &1) -
                rpow x (r + &1))
               (&1 / r))
          (g x))
     ==>
     tends_at_posinfinity
       (\x:real. g x / x)
       (exp (&1))`;;
