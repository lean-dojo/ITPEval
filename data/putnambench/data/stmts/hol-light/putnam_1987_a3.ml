(*
  Statement-only formalization of PutnamBench artifact putnam_1987_a3:
  determining whether positivity of a twice-differentiable solution of
  y'' - 2*y' + y = 2*exp(x) forces positivity of its derivative, and
  conversely. This file contains no proof.
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
     \(h:real->real) (x:real). @d. (h diffl d) x in
   let putnam_1987_a3_solution = (F,T) in
   ((!f:real->real.
       (!x:real.
          f differentiable x /\
          deriv f differentiable x /\
          deriv (deriv f) x - &2 * deriv f x + f x = &2 * exp x /\
          f x > &0)
       ==> !x:real. deriv f x > &0) <=>
     FST putnam_1987_a3_solution) /\
   ((!g:real->real.
       (!x:real.
          g differentiable x /\
          deriv g differentiable x /\
          deriv (deriv g) x - &2 * deriv g x + g x = &2 * exp x /\
          deriv g x > &0)
       ==> !x:real. g x > &0) <=>
     SND putnam_1987_a3_solution)`;;
