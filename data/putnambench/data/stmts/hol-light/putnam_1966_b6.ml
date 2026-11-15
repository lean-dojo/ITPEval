(*
  Statement-only formalization of PutnamBench artifact putnam_1966_b6:
  eventual boundedness of every twice-differentiable real solution of
  y'' + exp(x) y = 0. This file contains no proof.
*)

let analysis_output = open_out "/dev/null";;
let analysis_formatter = Format.formatter_of_out_channel analysis_output;;
let previous_file_loader = !Hol_loader.file_loader;;
Hol_loader.file_loader :=
  (fun path -> Toploop.use_file analysis_formatter path);;
let transc_loaded =
  Toploop.use_file analysis_formatter "Library/transc.ml";;
Hol_loader.file_loader := previous_file_loader;;
Format.pp_print_flush analysis_formatter ();;
close_out analysis_output;;
if not transc_loaded then failwith "failed to load Library/transc.ml";;

let statement =
  `let deriv =
     \(g:real->real) (x:real). @d. (g diffl d) x in
   !y:real->real.
     (!x. y differentiable x /\ deriv y differentiable x) /\
     (!x. deriv (deriv y) x + exp x * y x = &0)
     ==> ?r s N:real.
           !x. x > N ==> r <= y x /\ y x <= s`;;
