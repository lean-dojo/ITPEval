(*
  Statement-only formalization of PutnamBench artifact putnam_1963_b3:
  classification of twice-differentiable real solutions of a quadratic
  functional equation. This file contains no proof.
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
   !f:real->real.
     (!x. f differentiable x /\ deriv f differentiable x)
     ==>
     (((!x y:real.
          (f x) pow 2 - (f y) pow 2 = f (x + y) * f (x - y)) <=>
       (?A k:real.
          f = (\x. A * ((exp (k * x) - exp (--(k * x))) / &2))) \/
       (?A:real. f = (\x. A * x)) \/
       (?A k:real. f = (\x. A * sin (k * x)))))`;;
