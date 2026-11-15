(*
  Statement-only formalization of PutnamBench corpus artifact putnam_1991_b6:
  the greatest real bound for a hyperbolic-sine inequality involving positive
  weighted geometric means and endpoint terms. This file contains no proof.
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
  `let rpow =
     \x p:real. exp (p * ln x) in
   let sinh =
     \z:real. (exp z - exp (--z)) / &2 in
   !a b:real.
     &0 < a /\ &0 < b
     ==>
     let admissible =
       \c:real.
         !u:real.
           &0 < abs u /\ abs u <= c
           ==>
           !x:real.
             &0 < x /\ x < &1
             ==>
             rpow a x * rpow b (&1 - x) <=
             a * (sinh (u * x) / sinh u) +
             b * (sinh (u * (&1 - x)) / sinh u) in
     let solution = abs (ln (a / b)) in
     admissible solution /\
     (!c:real. admissible c ==> c <= solution)`;;
