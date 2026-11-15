(*
  Statement-only formalization of PutnamBench corpus artifact putnam_2007_a4:
  classification of real polynomials that map every base-10 repunit to a
  base-10 repunit. This file contains no proof.
*)

let poly_output = open_out "/dev/null";;
let poly_formatter = Format.formatter_of_out_channel poly_output;;
let previous_file_loader = !Hol_loader.file_loader;;
Hol_loader.file_loader :=
  (fun path -> Toploop.use_file poly_formatter path);;
let poly_loaded =
  Toploop.use_file poly_formatter "Library/poly.ml";;
Hol_loader.file_loader := previous_file_loader;;
Format.pp_print_flush poly_formatter ();;
close_out poly_output;;
if not poly_loaded then failwith "failed to load Library/poly.ml";;

let statement =
  `let repunit =
     \x:real.
       ?m:num.
         1 <= m /\
         x = ((&10:real) pow m - &1) / &9 in
   let integer_power =
     \(x:real) (z:int).
       if (&0:int) <= z
       then x pow (num_of_int z)
       else inv (x pow (num_of_int (--z))) in
   !p:real list.
     ((!n:real. repunit n ==> repunit (poly p n)) <=>
      ?d:num. ?c:int.
        (&1:int) - &d <= c /\
        !x:real.
          poly p x =
          (integer_power (&10) c * (&9 * x + &1) pow d - &1) / &9)`;;
