(*
  Statement-only formalization of PutnamBench artifact putnam_1969_a1:
  the classification of all possible ranges of bivariate polynomials with
  real coefficients. This file contains no proof.
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
  `{S:real->bool |
      ?f:(real list)list.
        S =
        {z:real |
          ?x y:real. poly (MAP (\p:real list. poly p y) f) x = z}} =
   {S:real->bool |
      (?a:real. S = {a}) \/
      (?a:real. S = {z:real | a <= z}) \/
      (?a:real. S = {z:real | z <= a}) \/
      (?a:real. S = {z:real | z < a}) \/
      (?a:real. S = {z:real | a < z}) \/
      S = (:real)}`;;
