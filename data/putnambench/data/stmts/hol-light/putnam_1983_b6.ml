(*
  Statement-only formalization of PutnamBench corpus artifact putnam_1983_b6:
  integer-coefficient polynomials whose squared values at a nontrivial complex
  root of unity sum to negative one. This file contains no proof.
*)

let cpoly_output = open_out "/dev/null";;
let cpoly_formatter = Format.formatter_of_out_channel cpoly_output;;
let previous_file_loader = !Hol_loader.file_loader;;
Hol_loader.file_loader :=
  (fun path -> Toploop.use_file cpoly_formatter path);;
let cpoly_loaded =
  Toploop.use_file cpoly_formatter "Complex/cpoly.ml";;
Hol_loader.file_loader := previous_file_loader;;
Format.pp_print_flush cpoly_formatter ();;
close_out cpoly_output;;
if not cpoly_loaded then failwith "failed to load Complex/cpoly.ml";;

let statement =
  `let integer_coefficients =
     \p:complex list.
       !k:num.
         k < LENGTH p
         ==> ?z:int. EL k p = Cx(real_of_int z) in
   !n:num alpha:complex.
     0 < n /\
     alpha pow (2 EXP n + 1) - Cx(&1) = Cx(&0) /\
     ~(alpha = Cx(&1))
     ==> ?p q:complex list.
           integer_coefficients p /\
           integer_coefficients q /\
           (poly p alpha) pow 2 + (poly q alpha) pow 2 = --Cx(&1)`;;
