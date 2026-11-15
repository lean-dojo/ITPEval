(*
  Statement-only formalization of PutnamBench artifact putnam_1968_a6:
  the classification of nonconstant polynomials with coefficients all equal
  to plus or minus one and with only real roots. This file contains no proof.
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
  `!p:complex list.
     let q = normalize p in
     (2 <= LENGTH q /\
      (!k:num.
         k < LENGTH q
         ==> EL k q = Cx(&1) \/ EL k q = --(Cx(&1))) /\
      (!z:complex.
         poly q z = Cx(&0)
         ==> ?r:real. z = Cx r))
     <=>
     q = [--(Cx(&1)); Cx(&1)] \/
     q = [Cx(&1); --(Cx(&1))] \/
     q = [Cx(&1); Cx(&1)] \/
     q = [--(Cx(&1)); --(Cx(&1))] \/
     q = [--(Cx(&1)); Cx(&1); Cx(&1)] \/
     q = [Cx(&1); --(Cx(&1)); --(Cx(&1))] \/
     q = [--(Cx(&1)); --(Cx(&1)); Cx(&1)] \/
     q = [Cx(&1); Cx(&1); --(Cx(&1))] \/
     q = [--(Cx(&1)); --(Cx(&1)); Cx(&1); Cx(&1)] \/
     q = [Cx(&1); Cx(&1); --(Cx(&1)); --(Cx(&1))] \/
     q = [Cx(&1); --(Cx(&1)); --(Cx(&1)); Cx(&1)] \/
     q = [--(Cx(&1)); Cx(&1); Cx(&1); --(Cx(&1))]`;;
