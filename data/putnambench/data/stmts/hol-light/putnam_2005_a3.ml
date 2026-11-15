(*
  Statement-only formalization of PutnamBench corpus artifact putnam_2005_a3:
  every nonzero critical point of a positive-degree complex polynomial
  normalized by the principal complex power z raised to half its degree lies
  on the unit circle when all polynomial zeros lie there. This file contains
  no proof.
*)

let complex_output = open_out "/dev/null";;
let complex_formatter = Format.formatter_of_out_channel complex_output;;
let previous_file_loader = !Hol_loader.file_loader;;
Hol_loader.file_loader :=
  (fun path -> Toploop.use_file complex_formatter path);;
let complex_loaded =
  Toploop.use_file complex_formatter "Complex/complex_transc.ml";;
Hol_loader.file_loader := previous_file_loader;;
Format.pp_print_flush complex_formatter ();;
close_out complex_output;;
if not complex_loaded then
  failwith "failed to load Complex/complex_transc.ml";;

let statement =
  `!c:num->complex. !n:num. !g:complex->complex. !z:complex.
     let poly =
       \w:complex.
         iterate ((+):complex->complex->complex)
           (0..n) (\k. c k * w pow k) in
     let principal_cpow =
       \w:complex. \s:complex.
         if w = Cx(&0) then Cx(&0) else cexp (clog w * s) in
     0 < n /\
     ~(c n = Cx(&0)) /\
     (!w:complex. poly w = Cx(&0) ==> norm w = &1) /\
     (!w:complex.
        g w = poly w / principal_cpow w (Cx(&n) / Cx(&2))) /\
     ~(z = Cx(&0)) /\
     (!e:real.
        &0 < e
        ==> ?d:real.
              &0 < d /\
              !w:complex.
                &0 < norm (w - z) /\ norm (w - z) < d
                ==> norm ((g w - g z) / (w - z)) < e)
     ==> norm z = &1`;;
