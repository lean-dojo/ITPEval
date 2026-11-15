(*
  Statement-only formalization of PutnamBench corpus artifact putnam_1999_b2:
  a complex polynomial satisfying P(x) = Q(x)P''(x) for a quadratic Q has
  as many distinct roots as its degree if it has two distinct roots. This
  file contains no proof.
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
  `let cpoly_diff =
     \P:complex list.
       list_of_seq
         (\i:num. Cx(&(i + 1)) * EL (i + 1) P)
         (PRE (LENGTH P)) in
   !P Q:complex list.
     degree Q = 2 /\
     (!x:complex.
        poly P x = poly Q x * poly (cpoly_diff (cpoly_diff P)) x)
     ==>
     ((?x1 x2:complex.
         ~(x1 = x2) /\
         poly P x1 = Cx(&0) /\
         poly P x2 = Cx(&0))
      ==>
      ?S:complex->bool.
        S HAS_SIZE degree P /\
        (!z:complex. z IN S ==> poly P z = Cx(&0)))`;;
