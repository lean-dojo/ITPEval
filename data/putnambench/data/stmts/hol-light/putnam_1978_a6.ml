(*
  Statement-only formalization of PutnamBench artifact putnam_1978_a6:
  a finite nonempty set of n points in the Euclidean plane determines fewer
  than 2 n^(3/2) unordered pairs at unit distance. This file contains no proof.
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
  `let edist =
     \(P:real#real) (Q:real#real).
       sqrt ((FST P - FST Q) pow 2 + (SND P - SND Q) pow 2) in
   let rpow =
     \x p:real. if x = &0 then &0 else exp (p * ln x) in
   !S:(real#real)->bool. !n:num.
     FINITE S /\ n = CARD S /\ 0 < n
     ==>
     &(CARD
         {pair:(real#real)->bool |
            ?P Q:real#real.
              P IN S /\ Q IN S /\
              pair = {P,Q} /\ edist P Q = &1})
     < &2 * rpow (&n) (&3 / &2)`;;
