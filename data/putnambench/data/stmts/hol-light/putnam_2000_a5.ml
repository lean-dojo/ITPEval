(*
  Statement-only formalization of PutnamBench corpus artifact putnam_2000_a5:
  three distinct integer-coordinate points on a circle of positive radius
  contain a pair separated by at least the cube root of the radius. This file
  contains no proof.
*)

let analysis_output = open_out "/dev/null";;
let analysis_formatter = Format.formatter_of_out_channel analysis_output;;
let analysis_loaded =
  Toploop.use_file analysis_formatter "Library/transc.ml";;
Format.pp_print_flush analysis_formatter ();;
close_out analysis_output;;
if not analysis_loaded then failwith "failed to load Library/transc.ml";;

let statement =
  `let lattice_point =
     \(p:real^2).
       ?m n:int.
         p$1 = real_of_int m /\ p$2 = real_of_int n in
   let edist =
     \(p:real^2) (q:real^2).
       sqrt ((p$1 - q$1) pow 2 + (p$2 - q$2) pow 2) in
   let rpow =
     \x p:real. if x = &0 then &0 else exp (p * ln x) in
   !r:real. !z:real^2. !S:real^2->bool.
     &0 < r /\
     FINITE S /\
     CARD S = 3 /\
     (!p:real^2. p IN S ==> lattice_point p) /\
     (!p:real^2. p IN S ==> edist p z = r)
     ==>
     ?p q:real^2.
       p IN S /\
       q IN S /\
       ~(p = q) /\
       edist p q >= rpow r (&1 / &3)`;;
