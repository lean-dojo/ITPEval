(*
  Statement-only formalization of PutnamBench artifact putnam_1967_a5:
  every convex region in the Euclidean plane with area greater than pi / 4
  contains two points exactly one unit apart. This file contains no proof.
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
  `let convex =
     \(R:(real#real)->bool).
       !x y:real#real. !u v:real.
         x IN R /\ y IN R /\ &0 <= u /\ &0 <= v /\ u + v = &1
         ==> (u * FST x + v * FST y,
              u * SND x + v * SND y) IN R in
   let area_greater_than =
     \(R:(real#real)->bool) (a:real).
       ?e:real.
         &0 < e /\
         !left right bottom top:num->real.
           (!n. left n <= right n /\ bottom n <= top n) /\
           (!p:real#real.
              p IN R
              ==> ?n.
                    left n <= FST p /\ FST p <= right n /\
                    bottom n <= SND p /\ SND p <= top n) /\
           summable
             (\n. (right n - left n) * (top n - bottom n))
           ==> a + e <=
               suminf
                 (\n. (right n - left n) * (top n - bottom n)) in
   let edist =
     \(P:real#real) (Q:real#real).
       sqrt ((FST P - FST Q) pow 2 + (SND P - SND Q) pow 2) in
   !R:(real#real)->bool.
     convex R /\ area_greater_than R (pi / &4)
     ==> ?P Q:real#real.
           P IN R /\ Q IN R /\ edist P Q = &1`;;
