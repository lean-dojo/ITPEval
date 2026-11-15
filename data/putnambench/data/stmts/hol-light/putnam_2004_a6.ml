(*
  Statement-only formalization of PutnamBench corpus artifact putnam_2004_a6:
  an integral inequality for a continuous real-valued function on the unit
  square, comparing squared marginal integrals with its first and second
  moments. This file contains no proof.
*)

let analysis_output = open_out "/dev/null";;
let analysis_formatter = Format.formatter_of_out_channel analysis_output;;
let previous_file_loader = !Hol_loader.file_loader;;
let previous_verbose = !verbose;;
verbose := false;;
Hol_loader.file_loader :=
  (fun path -> Toploop.use_file analysis_formatter path);;
let analysis_loaded =
  Toploop.use_file analysis_formatter "Library/analysis.ml";;
Hol_loader.file_loader := previous_file_loader;;
verbose := previous_verbose;;
Format.pp_print_flush analysis_formatter ();;
close_out analysis_output;;
if not analysis_loaded then failwith "failed to load Library/analysis.ml";;

let statement =
  `let unit_square =
     \(p:real#real).
       &0 <= FST p /\ FST p <= &1 /\
       &0 <= SND p /\ SND p <= &1 in
   let edist =
     \(p:real#real) (q:real#real).
       sqrt ((FST p - FST q) pow 2 + (SND p - SND q) pow 2) in
   let continuous_on_unit_square =
     \(f:(real#real)->real).
       !p:real#real.
         unit_square p
         ==> !e:real.
               &0 < e
               ==> ?delta:real.
                     &0 < delta /\
                     !q:real#real.
                       unit_square q /\ edist q p < delta
                       ==> abs (f q - f p) < e in
   !f:(real#real)->real.
     continuous_on_unit_square f
     ==>
     integral(&0,&1)
       (\y:real.
          (integral(&0,&1) (\x:real. f (x,y))) pow 2) +
     integral(&0,&1)
       (\x:real.
          (integral(&0,&1) (\y:real. f (x,y))) pow 2)
     <=
     (integral(&0,&1)
        (\y:real.
           integral(&0,&1) (\x:real. f (x,y)))) pow 2 +
     integral(&0,&1)
       (\y:real.
          integral(&0,&1) (\x:real. (f (x,y)) pow 2))`;;
