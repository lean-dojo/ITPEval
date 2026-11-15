(*
  Statement-only formalization of PutnamBench artifact putnam_1977_a6:
  vanishing integrals over every maximal centered axis-aligned square in the
  unit square force a continuous real function to vanish there; the answer is
  affirmative. This file contains no proof.
*)

let analysis_output = open_out "/dev/null";;
let analysis_formatter = Format.formatter_of_out_channel analysis_output;;
let analysis_loaded =
  Toploop.use_file analysis_formatter "Library/analysis.ml";;
Format.pp_print_flush analysis_formatter ();;
close_out analysis_output;;
if not analysis_loaded then failwith "failed to load Library/analysis.ml";;

let statement =
  `let X =
     {p:real#real |
        &0 <= FST p /\ FST p <= &1 /\
        &0 <= SND p /\ SND p <= &1} in
   let room =
     \(p:real#real).
       min (min (FST p) (&1 - FST p))
           (min (SND p) (&1 - SND p)) in
   let continuous_plane =
     \(f:(real#real)->real).
       !x y e:real.
         &0 < e
         ==> ?d:real.
               &0 < d /\
               !u v:real.
                 (u - x) pow 2 + (v - y) pow 2 < d pow 2
                 ==> abs (f (u,v) - f (x,y)) < e in
   let putnam_1977_a6_solution = T in
   ((!f:(real#real)->real.
       continuous_plane f
       ==> (!p:real#real.
              p IN X
              ==> integral(FST p - room p,FST p + room p)
                    (\x.
                       integral(SND p - room p,SND p + room p)
                         (\y. f (x,y))) = &0)
           ==> !p:real#real. p IN X ==> f p = &0) <=>
    putnam_1977_a6_solution)`;;
