(*
  Statement-only formalization of PutnamBench artifact putnam_1973_b4:
  an integral inequality for a real C1 function whose derivative lies in
  (0,1], together with an equality example. This file contains no proof.
*)

let analysis_output = open_out "/dev/null";;
let analysis_formatter = Format.formatter_of_out_channel analysis_output;;
let analysis_loaded =
  Toploop.use_file analysis_formatter "Library/transc.ml";;
Format.pp_print_flush analysis_formatter ();;
close_out analysis_output;;
if not analysis_loaded then failwith "failed to load Library/transc.ml";;

let statement =
  `let admissible =
     \(g:real->real).
       ?g':real->real.
         (!x. (g diffl g' x) x) /\
         (!x e. &0 < e
                ==> ?d. &0 < d /\
                        !y. abs (y - x) < d
                            ==> abs (g' y - g' x) < e) /\
         (!x. &0 < g' x /\ g' x <= &1) /\
         g (&0) = &0 in
   let solution = \x:real. x in
   !f:real->real.
     admissible f
     ==>
     (integral(&0,&1) f) pow 2 >=
       integral(&0,&1) (\x. f x pow 3) /\
     admissible solution /\
     (integral(&0,&1) solution) pow 2 =
       integral(&0,&1) (\x. solution x pow 3)`;;
