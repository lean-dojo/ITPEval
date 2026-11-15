(*
  Statement-only formalization of PutnamBench artifact putnam_1964_a2:
  nonexistence of a positive continuous density on [0,1] whose first two
  moments have zero variance. This file contains no proof.
*)

let analysis_output = open_out "/dev/null";;
let analysis_formatter = Format.formatter_of_out_channel analysis_output;;
let analysis_loaded =
  Toploop.use_file analysis_formatter "Library/analysis.ml";;
Format.pp_print_flush analysis_formatter ();;
close_out analysis_output;;
if not analysis_loaded then failwith "failed to load Library/analysis.ml";;

let statement =
  `let unit_interval = {x:real | &0 <= x /\ x <= &1} in
   let continuous_on =
     \(f:real->real) (s:real->bool).
       !x. x IN s
           ==> !e. &0 < e
                   ==> ?d. &0 < d /\
                           !y. y IN s /\ abs (y - x) < d
                               ==> abs (f y - f x) < e in
   let solution = \alpha:real. {}:(real->real)->bool in
   !alpha:real.
     solution alpha =
     {f:real->real |
        (!x. x IN unit_interval ==> &0 < f x) /\
        continuous_on f unit_interval /\
        integral(&0,&1) f = &1 /\
        integral(&0,&1) (\x. x * f x) = alpha /\
        integral(&0,&1) (\x. x pow 2 * f x) = alpha pow 2}`;;
