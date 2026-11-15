(*
  Statement-only formalization of PutnamBench corpus artifact putnam_2006_b5:
  the maximum over continuous real functions on the unit interval of the
  difference between the specified weighted integrals is 1/16. This file
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
  `let unit_interval = {x:real | &0 <= x /\ x <= &1} in
   let continuous_on =
     \(f:real->real) (s:real->bool).
       !x. x IN s
           ==> !e. &0 < e
                   ==> ?d. &0 < d /\
                           !y. y IN s /\ abs (y - x) < d
                               ==> abs (f y - f x) < e in
   let objective =
     \(f:real->real).
       integral(&0,&1) (\x:real. x pow 2 * f x) -
       integral(&0,&1) (\x:real. x * (f x) pow 2) in
   let is_greatest =
     \(s:real->bool) (m:real).
       m IN s /\ (!y:real. y IN s ==> y <= m) in
   is_greatest
     {y:real |
        ?f:real->real.
          continuous_on f unit_interval /\ objective f = y}
     (&1 / &16)`;;
