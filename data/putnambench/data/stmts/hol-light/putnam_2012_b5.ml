(*
  Statement-only formalization of PutnamBench corpus artifact putnam_2012_b5:
  bounded real functions with values at least one admit a representation whose
  power-product supremum is attained as a maximum of affine functions. This
  file contains no proof.
*)

let analysis_output = open_out "/dev/null";;
let analysis_formatter = Format.formatter_of_out_channel analysis_output;;
let analysis_loaded =
  Toploop.use_file analysis_formatter "Library/transc.ml";;
Format.pp_print_flush analysis_formatter ();;
close_out analysis_output;;
if not analysis_loaded then failwith "failed to load Library/transc.ml";;

let statement =
  `let rpow =
     \a x:real. exp (x * ln a) in
   !g1 g2:real->real.
     (!s:real. &1 <= g1 s /\ &1 <= g2 s) /\
     (?B1 B2:real.
        !s:real. g1 s <= B1 /\ g2 s <= B2)
     ==>
     ?h1 h2:real->real.
       !x:real.
         ?t:real.
           sup {y:real |
                  ?s:real. y = rpow (g1 s) x * g2 s} =
             x * h1 t + h2 t /\
           (!u:real.
              x * h1 u + h2 u <= x * h1 t + h2 t)`;;
