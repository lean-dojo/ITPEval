(*
  Statement-only formalization of PutnamBench corpus artifact putnam_1984_a5:
  evaluation of a monomial triple integral over the nonnegative unit simplex
  as a quotient of factorials. This file contains no proof.
*)

let analysis_output = open_out "/dev/null";;
let analysis_formatter = Format.formatter_of_out_channel analysis_output;;
let analysis_loaded =
  Toploop.use_file analysis_formatter "Library/transc.ml";;
Format.pp_print_flush analysis_formatter ();;
close_out analysis_output;;
if not analysis_loaded then failwith "failed to load Library/transc.ml";;

let statement =
  `integral(&0,&1)
     (\z:real.
        integral(&0,&1 - z)
          (\y:real.
             integral(&0,&1 - y - z)
               (\x:real.
                  x pow 1 * y pow 9 * z pow 8 *
                  (&1 - x - y - z) pow 4))) =
   (&(FACT 1) * &(FACT 9) * &(FACT 8) * &(FACT 4)) / &(FACT 25)`;;
