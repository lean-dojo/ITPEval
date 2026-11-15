(*
  Statement-only formalization of PutnamBench corpus artifact putnam_2023_a3
  (putnambench__hol-light__putnam_2023_a3): the least positive zero attainable
  by differentiable real functions satisfying the stated coupled derivative
  bounds is pi/2. This file contains no proof.
*)

let analysis_output = open_out "/dev/null";;
let analysis_formatter = Format.formatter_of_out_channel analysis_output;;
let analysis_loaded =
  Toploop.use_file analysis_formatter "Library/transc.ml";;
Format.pp_print_flush analysis_formatter ();;
close_out analysis_output;;
if not analysis_loaded then failwith "failed to load Library/transc.ml";;

let statement =
  `let deriv =
     \(h:real->real) (x:real). @d:real. (h diffl d) x in
   let admissible =
     \r:real.
       ?f g:real->real.
         (!x:real. f differentiable x) /\
         (!x:real. g differentiable x) /\
         f (&0) > &0 /\
         g (&0) = &0 /\
         (!x:real.
            abs (deriv f x) <= abs (g x) /\
            abs (deriv g x) <= abs (f x)) /\
         f r = &0 in
   let solution = pi / &2 in
   &0 < solution /\
   admissible solution /\
   (!t:real.
      &0 < t /\ t < solution ==> ~(admissible t))`;;
