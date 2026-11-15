(*
  Statement-only formalization of PutnamBench corpus artifact putnam_2022_b3
  (putnambench__hol-light__putnam_2022_b3): every red-blue coloring of the
  positive reals reaches the all-red coloring after finitely many iterations
  of the same-color distance recoloring operation. This file contains no
  proof.
*)

let analysis_output = open_out "/dev/null";;
let analysis_formatter = Format.formatter_of_out_channel analysis_output;;
let iter_loaded =
  Toploop.use_file analysis_formatter "Library/iter.ml";;
Format.pp_print_flush analysis_formatter ();;
close_out analysis_output;;
if not iter_loaded then failwith "failed to load Library/iter.ml";;

let statement =
  `let recolor =
     \(isred:real->bool) (d:real).
       ?p q:real.
         &0 < p /\
         &0 < q /\
         p < q /\
         (isred p <=> isred q) /\
         q - p = d in
   let putnam_2022_b3_solution = T in
   ((!isred:real->bool.
       ?k:num.
         !p:real.
           &0 < p ==> ITER k recolor isred p)
    <=>
    putnam_2022_b3_solution)`;;
