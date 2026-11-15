(*
  Statement-only formalization of PutnamBench corpus artifact putnam_2009_b4:
  the vector space of balanced real bivariate polynomials of total degree at
  most 2009 has dimension 2020050. This file contains no proof.
*)

let analysis_output = open_out "/dev/null";;
let analysis_formatter = Format.formatter_of_out_channel analysis_output;;
let analysis_loaded =
  Toploop.use_file analysis_formatter "Library/transc.ml";;
Format.pp_print_flush analysis_formatter ();;
close_out analysis_output;;
if not analysis_loaded then failwith "failed to load Library/transc.ml";;

let statement =
  `let solution = 2020050 in
   let degree_at_most_2009 =
     \p:(num#num)->real.
       !i j:num. 2009 < i + j ==> p(i,j) = &0 in
   let polynomial_value =
     \p:(num#num)->real. \x:real. \y:real.
       sum (0..2009)
         (\i:num.
            sum (0..(2009 - i))
              (\j:num. p(i,j) * x pow i * y pow j)) in
   let balanced =
     \p:(num#num)->real.
       !r:real.
         &0 < r
         ==>
         integral(&0,&2 * pi)
           (\t:real. polynomial_value p (r * cos t) (r * sin t)) /
         (&2 * pi * r) =
         &0 in
   let V =
     \p:(num#num)->real. degree_at_most_2009 p /\ balanced p in
   ?basis:num->(num#num)->real.
     (!k:num. k < solution ==> V (basis k)) /\
     (!c:num->real.
        (!i j:num.
           sum (0..(solution - 1))
             (\k:num. c k * basis k (i,j)) =
           &0)
        ==>
        !k:num. k < solution ==> c k = &0) /\
     (!p:(num#num)->real.
        V p
        ==>
        ?c:num->real.
          !i j:num.
            p(i,j) =
            sum (0..(solution - 1))
              (\k:num. c k * basis k (i,j)))`;;
