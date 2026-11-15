(*
  Statement-only formalization of PutnamBench artifact putnam_1965_b4:
  the recurrence and pointwise convergence set for a quotient of the even
  and odd parts of a binomial expansion. This file contains no proof.
*)

let library_output = open_out "/dev/null";;
let library_formatter = Format.formatter_of_out_channel library_output;;
let binomial_loaded =
  Toploop.use_file library_formatter "Library/binomial.ml";;
let analysis_loaded =
  Toploop.use_file library_formatter "Library/analysis.ml";;
Format.pp_print_flush library_formatter ();;
close_out library_output;;
if not binomial_loaded then failwith "failed to load Library/binomial.ml";;
if not analysis_loaded then failwith "failed to load Library/analysis.ml";;

let statement =
  `let p = \(h:real->real) (x:real). h x + x in
   let q = \(h:real->real) (x:real). h x + &1 in
   let s = \x:real. &0 <= x in
   let g = \x:real. sqrt x in
   !f u v:num->real->real. !n:num.
     (!m:num. 0 < m
              ==> !x:real.
                    u m x =
                    sum (0..m DIV 2)
                        (\i. &(binom (m,2 * i)) * x pow i)) /\
     (!m:num. 0 < m
              ==> !x:real.
                    v m x =
                    sum (0..(m - 1) DIV 2)
                        (\i. &(binom (m,2 * i + 1)) * x pow i)) /\
     (!m:num. 0 < m
              ==> !x:real. f m x = u m x / v m x) /\
     0 < n
     ==> (!x:real.
            ~(v n x = &0)
            ==> ~(v (n + 1) x = &0)
            ==> ~(q (f n) x = &0)
            ==> f (n + 1) x = p (f n) x / q (f n) x) /\
         s = {x:real | ?l:real.
                       (\m:num. f m x) tends_num_real l} /\
         (!x:real. s x
                   ==> (\m:num. f m x) tends_num_real (g x))`;;
