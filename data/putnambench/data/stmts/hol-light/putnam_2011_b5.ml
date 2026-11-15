(*
  Statement-only formalization of PutnamBench corpus artifact putnam_2011_b5:
  a uniform linear bound on whole-line integrals of squared sums of Cauchy
  kernels implies a positive cubic lower bound for the corresponding double
  sums of one plus squared pairwise distances. This file contains no proof.
*)

let analysis_output = open_out "/dev/null";;
let analysis_formatter = Format.formatter_of_out_channel analysis_output;;
let analysis_loaded =
  Toploop.use_file analysis_formatter "Library/transc.ml";;
Format.pp_print_flush analysis_formatter ();;
close_out analysis_output;;
if not analysis_loaded then failwith "failed to load Library/transc.ml";;

let statement =
  `let tends_at_posinfinity =
     \(f:real->real) (l:real).
       !e:real.
         &0 < e
         ==> ?c:real.
               !t:real. c <= t ==> abs (f t - l) < e in
   !a:num->real.
     (?A:real.
        !n:num.
          ?L:real.
            tends_at_posinfinity
              (\t:real.
                 integral(--t,t)
                   (\x:real.
                      (sum {i:num | i < n}
                         (\i. &1 / (&1 + (x - a i) pow 2))) pow 2))
              L /\
            L <= A * &n)
     ==> ?B:real.
           &0 < B /\
           !n:num.
             B * (&n pow 3) <=
             sum {i:num | i < n}
               (\i. sum {j:num | j < n}
                      (\j. &1 + (a i - a j) pow 2))`;;
