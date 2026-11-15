(*
  Statement-only formalization of PutnamBench corpus artifact putnam_2023_b4
  (putnambench__hol-light__putnam_2023_b4): the least time for a piecewise
  twice-differentiable function with prescribed accelerations and reset
  right-hand derivative limits to reach 2023 is 29. This file contains no
  proof.
*)

let analysis_output = open_out "/dev/null";;
let analysis_formatter = Format.formatter_of_out_channel analysis_output;;
let analysis_loaded =
  Toploop.use_file analysis_formatter "Library/analysis.ml";;
Format.pp_print_flush analysis_formatter ();;
close_out analysis_output;;
if not analysis_loaded then failwith "failed to load Library/analysis.ml";;

let statement =
  `let continuous_on_ray =
     \(f:real->real) (a:real).
       !x:real.
         a <= x
         ==> !e:real.
               &0 < e
               ==> ?d:real.
                     &0 < d /\
                     !y:real.
                       a <= y /\ abs (y - x) < d
                       ==> abs (f y - f x) < e in
   let right_limit =
     \(g:real->real) (a:real) (l:real).
       !e:real.
         &0 < e
         ==> ?d:real.
               &0 < d /\
               !x:real.
                 a < x /\ x - a < d
                 ==> abs (g x - l) < e in
   let attainable =
     \tau:real.
       &0 <= tau /\
       ?n:num. ?ts:num->real. ?f fp:real->real.
         (!k:num.
            k < n
            ==> ts k + &1 <= ts (k + 1)) /\
         continuous_on_ray f (ts 0) /\
         (!t:real.
            ts 0 < t /\
            (!i:num.
               1 <= i /\ i <= n
               ==> ~(t = ts i))
            ==> (f diffl fp t) t /\
                (?d:real. (fp diffl d) t)) /\
         f (ts 0) = &1 / &2 /\
         (!k:num.
            k <= n
            ==> right_limit fp (ts k) (&0)) /\
         (!k:num.
            k < n
            ==> !t:real.
                  ts k < t /\ t < ts (k + 1)
                  ==> (fp diffl &(k + 1)) t) /\
         (!t:real.
            ts n < t
            ==> (fp diffl &(n + 1)) t) /\
         f (ts 0 + tau) = &2023 in
   attainable (&29) /\
   (!tau:real. attainable tau ==> &29 <= tau)`;;
