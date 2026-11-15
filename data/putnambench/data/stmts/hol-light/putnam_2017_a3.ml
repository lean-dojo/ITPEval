(*
  Statement-only formalization of PutnamBench corpus artifact putnam_2017_a3
  (putnambench__hol-light__putnam_2017_a3): strict growth and divergence to
  positive infinity of an integral sequence formed from two distinct positive
  continuous functions with equal integrals. This file contains no proof.
*)

let analysis_output = open_out "/dev/null";;
let analysis_formatter = Format.formatter_of_out_channel analysis_output;;
let analysis_loaded =
  Toploop.use_file analysis_formatter "Library/transc.ml";;
Format.pp_print_flush analysis_formatter ();;
close_out analysis_output;;
if not analysis_loaded then failwith "failed to load Library/transc.ml";;

let statement =
  `let continuous_on_interval =
     \(a:real) (b:real) (h:real->real).
       !x:real.
         a <= x /\ x <= b
         ==> !e:real.
               &0 < e
               ==> ?d:real.
                     &0 < d /\
                     !y:real.
                       a <= y /\ y <= b /\ abs (y - x) < d
                       ==> abs (h y - h x) < e in
   let tends_to_posinfinity =
     \(u:num->real).
       !M:real.
         ?N:num.
           !n:num. N <= n ==> M <= u n in
   !a b:real. !f g:real->real. !seq:num->real.
     a < b /\
     continuous_on_interval a b f /\
     continuous_on_interval a b g /\
     (!x:real.
        a <= x /\ x <= b
        ==> &0 < f x /\ &0 < g x) /\
     integral(a,b) f = integral(a,b) g /\
     (?x:real. a <= x /\ x <= b /\ ~(f x = g x)) /\
     (!n:num.
        0 < n
        ==> seq n =
            integral(a,b)
              (\x:real. (f x) pow (n + 1) / (g x) pow n))
     ==>
     (!n:num. 0 < n ==> seq n < seq (n + 1)) /\
     tends_to_posinfinity seq`;;
