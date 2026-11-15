(*
  Statement-only formalization of PutnamBench corpus artifact putnam_1991_a4:
  the existence of a sequence of closed discs in the real plane with no
  finite cluster point among their centers, finite total area, and an
  intersection with every line. This file contains no proof.
*)

let vectors_output = open_out "/dev/null";;
let vectors_formatter = Format.formatter_of_out_channel vectors_output;;
let previous_file_loader = !Hol_loader.file_loader;;
Hol_loader.file_loader :=
  (fun path -> Toploop.use_file vectors_formatter path);;
let vectors_loaded =
  Toploop.use_file vectors_formatter "Multivariate/vectors.ml";;
Hol_loader.file_loader := previous_file_loader;;
Format.pp_print_flush vectors_formatter ();;
close_out vectors_output;;
if not vectors_loaded then failwith "failed to load Multivariate/vectors.ml";;

let statement =
  `?c:num->real^2 r:num->real.
     (!i:num. &0 <= r i) /\
     ~(?p:real^2.
         !e:real.
           &0 < e
           ==> ?f:num->num.
                 (!i j:num. i < j ==> f i < f j) /\
                 (!i:num. dist(c(f i),p) < e)) /\
     summable (\i. (r i) pow 2) /\
     (!v w:real^2.
        ~(w = vec 0)
        ==> ?i:num. ?t:real. dist(v + t % w,c i) <= r i)`;;
