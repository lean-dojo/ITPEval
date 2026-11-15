(*
  Statement-only formalization of PutnamBench corpus artifact putnam_1998_a2:
  the sum of the areas below and to the left of a first-quadrant unit-circle
  arc depends only on its angular arc length. This file contains no proof.
*)

let transc_output = open_out "/dev/null";;
let transc_formatter = Format.formatter_of_out_channel transc_output;;
let previous_file_loader = !Hol_loader.file_loader;;
Hol_loader.file_loader :=
  (fun path -> Toploop.use_file transc_formatter path);;
let transc_loaded =
  Toploop.use_file transc_formatter "Library/transc.ml";;
Hol_loader.file_loader := previous_file_loader;;
Format.pp_print_flush transc_formatter ();;
close_out transc_output;;
if not transc_loaded then failwith "failed to load Library/transc.ml";;

let statement =
  `let cover_bound =
     \(S:real^2->bool) (M:real).
       &0 <= M /\
       ?xl xu yl yu:num->real.
         (!k:num. xl k <= xu k /\ yl k <= yu k) /\
         (!p:real^2.
            p IN S
            ==> ?k:num.
                  xl k < p$1 /\ p$1 < xu k /\
                  yl k < p$2 /\ p$2 < yu k) /\
         (!N:num.
            sum (0..N)
              (\k:num. (xu k - xl k) * (yu k - yl k)) <= M) in
   let outer_area =
     \(S:real^2->bool).
       inf {M:real | cover_bound S M} in
   let quadrant =
     \P:real^2.
       P$1 > &0 /\ P$2 > &0 /\
       (P$1) pow 2 + (P$2) pow 2 = &1 in
   let isarc =
     \P Q:real^2.
       quadrant P /\ quadrant Q /\ P$1 > Q$1 in
   let arc =
     \P Q:real^2.
       {R:real^2 | quadrant R /\ P$1 > R$1 /\ R$1 > Q$1} in
   let A =
     \P Q:real^2.
       outer_area
         {S:real^2 |
            ?R:real^2.
              R IN arc P Q /\
              R$1 = S$1 /\ R$2 > S$2 /\ S$2 > &0} in
   let B =
     \P Q:real^2.
       outer_area
         {S:real^2 |
            ?R:real^2.
              R IN arc P Q /\
              R$2 = S$2 /\ R$1 > S$1 /\ S$1 > &0} in
   ?f:real->real.
     !P Q:real^2.
       isarc P Q
       ==> A P Q + B P Q =
           f (atn (Q$2 / Q$1) - atn (P$2 / P$1))`;;
