(*
  Statement-only formalization of PutnamBench corpus artifact putnam_2024_a5
  (putnambench__hol-light__putnam_2024_a5): the radius-axis displacement
  minimizing the probability that the affine line through two independent
  uniform points on a radius-9 circle meets a unit circle. The unique
  minimizing displacement is 0. This file contains no proof.
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
     \(s:(real#real)->bool) (B:real).
       &0 <= B /\
       ?xl xu yl yu:num->real.
         (!k:num. xl k <= xu k /\ yl k <= yu k) /\
         (!p:real#real.
            p IN s
            ==> ?k:num.
                  xl k < FST p /\ FST p < xu k /\
                  yl k < SND p /\ SND p < yu k) /\
         (!N:num.
            sum (0..N)
              (\k:num. (xu k - xl k) * (yu k - yl k)) <= B) in
   let planar_outer_measure =
     \(s:(real#real)->bool).
       inf {B:real | cover_bound s B} in
   let line_meets_circle =
     \(r:real) (P:real#real) (Q:real#real).
       ?u:real.
         (FST P + u * (FST Q - FST P) - r) pow 2 +
         (SND P + u * (SND Q - SND P)) pow 2 = &1 in
   !IsIntersecting:real->(real#real)->(real#real)->bool
    ProbIntersect:real->real.
      (!r:real P:real#real Q:real#real.
         (IsIntersecting r P Q <=> line_meets_circle r P Q)) /\
      (!r:real.
         ProbIntersect r =
         planar_outer_measure
           {st:real#real |
              &0 <= FST st /\ FST st <= &1 /\
              &0 <= SND st /\ SND st <= &1 /\
              IsIntersecting r
                (&9 * cos (&2 * pi * FST st),
                 &9 * sin (&2 * pi * FST st))
                (&9 * cos (&2 * pi * SND st),
                 &9 * sin (&2 * pi * SND st))})
      ==>
      {r:real |
         &0 <= r /\ r <= &8 /\
         ProbIntersect r =
         inf (IMAGE ProbIntersect {x:real | &0 <= x /\ x <= &8})} =
      {r:real | r = &0}`;;
