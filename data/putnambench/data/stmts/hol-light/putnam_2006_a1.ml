(*
  Statement-only formalization of PutnamBench corpus artifact putnam_2006_a1:
  the Lebesgue volume of the region in real three-space defined by
  (x^2 + y^2 + z^2 + 8)^2 <= 36(x^2 + y^2) is 6 pi^2.
  This file contains no proof.
*)

needs "Library/transc.ml";;

let statement =
  `let cover_bound =
     \(s:(real#(real#real))->bool) (B:real).
       &0 <= B /\
       ?xl xu yl yu zl zu:num->real.
         (!k:num.
            xl k <= xu k /\ yl k <= yu k /\ zl k <= zu k) /\
         (!p:real#(real#real).
            p IN s
            ==> ?k:num.
                  xl k < FST p /\ FST p < xu k /\
                  yl k < FST (SND p) /\ FST (SND p) < yu k /\
                  zl k < SND (SND p) /\ SND (SND p) < zu k) /\
         (!N:num.
            sum (0..N)
              (\k:num.
                 (xu k - xl k) *
                 (yu k - yl k) *
                 (zu k - zl k)) <= B) in
   let lebesgue_outer_measure =
     \(s:(real#(real#real))->bool).
       inf {B:real | cover_bound s B} in
   lebesgue_outer_measure
     {p:real#(real#real) |
        (FST p pow 2 +
         FST (SND p) pow 2 +
         SND (SND p) pow 2 +
         &8) pow 2
        <= &36 * (FST p pow 2 + FST (SND p) pow 2)} =
   &6 * pi pow 2`;;
