(*
  Statement-only formalization of PutnamBench artifact putnam_1987_a1:
  equality of the intersection of two rational plane curves with the
  intersection of two cubic plane curves. This file contains no proof.
*)

let statement =
  `!A B C D:(real#real)->bool.
     A =
       {p:real#real |
          ~((FST p) pow 2 + (SND p) pow 2 = &0) /\
          (FST p) pow 2 - (SND p) pow 2 =
          FST p / ((FST p) pow 2 + (SND p) pow 2)} /\
     B =
       {p:real#real |
          ~((FST p) pow 2 + (SND p) pow 2 = &0) /\
          &2 * FST p * SND p +
          SND p / ((FST p) pow 2 + (SND p) pow 2) = &3} /\
     C =
       {p:real#real |
          (FST p) pow 3 - &3 * FST p * (SND p) pow 2 +
          &3 * SND p = &1} /\
     D =
       {p:real#real |
          &3 * (FST p) pow 2 * SND p - &3 * FST p -
          (SND p) pow 3 = &0}
     ==> A INTER B = C INTER D`;;
