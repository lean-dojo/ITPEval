(*
  Statement-only formalization of PutnamBench artifact putnam_1973_a6:
  impossibility of seven distinct slope-intercept lines having at least six
  points incident to exactly three lines and at least four points incident to
  exactly two lines. This file contains no proof.
*)

let statement =
  `let nint =
     \n (lines:num->real#real).
       CARD
         {p:real#real |
            ?!S:num->bool.
              S SUBSET (0..6) /\
              CARD S = n /\
              (!i. i IN S
                   ==> SND p =
                       FST (lines i) * FST p + SND (lines i))} in
   ~(?lines:num->real#real.
       (!i j.
          i IN (0..6) /\ j IN (0..6) /\ ~(i = j)
          ==> ~(lines i = lines j)) /\
       6 <= nint 3 lines /\
       4 <= nint 2 lines)`;;
