(*
  Statement-only formalization of PutnamBench artifact putnam_1964_b6:
  impossibility of partitioning the closed unit disk in the real plane into
  two disjoint congruent sets. This file contains no proof.
*)

let statement =
  `let disk =
     {p:real#real |
        (FST p) pow 2 + (SND p) pow 2 <= &1} in
   let congruent =
     \(A:(real#real)->bool) (B:(real#real)->bool).
       ?f:(real#real)->(real#real).
         B = IMAGE f A /\
         !v w:real#real.
           (FST v - FST w) pow 2 + (SND v - SND w) pow 2 =
           (FST (f v) - FST (f w)) pow 2 +
           (SND (f v) - SND (f w)) pow 2 in
   ~(?A B:(real#real)->bool.
       congruent A B /\
       A INTER B = {} /\
       A UNION B = disk)`;;
