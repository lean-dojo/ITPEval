(*
  Statement-only formalization of PutnamBench corpus artifact putnam_2011_a1:
  exactly 10053 integer points in the 2011 by 2011 coordinate box cannot be
  endpoints of growing lattice spirals with positive strictly increasing
  segment lengths. This file contains no proof.
*)

let statement =
  `let is_spiral =
     \P:(int#int)list.
       3 <= LENGTH P /\
       EL 0 P = ((&0:int),(&0:int)) /\
       ?l:num->num.
         (!i:num. i + 1 < LENGTH P ==> 0 < l i) /\
         (!i j:num.
            i < j /\ j + 1 < LENGTH P
            ==> l i < l j) /\
         (!i:num.
            i + 1 < LENGTH P
            ==>
            (i MOD 4 = 0
             ==> FST (EL i P) + (&(l i):int) = FST (EL (i + 1) P) /\
                 SND (EL i P) = SND (EL (i + 1) P)) /\
            (i MOD 4 = 1
             ==> FST (EL i P) = FST (EL (i + 1) P) /\
                 SND (EL i P) + (&(l i):int) = SND (EL (i + 1) P)) /\
            (i MOD 4 = 2
             ==> FST (EL i P) - (&(l i):int) = FST (EL (i + 1) P) /\
                 SND (EL i P) = SND (EL (i + 1) P)) /\
            (i MOD 4 = 3
             ==> FST (EL i P) = FST (EL (i + 1) P) /\
                 SND (EL i P) - (&(l i):int) = SND (EL (i + 1) P))) in
   CARD
     {p:int#int |
        (&0:int) <= FST p /\ FST p <= &2011 /\
        (&0:int) <= SND p /\ SND p <= &2011 /\
        ~(?P:(int#int)list. is_spiral P /\ LAST P = p)} =
   10053`;;
