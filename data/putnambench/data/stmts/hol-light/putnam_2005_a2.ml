(*
  Statement-only formalization of PutnamBench corpus artifact putnam_2005_a2:
  the number of rook tours of an n-by-3 integer grid that start at (1,1) and
  end at (n,1). This file contains no proof.
*)

let statement =
  `!n:num.
     0 < n
     ==>
     let grid =
       {p:int#int |
          (&1:int) <= FST p /\ FST p <= &n /\
          (&1:int) <= SND p /\ SND p <= &3} in
     let unit =
       \p q:int#int.
         (FST p = FST q /\ abs (SND q - SND p) = &1) \/
         (SND p = SND q /\ abs (FST q - FST p) = &1) in
     let rooktour =
       \p:num->int#int.
         (!P:int#int.
            P IN grid
            ==> ?!i:num. i IN (1..3 * n) /\ p i = P) /\
         (!i:num.
            i IN (1..3 * n - 1)
            ==> unit (p i) (p (i + 1))) /\
         p 0 = ((&0:int),(&0:int)) /\
         (!i:num. 3 * n < i ==> p i = ((&0:int),(&0:int))) in
     CARD
       {p:num->int#int |
          rooktour p /\
          p 1 = ((&1:int),(&1:int)) /\
          p (3 * n) = (&n,(&1:int))} =
     (if n = 1 then 0 else 2 EXP (n - 2))`;;
