(*
  Statement-only formalization of PutnamBench corpus artifact putnam_2021_a1
  (putnambench__hol-light__putnam_2021_a1): the minimum number of length-five
  hops between integer lattice points from (0,0) to (2021,2021) is 578. This
  file contains no proof.
*)

let statement =
  `let valid_path =
     \p:(int#int)list.
       ~(p = []) /\
       HD p = ((&0:int),(&0:int)) /\
       LAST p = ((&2021:int),(&2021:int)) /\
       (!i:num.
          i + 1 < LENGTH p
          ==>
          (FST (EL (i + 1) p) - FST (EL i p)) pow 2 +
          (SND (EL (i + 1) p) - SND (EL i p)) pow 2 = (&25:int)) in
   (?p:(int#int)list. valid_path p /\ LENGTH p = 578 + 1) /\
   (!d:num.
      d < 578
      ==> ~(?p:(int#int)list. valid_path p /\ LENGTH p = d + 1))`;;
