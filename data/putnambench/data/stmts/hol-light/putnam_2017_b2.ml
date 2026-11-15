(*
  Statement-only formalization of PutnamBench corpus artifact putnam_2017_b2
  (putnambench__hol-light__putnam_2017_b2): the least positive starting
  integer whose sum of 2017 consecutive positive integers has no
  representation by any other length greater than one. This file contains no
  proof.
*)

let statement =
  `let consecutive_sum =
     \(a:int) (k:num).
       isum (0..k - 1) (\i:num. a + &i) in
   let valid =
     \a:int.
       &0 < a /\
       (!b:int. !k:num.
          &0 < b /\
          1 < k /\
          consecutive_sum a 2017 = consecutive_sum b k
          ==> k = 2017) in
   valid (&16:int) /\
   (!a:int. valid a ==> (&16:int) <= a)`;;
