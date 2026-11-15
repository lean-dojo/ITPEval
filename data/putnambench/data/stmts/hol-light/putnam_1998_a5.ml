(*
  Statement-only formalization of PutnamBench corpus artifact putnam_1998_a5:
  a finite family of positive-radius open discs covering a planar set has a
  pairwise disjoint subfamily whose radius-tripled discs still cover the set.
  This file contains no proof.
*)

let statement =
  `!k:num. !c:num->real^2. !r:num->real. !E:real^2->bool.
     let disc =
       \(p:real^2) (s:real).
         {x:real^2 |
            &0 < s /\
            (x$1 - p$1) pow 2 + (x$2 - p$2) pow 2 < s pow 2} in
     ((!i:num. i < k ==> &0 < r i) /\
      (!x:real^2.
         x IN E
         ==> ?i:num. i < k /\ x IN disc (c i) (r i)))
     ==>
     ?n:num. ?t:num->num.
       n <= k /\
       (!i:num. i < n ==> t i < k) /\
       (!i j:num.
          i < n /\ j < n /\ ~(i = j)
          ==> disc (c (t i)) (r (t i)) INTER
              disc (c (t j)) (r (t j)) = {}) /\
       (!x:real^2.
          x IN E
          ==> ?i:num.
                i < n /\ x IN disc (c (t i)) (&3 * r (t i)))`;;
