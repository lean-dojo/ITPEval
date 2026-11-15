(*
  Statement-only formalization of PutnamBench corpus artifact putnam_2004_b6:
  unbounded gaps between the increasing positive differences of a nonempty
  set of positive integers force its counting function to have density zero
  at positive infinity. This file contains no proof.
*)

let statement =
  `let tends_at_posinfinity =
     \(f:real->real) (l:real).
       !e:real.
         &0 < e
         ==> ?M:real.
               !x:real. M <= x ==> abs (f x - l) < e in
   !A B:num->bool.
   !N:real->num.
   !b:num->num.
     ~(A = {}) /\
     (!a:num. a IN A ==> 0 < a) /\
     (!x:real. N x = CARD {a:num | a IN A /\ &a <= x}) /\
     B =
       {d:num |
          0 < d /\
          ?a a':num.
            a IN A /\ a' IN A /\ d = a - a'} /\
     IMAGE b (:num) = B /\
     (!i:num. b i < b (i + 1))
     ==>
     ((!r:num. ?i:num. r <= b (i + 1) - b i)
      ==>
      tends_at_posinfinity (\x:real. &(N x) / x) (&0))`;;
