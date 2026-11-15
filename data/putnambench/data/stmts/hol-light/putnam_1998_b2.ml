(*
  Statement-only formalization of PutnamBench corpus artifact putnam_1998_b2:
  the minimum perimeter of a triangle with vertices at (a,b), on the x-axis,
  and on the line y = x. This file contains no proof.
*)

let statement =
  `let edge_ac =
     \a b c:real.
       sqrt ((a - c) pow 2 + (b - &0) pow 2) in
   let edge_cx =
     \c x:real.
       sqrt ((c - x) pow 2 + (&0 - x) pow 2) in
   let edge_ax =
     \a b x:real.
       sqrt ((a - x) pow 2 + (b - x) pow 2) in
   !a b:real.
     &0 < b /\ b < a
     ==>
     inf
       {p:real |
          ?c x:real.
            p = edge_ac a b c + edge_cx c x + edge_ax a b x /\
            edge_ac a b c + edge_cx c x > edge_ax a b x /\
            edge_ac a b c + edge_ax a b x > edge_cx c x /\
            edge_cx c x + edge_ax a b x > edge_ac a b c} =
     sqrt (&2 * a pow 2 + &2 * b pow 2)`;;
