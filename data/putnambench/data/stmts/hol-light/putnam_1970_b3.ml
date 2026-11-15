(*
  Statement-only formalization of PutnamBench artifact putnam_1970_b3:
  closedness of the y-coordinate projection of a closed subset of the real
  plane whose x-coordinates lie in a bounded open interval. This file
  contains no proof.
*)

let statement =
  `let closed_plane =
     \S:(real#real)->bool.
       !p:real#real.
         ~(p IN S)
         ==> ?e:real.
               &0 < e /\
               !q:real#real.
                 (FST q - FST p) pow 2 +
                 (SND q - SND p) pow 2 < e pow 2
                 ==> ~(q IN S) in
   let closed_real =
     \A:real->bool.
       !x:real.
         ~(x IN A)
         ==> ?e:real.
               &0 < e /\
               !y:real.
                 (y - x) pow 2 < e pow 2
                 ==> ~(y IN A) in
   !S:(real#real)->bool. !a b:real.
     a < b /\
     (!s:real#real. s IN S ==> a < FST s /\ FST s < b) /\
     closed_plane S
     ==> closed_real {y:real | ?x:real. (x,y) IN S}`;;
