(*
  Statement-only formalization of PutnamBench artifact putnam_1964_b4:
  the number of regions cut from the unit sphere by distinct great circles
  in general position, described by their nonzero dot-product sign patterns.
  This file contains no proof.
*)

let statement =
  `!n:num.
   !C:num->(real#(real#real))->bool.
   !v:num->real#(real#real).
   !IsRegion:((real#(real#real))->bool)->bool.
     let dot =
       \p:real#(real#real).
       \q:real#(real#real).
         FST p * FST q +
         FST (SND p) * FST (SND q) +
         SND (SND p) * SND (SND q) in
     let sphere = {x:real#(real#real) | dot x x = &1} in
     0 < n /\
     (!i:num.
        i < n
        ==> C i = sphere INTER {x | dot (v i) x = &0}) /\
     (!i:num. i < n ==> ~(v i = (&0,(&0,&0)))) /\
     (!i j:num.
        i < n /\ j < n /\ C i = C j
        ==> i = j) /\
     (!x y:real#(real#real).
        x IN sphere /\ y IN sphere
        ==> CARD {i:num |
                    i < n /\ x IN C i /\ y IN C i} <= 2) /\
     (!R:(real#(real#real))->bool.
        IsRegion R <=>
        ~(R = {}) /\
        ?sign:num->bool.
          R =
          sphere INTER
          {x | !i:num.
                 i < n
                 ==> (if sign i
                      then &0 < dot (v i) x
                      else dot (v i) x < &0)})
     ==> CARD {R:(real#(real#real))->bool | IsRegion R} =
         n EXP 2 - n + 2`;;
