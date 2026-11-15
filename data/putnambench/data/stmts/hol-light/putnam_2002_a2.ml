(*
  Statement-only formalization of PutnamBench corpus artifact putnam_2002_a2:
  among any five points on the unit sphere in real three-space, at least four
  lie in a closed hemisphere. This file contains no proof.
*)

let statement =
  `let dot =
     \p:real#(real#real).
     \q:real#(real#real).
       FST p * FST q +
       FST (SND p) * FST (SND q) +
       SND (SND p) * SND (SND q) in
   let zero = (&0,(&0,&0)) in
   !S:(real#(real#real))->bool.
     FINITE S /\
     S SUBSET {P:real#(real#real) | dot P P = &1} /\
     CARD S = 5
     ==> ?V:real#(real#real).
           ~(V = zero) /\
           4 <=
           CARD
             (S INTER
              {P:real#(real#real) | dot P V >= &0})`;;
