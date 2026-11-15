(*
  Statement-only formalization of PutnamBench artifact putnam_1967_a6:
  the maximum number of coordinatewise sign patterns of nonzero real
  solutions to two homogeneous linear equations in four variables is 8.
  This file contains no proof.
*)

let statement =
  `let dot4 =
     \(a:real#(real#(real#real))) (x:real#(real#(real#real))).
       FST a * FST x +
       FST (SND a) * FST (SND x) +
       FST (SND (SND a)) * FST (SND (SND x)) +
       SND (SND (SND a)) * SND (SND (SND x)) in
   let nonzero4 =
     \(x:real#(real#(real#real))).
       ~(FST x = &0) /\
       ~(FST (SND x) = &0) /\
       ~(FST (SND (SND x)) = &0) /\
       ~(SND (SND (SND x)) = &0) in
   let sign4 =
     \(x:real#(real#(real#real))).
       (real_sgn (FST x),
        (real_sgn (FST (SND x)),
         (real_sgn (FST (SND (SND x))),
          real_sgn (SND (SND (SND x)))))) in
   let admissible =
     \(a:real#(real#(real#real))) (b:real#(real#(real#real))).
       ~(FST a * FST (SND b) - FST (SND a) * FST b = &0) in
   let patterns =
     \(a:real#(real#(real#real))) (b:real#(real#(real#real))).
       {s:real#(real#(real#real)) |
          ?x:real#(real#(real#real)).
            nonzero4 x /\
            dot4 a x = &0 /\
            dot4 b x = &0 /\
            s = sign4 x} in
   (?a b:real#(real#(real#real)).
      admissible a b /\ CARD (patterns a b) = 8) /\
   (!a b:real#(real#(real#real)).
      admissible a b ==> CARD (patterns a b) <= 8)`;;
