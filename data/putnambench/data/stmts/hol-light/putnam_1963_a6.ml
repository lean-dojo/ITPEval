(*
  Statement-only formalization of PutnamBench artifact putnam_1963_a6:
  an ellipse chord-midpoint configuration in which two induced intersection
  points have the original chord midpoint as their midpoint. This file
  contains no proof.
*)

let statement =
  `let edist =
     \(x:real#real) (y:real#real).
       sqrt ((FST x - FST y) pow 2 + (SND x - SND y) pow 2) in
   let midpoint =
     \(x:real#real) (y:real#real).
       ((FST x + FST y) / &2, (SND x + SND y) / &2) in
   let segment =
     \(a:real#real) (b:real#real) (x:real#real).
       ?t:real.
         &0 <= t /\ t <= &1 /\
         FST x = (&1 - t) * FST a + t * FST b /\
         SND x = (&1 - t) * SND a + t * SND b in
   let collinear3 =
     \(a:real#real) (b:real#real) (c:real#real).
       (FST b - FST a) * (SND c - SND a) =
       (SND b - SND a) * (FST c - FST a) in
   !F1 F2 U V A B C D P Q:real#real.
   !r:real. !E:(real#real)->bool. !M:real#real.
     E = {H | edist F1 H + edist F2 H = r} /\
     M = midpoint U V /\
     r > edist F1 F2 /\
     U IN E /\ V IN E /\ ~(U = V) /\
     A IN E /\ B IN E /\ ~(A = B) /\
     C IN E /\ D IN E /\ ~(C = D) /\
     ~(A = C) /\ ~(B = D) /\
     ~(segment A B = segment U V) /\
     ~(segment C D = segment U V) /\
     ~(segment A B = segment C D) /\
     segment A B M /\ segment C D M /\
     collinear3 P A C /\ collinear3 P U V /\
     collinear3 Q B D /\ collinear3 Q U V
     ==> M = midpoint P Q`;;
