(*
  Statement-only formalization of PutnamBench artifact putnam_1966_b5:
  a finite set of at least three real-plane points, no three collinear, is
  the vertex set of a simple closed polygon. This file contains no proof.
*)

let statement =
  `let collinear_set =
     \s:(real#real)->bool.
       ?p d:real#real.
         !x:real#real.
           x IN s
           ==> ?c:real.
                 x = (FST p + c * FST d,
                      SND p + c * SND d) in
   let on_segment =
     \(a:real#real) (b:real#real) (x:real#real).
       ?t:real.
         &0 <= t /\ t <= &1 /\
         FST x = (&1 - t) * FST a + t * FST b /\
         SND x = (&1 - t) * SND a + t * SND b in
   !S:(real#real)->bool.
     FINITE S /\
     3 <= CARD S /\
     (!s:(real#real)->bool.
        s SUBSET S /\ s HAS_SIZE 3
        ==> ~(collinear_set s))
     ==> ?L:num->real#real.
           (!p:real#real.
              p IN S
              ==> ?!i:num. i < CARD S /\ p = L i) /\
           (!i j:num.
              i < CARD S /\ j < CARD S /\ ~(i = j)
              ==> !x:real#real.
                    on_segment
                      (L i) (L ((i + 1) MOD CARD S)) x /\
                    on_segment
                      (L j) (L ((j + 1) MOD CARD S)) x
                    ==> x = L i \/
                        x = L ((i + 1) MOD CARD S) \/
                        x = L j \/
                        x = L ((j + 1) MOD CARD S))`;;
