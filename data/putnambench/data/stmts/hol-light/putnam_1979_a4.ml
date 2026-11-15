(*
  Statement-only formalization of PutnamBench artifact putnam_1979_a4:
  equal finite red and blue point sets in the real plane, with no three
  points collinear, admit disjoint closed segments pairing opposite colors.
  This file contains no proof.
*)

let statement =
  `let collinear3 =
     \(p:real#real) (q:real#real) (r:real#real).
       (FST q - FST p) * (SND r - SND p) =
       (SND q - SND p) * (FST r - FST p) in
   let on_segment =
     \(p:real#real) (q:real#real) (x:real#real).
       ?t:real.
         &0 <= t /\ t <= &1 /\
         FST x = t * FST p + (&1 - t) * FST q /\
         SND x = t * SND p + (&1 - t) * SND q in
   !R B:(real#real)->bool.
     FINITE R /\
     FINITE B /\
     CARD R = CARD B /\
     DISJOINT R B /\
     (!p q r:real#real.
        p IN R UNION B /\
        q IN R UNION B /\
        r IN R UNION B /\
        ~(q = p) /\ ~(r = p) /\ ~(r = q)
        ==> ~(collinear3 p q r))
     ==> ?v:((real#real)#(real#real))->bool.
           FINITE v /\
           CARD v = CARD R /\
           (!l.
              l IN v
              ==> FST l IN R /\ SND l IN B) /\
           (!l m.
              l IN v /\ m IN v /\ ~(l = m)
              ==> ~(FST l = FST m) /\
                  ~(SND l = SND m) /\
                  ~(?x:real#real.
                      on_segment (FST l) (SND l) x /\
                      on_segment (FST m) (SND m) x))`;;
