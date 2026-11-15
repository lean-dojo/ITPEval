(*
  Statement-only formalization of PutnamBench corpus artifact putnam_2008_b3:
  the largest radius of a circle contained in a four-dimensional hypercube of
  side length one is sqrt 2 / 2. This file contains no proof.
*)

let statement =
  `let zero4 =
     (&0,(&0,(&0,&0))) in
   let add4 =
     \(x:real#(real#(real#real))) (y:real#(real#(real#real))).
       (FST x + FST y,
        (FST (SND x) + FST (SND y),
         (FST (SND (SND x)) + FST (SND (SND y)),
          SND (SND (SND x)) + SND (SND (SND y))))) in
   let smul4 =
     \(a:real) (x:real#(real#(real#real))).
       (a * FST x,
        (a * FST (SND x),
         (a * FST (SND (SND x)),
          a * SND (SND (SND x))))) in
   let norm4 =
     \(x:real#(real#(real#real))).
       sqrt
         ((FST x) pow 2 +
          (FST (SND x)) pow 2 +
          (FST (SND (SND x))) pow 2 +
          (SND (SND (SND x))) pow 2) in
   let hypercube =
     {x:real#(real#(real#real)) |
        abs (FST x) <= &1 / &2 /\
        abs (FST (SND x)) <= &1 / &2 /\
        abs (FST (SND (SND x))) <= &1 / &2 /\
        abs (SND (SND (SND x))) <= &1 / &2} in
   let contains =
     \r:real.
       ?center p q:real#(real#(real#real)).
         (!a b:real.
            add4 (smul4 a p) (smul4 b q) = zero4
            ==> a = &0 /\ b = &0) /\
         (!s t:real.
            norm4 (add4 (smul4 s p) (smul4 t q)) = r
            ==> add4 center (add4 (smul4 s p) (smul4 t q))
                IN hypercube) in
   contains (sqrt(&2) / &2) /\
   (!r:real.
      contains r
      ==> r <= sqrt(&2) / &2)`;;
