(*
  Statement-only formalization of PutnamBench corpus artifact putnam_1990_a4:
  the least number of paper punches whose irrational-distance loci cover the
  Euclidean plane is three. This file contains no proof.
*)

let statement =
  `let edist =
     \(P:real#real) (Q:real#real).
       sqrt ((FST P - FST Q) pow 2 + (SND P - SND Q) pow 2) in
   let is_rational =
     \x:real.
       ?p q:int.
         ~(q = (&0:int)) /\
         x = real_of_int p / real_of_int q in
   let feasible =
     \n:num.
       ?S:(real#real)->bool.
         S HAS_SIZE n /\
         (!Q:real#real.
            ?P:real#real.
              P IN S /\ ~is_rational (edist P Q)) in
   let putnam_1990_a4_solution = 3 in
   feasible putnam_1990_a4_solution /\
   (!n:num. feasible n ==> putnam_1990_a4_solution <= n)`;;
