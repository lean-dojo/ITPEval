(*
  Statement-only formalization of PutnamBench artifact putnam_1974_b1:
  five points on the unit circle maximize the sum of their ten pairwise
  distances exactly when they admit a cyclic ordering with one common positive
  consecutive distance. This file contains no proof.
*)

let statement =
  `let edist =
     \(x:real#real) (y:real#real).
       sqrt ((FST x - FST y) pow 2 + (SND x - SND y) pow 2) in
   let on_unit_circle =
     \(p:num->real#real).
       !i. i < 5 ==> edist (p i) (&0,&0) = &1 in
   let distance_sum =
     \(p:num->real#real).
       sum (0..4)
         (\i. sum ((i + 1)..4) (\j. edist (p i) (p j))) in
   let putnam_1974_b1_solution =
     \(p:num->real#real).
       (!i j:num.
          i < 5 /\ j < 5 /\ p i = p j ==> i = j) /\
       ?B:real. ?ordering:num->num.
         &0 < B /\
         (!i. i < 5 ==> ordering i < 5) /\
         (!i j.
            i < 5 /\ j < 5 /\ ordering i = ordering j ==> i = j) /\
         (!i. i < 5
              ==> edist (p (ordering i))
                        (p (ordering ((i + 1) MOD 5))) = B) in
   !p:num->real#real.
     on_unit_circle p
     ==> (distance_sum p =
          sup (IMAGE distance_sum
                     {q:num->real#real | on_unit_circle q}) <=>
          putnam_1974_b1_solution p)`;;
