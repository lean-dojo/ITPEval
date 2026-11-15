(*
  Statement-only formalization of PutnamBench corpus artifact putnam_2006_b1:
  uniqueness of an equilateral three-point subset of the cubic curve
  x^3 + 3xy + y^3 = 1, whose triangle has area 3 sqrt(3) / 2. This file
  contains no proof.
*)

let statement =
  `let edist =
     \(P:real#real) (Q:real#real).
       sqrt ((FST P - FST Q) pow 2 + (SND P - SND Q) pow 2) in
   let curve =
     {P:real#real |
        FST P pow 3 + &3 * FST P * SND P + SND P pow 3 = &1} in
   let equilateral =
     \(S:(real#real)->bool).
       S HAS_SIZE 3 /\
       ?d:real.
         !P Q:real#real.
           P IN S /\ Q IN S /\ ~(P = Q)
           ==> edist P Q = d in
   let triangle_area =
     \(A:real#real) (B:real#real) (C:real#real).
       abs ((FST B - FST A) * (SND C - SND A) -
            (SND B - SND A) * (FST C - FST A)) / &2 in
   let putnam_2006_b1_solution = &3 * sqrt (&3) / &2 in
   (?!S:(real#real)->bool.
       S SUBSET curve /\ equilateral S) /\
   (?S:(real#real)->bool. ?A B C:real#real.
      S SUBSET curve /\
      equilateral S /\
      S = {A,B,C} /\
      triangle_area A B C = putnam_2006_b1_solution)`;;
