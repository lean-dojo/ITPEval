(*
  Statement-only formalization of PutnamBench artifact putnam_1967_a3:
  the least positive integer leading coefficient of a quadratic with integer
  coefficients and two distinct zeros in the open unit interval is 5. This
  file contains no proof.
*)

let statement =
  `let admissible =
     \(a:int) (b:int) (c:int).
       (&0:int) < a /\
       ?z1 z2:real.
         &0 < z1 /\ z1 < &1 /\
         &0 < z2 /\ z2 < &1 /\
         ~(z1 = z2) /\
         real_of_int a * z1 pow 2 - real_of_int b * z1 + real_of_int c = &0 /\
         real_of_int a * z2 pow 2 - real_of_int b * z2 + real_of_int c = &0 in
   (?b c:int. admissible (&5:int) b c) /\
   (!a b c:int. admissible a b c ==> (&5:int) <= a)`;;
