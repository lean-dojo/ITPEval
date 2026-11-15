(*
  Statement-only formalization of PutnamBench corpus artifact putnam_1996_a1:
  the minimum positive product satisfying the stated packing inequalities for
  every positive pair whose squared values sum to one. This file contains no
  proof.
*)

let statement =
  `let packable =
     \(n1:real) (n2:real) (a1:real) (a2:real).
       n1 + n2 <= real_max a1 a2 /\
       real_max n1 n2 <= real_min a1 a2 in
   let aprop =
     \(a:real).
       !n1 n2:real.
         &0 < n1 /\ &0 < n2 /\ n1 pow 2 + n2 pow 2 = &1
         ==> ?a1 a2:real.
               &0 < a1 /\ &0 < a2 /\ a1 * a2 = a /\
               packable n1 n2 a1 a2 in
   let solution = (&1 + sqrt (&2)) / &2 in
   aprop solution /\
   (!a:real. aprop a ==> solution <= a)`;;
