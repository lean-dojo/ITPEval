(*
  Statement-only formalization of PutnamBench corpus artifact putnam_2019_b6
  (putnambench__hol-light__putnam_2019_b6): existence, in every positive
  dimension, of an independent perfect dominating set in the integer lattice.
  This file contains no proof.
*)

let statement =
  `let lattice_point =
     \n:num. \p:num->int.
       !i:num. n <= i ==> p i = &0 in
   let neighbors =
     \n:num. \p q:num->int.
       lattice_point n p /\
       lattice_point n q /\
       ?i:num.
         i < n /\
         abs (p i - q i) = &1 /\
         (!j:num. j < n /\ ~(j = i) ==> p j = q j) in
   let solution = {n:num | 1 <= n} in
   !n:num.
     (1 <= n /\
      ?S:(num->int)->bool.
        S SUBSET {p:num->int | lattice_point n p} /\
        (!p:num->int.
           p IN S
           ==> !q:num->int. neighbors n p q ==> ~(q IN S)) /\
        (!p:num->int.
           lattice_point n p /\ ~(p IN S)
           ==> ?!q:num->int. q IN S /\ neighbors n p q))
     <=> n IN solution`;;
