(*
  Statement-only formalization of Thousand Theorems corpus artifact Q3527241
  (thousand-theorems__hol-light__Q3527241), "Krull's principal ideal theorem":
  in a commutative Noetherian ring, every prime ideal minimal over a principal
  ideal has height at most one. This file contains no proof.
*)

let Q3527241_KRULLS_PRINCIPAL_IDEAL_THEOREM =
  `let is_comm_ring =
     \(zeroR:R) (oneR:R) (addR:R->R->R) (mulR:R->R->R)
      (negR:R->R).
       (!x. addR zeroR x = x) /\
       (!x. addR (negR x) x = zeroR) /\
       (!x y. addR x y = addR y x) /\
       (!x y z. addR x (addR y z) = addR (addR x y) z) /\
       (!x. mulR oneR x = x) /\
       (!x y. mulR x y = mulR y x) /\
       (!x y z. mulR x (mulR y z) = mulR (mulR x y) z) /\
       (!x y z. mulR x (addR y z) =
                addR (mulR x y) (mulR x z)) in
   let is_ideal =
     \(zeroR:R) (addR:R->R->R) (mulR:R->R->R)
      (negR:R->R) (j:R->bool).
       j zeroR /\
       (!x. j x ==> j (negR x)) /\
       (!x y. j x /\ j y ==> j (addR x y)) /\
       (!a x. j x ==> j (mulR a x)) in
   let ideal_subset =
     \(i:R->bool) (j:R->bool). !x:R. i x ==> j x in
   let finitely_generates_ideal =
     \(zeroR:R) (addR:R->R->R) (mulR:R->R->R)
      (negR:R->R) (j:R->bool) (generators:R->bool).
       FINITE generators /\
       ideal_subset generators j /\
       (!other:R->bool.
          is_ideal zeroR addR mulR negR other /\
          ideal_subset generators other
          ==> ideal_subset j other) in
   let is_noetherian_ring =
     \(zeroR:R) (addR:R->R->R) (mulR:R->R->R)
      (negR:R->R).
       !j:R->bool.
         is_ideal zeroR addR mulR negR j
         ==> ?generators:R->bool.
               finitely_generates_ideal
                 zeroR addR mulR negR j generators in
   let is_principal_ideal =
     \(zeroR:R) (addR:R->R->R) (mulR:R->R->R)
      (negR:R->R) (j:R->bool).
       is_ideal zeroR addR mulR negR j /\
       ?a:R. !x:R. j x <=> ?r:R. x = mulR r a in
   let is_prime_ideal =
     \(zeroR:R) (oneR:R) (addR:R->R->R) (mulR:R->R->R)
      (negR:R->R) (p:R->bool).
       is_ideal zeroR addR mulR negR p /\
       ~(p oneR) /\
       (!x y. p (mulR x y) ==> p x \/ p y) in
   let strict_ideal_subset =
     \(i:R->bool) (j:R->bool).
       ideal_subset i j /\ ?x:R. j x /\ ~(i x) in
   let is_minimal_prime_over =
     \(zeroR:R) (oneR:R) (addR:R->R->R) (mulR:R->R->R)
      (negR:R->R) (i:R->bool) (p:R->bool).
       is_prime_ideal zeroR oneR addR mulR negR p /\
       ideal_subset i p /\
       (!q:R->bool.
          is_prime_ideal zeroR oneR addR mulR negR q /\
          ideal_subset i q /\
          ideal_subset q p
          ==> q = p) in
   let prime_height_at_most_one =
     \(zeroR:R) (oneR:R) (addR:R->R->R) (mulR:R->R->R)
      (negR:R->R) (p:R->bool).
       ~(?q:R->bool. ?l:R->bool.
           is_prime_ideal zeroR oneR addR mulR negR q /\
           is_prime_ideal zeroR oneR addR mulR negR l /\
           strict_ideal_subset l q /\
           strict_ideal_subset q p) in
   !zeroR:R. !oneR:R. !addR:R->R->R. !mulR:R->R->R.
   !negR:R->R. !ideal0:R->bool. !prime0:R->bool.
     is_comm_ring zeroR oneR addR mulR negR /\
     is_noetherian_ring zeroR addR mulR negR /\
     is_principal_ideal zeroR addR mulR negR ideal0 /\
     is_minimal_prime_over
       zeroR oneR addR mulR negR ideal0 prime0
     ==> prime_height_at_most_one
           zeroR oneR addR mulR negR prime0`;;
