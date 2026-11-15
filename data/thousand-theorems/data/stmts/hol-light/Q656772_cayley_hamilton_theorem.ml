(*
  Statement-only formalization of Thousand Theorems corpus artifact Q656772
  (thousand-theorems__hol-light__Q656772), "Cayley–Hamilton theorem": over
  any commutative ring, the characteristic polynomial of a square matrix on
  a finite index type annihilates that matrix. This file contains no proof.
*)

let Q656772_CAYLEY_HAMILTON_THEOREM =
  `let is_comm_ring =
     \(zeroR:R) (oneR:R) (addR:R->R->R) (mulR:R->R->R)
      (negR:R->R).
       (!x:R. addR zeroR x = x) /\
       (!x:R. addR (negR x) x = zeroR) /\
       (!x y:R. addR x y = addR y x) /\
       (!x y z:R. addR x (addR y z) = addR (addR x y) z) /\
       (!x:R. mulR oneR x = x) /\
       (!x y:R. mulR x y = mulR y x) /\
       (!x y z:R. mulR x (mulR y z) = mulR (mulR x y) z) /\
       (!x y z:R.
          mulR x (addR y z) = addR (mulR x y) (mulR x z)) in
   let matrix_identity =
     \(zeroR:R) (oneR:R) (s:I->bool).
       \i j:I. if i IN s /\ j = i then oneR else zeroR in
   let matrix_mul =
     \(zeroR:R) (addR:R->R->R) (mulR:R->R->R) (s:I->bool)
      (A:I->I->R) (B:I->I->R).
       \i j:I. iterate addR s (\k:I. mulR (A i k) (B k j)) in
   let matrix_pow =
     \(zeroR:R) (oneR:R) (addR:R->R->R) (mulR:R->R->R)
      (s:I->bool) (A:I->I->R) (n:num).
       ITLIST (matrix_mul zeroR addR mulR s)
         (REPLICATE n A) (matrix_identity zeroR oneR s) in
   let polynomial_mul =
     \(zeroR:R) (addR:R->R->R) (mulR:R->R->R)
      (p:num->R) (q:num->R).
       \n:num. iterate addR (0..n) (\k:num. mulR (p k) (q (n - k))) in
   let apply_swaps =
     \(swaps:(I#I)list) (x:I).
       ITLIST
         (\ab y:I.
            if y = FST ab then SND ab
            else if y = SND ab then FST ab
            else y)
         swaps x in
   let even_permutation =
     \(s:I->bool) (p:I->I).
       ?swaps:(I#I)list.
         EVEN (LENGTH swaps) /\
         ALL
           (\ab:I#I.
              FST ab IN s /\ SND ab IN s /\ ~(FST ab = SND ab))
           swaps /\
         (!i:I. i IN s ==> apply_swaps swaps i = p i) in
   let signR =
     \(oneR:R) (negR:R->R) (s:I->bool) (p:I->I).
       if even_permutation s p then oneR else negR oneR in
   let permutations =
     \(s:I->bool).
       {p:I->I | BIJ p s s /\ (!i:I. ~(i IN s) ==> p i = i)} in
   let characteristic_coefficient =
     \(zeroR:R) (oneR:R) (addR:R->R->R) (mulR:R->R->R)
      (negR:R->R) (s:I->bool) (M:I->I->R) (n:num).
       iterate addR (permutations s)
         (\p:I->I.
            mulR (signR oneR negR s p)
              ((iterate (polynomial_mul zeroR addR mulR) s
                  (\i:I. \k:num.
                     if k = 0 then negR (M i (p i))
                     else if k = 1 /\ p i = i then oneR
                     else zeroR)) n)) in
   !zeroR oneR:R.
   !addR mulR:R->R->R.
   !negR:R->R.
   !s:I->bool.
   !M:I->I->R.
     is_comm_ring zeroR oneR addR mulR negR /\
     FINITE s
     ==>
     !i j:I.
       i IN s /\ j IN s
       ==>
       iterate addR (0..CARD s)
         (\n:num.
            mulR
              (characteristic_coefficient
                zeroR oneR addR mulR negR s M n)
              (matrix_pow zeroR oneR addR mulR s M n i j)) =
       zeroR`;;
