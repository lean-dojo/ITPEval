(*
  Statement-only formalization of Thousand Theorems corpus artifact Q619985,
  "Multinomial theorem": in a semiring, the power of a finite sum of pairwise
  commuting elements expands as the sum over supported exponent functions of
  multinomial coefficients times the corresponding products. This file
  contains no proof.
*)

let Q619985_MULTINOMIAL_THEOREM =
  `let is_semiring =
     \(zeroR:R) (oneR:R) (addR:R->R->R) (mulR:R->R->R).
       (!a:R. addR zeroR a = a /\ addR a zeroR = a) /\
       (!a b:R. addR a b = addR b a) /\
       (!a b c:R. addR (addR a b) c = addR a (addR b c)) /\
       (!a:R. mulR oneR a = a /\ mulR a oneR = a) /\
       (!a b c:R. mulR (mulR a b) c = mulR a (mulR b c)) /\
       (!a b c:R.
          mulR a (addR b c) = addR (mulR a b) (mulR a c)) /\
       (!a b c:R.
          mulR (addR a b) c = addR (mulR a c) (mulR b c)) /\
       (!a:R. mulR zeroR a = zeroR /\ mulR a zeroR = zeroR) in
   let powerR =
     \(oneR:R) (mulR:R->R->R) (x:R) (m:num).
       ITLIST mulR (REPLICATE m x) oneR in
   let natcastR =
     \(zeroR:R) (oneR:R) (addR:R->R->R) (m:num).
       ITLIST addR (REPLICATE m oneR) zeroR in
   let enum_I =
     \(s:I->bool).
       @li:I list.
         PAIRWISE (\x y:I. ~(x = y)) li /\
         (!i:I. MEM i li <=> i IN s) in
   let sumR_I =
     \(zeroR:R) (addR:R->R->R) (s:I->bool) (g:I->R).
       ITSET (\i a. addR (g i) a) s zeroR in
   let productR_I =
     \(oneR:R) (mulR:R->R->R) (s:I->bool) (g:I->R).
       ITLIST (\i a. mulR (g i) a) (enum_I s) oneR in
   let sumN_I =
     \(s:I->bool) (k:I->num).
       ITSET (\i a. k i + a) s 0 in
   let productN_I =
     \(s:I->bool) (k:I->num).
       ITSET (\i a. k i * a) s 1 in
   let multinomial =
     \(s:I->bool) (k:I->num).
       FACT (sumN_I s k) DIV
       productN_I s (\i:I. FACT (k i)) in
   let pi_antidiag =
     \(s:I->bool) (n:num).
       {k:I->num |
          sumN_I s k = n /\
          (!i:I. ~(i IN s) ==> k i = 0)} in
   let sumR_K =
     \(zeroR:R) (addR:R->R->R)
      (t:(I->num)->bool) (g:(I->num)->R).
       ITSET (\k a. addR (g k) a) t zeroR in
   !zeroR oneR:R.
   !addR mulR:R->R->R.
   !s:I->bool.
   !f:I->R.
   !n:num.
     is_semiring zeroR oneR addR mulR /\
     FINITE s /\
     (!i j:I.
        i IN s /\ j IN s /\ ~(i = j)
        ==> mulR (f i) (f j) = mulR (f j) (f i))
     ==>
     powerR oneR mulR (sumR_I zeroR addR s f) n =
       sumR_K zeroR addR (pi_antidiag s n)
         (\k:I->num.
            mulR
              (natcastR zeroR oneR addR (multinomial s k))
              (productR_I oneR mulR s
                (\i:I. powerR oneR mulR (f i) (k i))))`;;
