(*
  Statement-only formalization of Thousand Theorems corpus artifact Q26708,
  "Binomial theorem": the binomial expansion holds for two elements of an
  arbitrary commutative semiring. This file contains no proof.
*)

let Q26708_BINOMIAL_THEOREM =
  `let is_comm_semiring =
     \(zeroR:R) (oneR:R) (addR:R->R->R) (mulR:R->R->R).
       (!a:R. addR zeroR a = a /\ addR a zeroR = a) /\
       (!a b:R. addR a b = addR b a) /\
       (!a b c:R. addR (addR a b) c = addR a (addR b c)) /\
       (!a:R. mulR oneR a = a /\ mulR a oneR = a) /\
       (!a b:R. mulR a b = mulR b a) /\
       (!a b c:R. mulR (mulR a b) c = mulR a (mulR b c)) /\
       (!a:R. mulR zeroR a = zeroR /\ mulR a zeroR = zeroR) /\
       (!a b c:R.
          mulR a (addR b c) = addR (mulR a b) (mulR a c)) /\
       (!a b c:R.
          mulR (addR a b) c = addR (mulR a c) (mulR b c)) in
   let powerR =
     \(oneR:R) (mulR:R->R->R) (a:R) (k:num).
       ITLIST mulR (REPLICATE k a) oneR in
   let natcastR =
     \(zeroR:R) (oneR:R) (addR:R->R->R) (k:num).
       ITLIST addR (REPLICATE k oneR) zeroR in
   let sumR =
     \(zeroR:R) (addR:R->R->R) (n:num) (f:num->R).
       ITSET (\k a. addR (f k) a) (0..n) zeroR in
   !zeroR oneR:R.
   !addR mulR:R->R->R.
   !x y:R.
   !n:num.
     is_comm_semiring zeroR oneR addR mulR
     ==>
     powerR oneR mulR (addR x y) n =
       sumR zeroR addR n
         (\m:num.
            mulR
              (mulR
                (powerR oneR mulR x m)
                (powerR oneR mulR y (n - m)))
              (natcastR zeroR oneR addR (binom(n,m))))`;;
