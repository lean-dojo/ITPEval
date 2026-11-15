(*
  Statement-only formalization of Thousand Theorems corpus artifact Q656645,
  "Hilbert's basis theorem": the univariate polynomial ring over a
  commutative Noetherian ring is Noetherian. This file contains no proof.
*)

let Q656645_HILBERTS_BASIS_THEOREM =
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
       (!x y z.
          mulR x (addR y z) = addR (mulR x y) (mulR x z)) in
   let is_ideal_R =
     \(zeroR:R) (addR:R->R->R) (mulR:R->R->R)
      (negR:R->R) (ideal:R->bool).
       ideal zeroR /\
       (!x. ideal x ==> ideal (negR x)) /\
       (!x y. ideal x /\ ideal y ==> ideal (addR x y)) /\
       (!a x. ideal x ==> ideal (mulR a x)) in
   let finitely_generates_R =
     \(zeroR:R) (addR:R->R->R) (mulR:R->R->R)
      (negR:R->R) (ideal:R->bool) (generators:R->bool).
       FINITE generators /\
       (!x. generators x ==> ideal x) /\
       (!other:R->bool.
          is_ideal_R zeroR addR mulR negR other /\
          (!x. generators x ==> other x)
          ==> !x. ideal x ==> other x) in
   let is_noetherian_R =
     \(zeroR:R) (addR:R->R->R) (mulR:R->R->R)
      (negR:R->R).
       !ideal:R->bool.
         is_ideal_R zeroR addR mulR negR ideal
         ==> ?generators:R->bool.
               finitely_generates_R
                 zeroR addR mulR negR ideal generators in
   let is_polynomial =
     \(zeroR:R) (p:num->R).
       FINITE {n | ~(p n = zeroR)} in
   let polynomial_zero =
     \(zeroR:R). \n:num. zeroR in
   let polynomial_one =
     \(zeroR:R) (oneR:R). \n:num.
       if n = 0 then oneR else zeroR in
   let polynomial_neg =
     \(negR:R->R) (p:num->R). \n:num. negR (p n) in
   let polynomial_add =
     \(addR:R->R->R) (p:num->R) (q:num->R).
       \n:num. addR (p n) (q n) in
   let polynomial_mul =
     \(addR:R->R->R) (mulR:R->R->R)
      (p:num->R) (q:num->R).
       \n:num.
         iterate addR {(i,j) | i + j = n}
           (\(i,j). mulR (p i) (q j)) in
   let is_ideal_polynomial =
     \(zeroR:R) (addR:R->R->R) (mulR:R->R->R)
      (negR:R->R) (ideal:(num->R)->bool).
       (!p. ideal p ==> is_polynomial zeroR p) /\
       ideal (polynomial_zero zeroR) /\
       (!p.
          ideal p
          ==> ideal (polynomial_neg negR p)) /\
       (!p q.
          ideal p /\ ideal q
          ==> ideal (polynomial_add addR p q)) /\
       (!a p.
          is_polynomial zeroR a /\ ideal p
          ==> ideal (polynomial_mul addR mulR a p)) in
   let finitely_generates_polynomial =
     \(zeroR:R) (addR:R->R->R) (mulR:R->R->R)
      (negR:R->R) (ideal:(num->R)->bool)
      (generators:(num->R)->bool).
       FINITE generators /\
       (!p. generators p ==> ideal p) /\
       (!other:(num->R)->bool.
          is_ideal_polynomial zeroR addR mulR negR other /\
          (!p. generators p ==> other p)
          ==> !p. ideal p ==> other p) in
   let is_noetherian_polynomial_ring =
     \(zeroR:R) (addR:R->R->R) (mulR:R->R->R)
      (negR:R->R).
       !ideal:(num->R)->bool.
         is_ideal_polynomial zeroR addR mulR negR ideal
         ==> ?generators:(num->R)->bool.
               finitely_generates_polynomial
                 zeroR addR mulR negR ideal generators in
   !zeroR oneR:R.
   !addR mulR:R->R->R.
   !negR:R->R.
     is_comm_ring zeroR oneR addR mulR negR /\
     is_noetherian_R zeroR addR mulR negR
     ==> is_noetherian_polynomial_ring
           zeroR addR mulR negR`;;
