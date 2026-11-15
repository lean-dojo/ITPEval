(*
  Statement-only formalization of Thousand Theorems corpus artifact Q720469
  (thousand-theorems__hol-light__Q720469), "Chevalley–Warning theorem": over
  a finite field of characteristic p, if a finite family of multivariate
  polynomials has sum of total degrees smaller than the number of variables,
  then p divides the number of their common zeros. This file contains no proof.
*)

let Q720469_CHEVALLEY_WARNING_THEOREM =
  `let is_field =
     \(zeroK:K) (oneK:K) (addK:K->K->K) (mulK:K->K->K)
      (negK:K->K) (invK:K->K).
       ~(zeroK = oneK) /\
       (!x:K. addK zeroK x = x) /\
       (!x:K. addK (negK x) x = zeroK) /\
       (!x y:K. addK x y = addK y x) /\
       (!x y z:K. addK x (addK y z) = addK (addK x y) z) /\
       (!x:K. mulK oneK x = x) /\
       (!x y:K. mulK x y = mulK y x) /\
       (!x y z:K. mulK x (mulK y z) = mulK (mulK x y) z) /\
       (!x y z:K.
          mulK x (addK y z) = addK (mulK x y) (mulK x z)) /\
       invK zeroK = zeroK /\
       (!x:K. ~(x = zeroK) ==> mulK (invK x) x = oneK) in
   let natural_multiple =
     \(zeroK:K) (addK:K->K->K) (n:num) (x:K).
       ITLIST addK (REPLICATE n x) zeroK in
   let has_characteristic =
     \(zeroK:K) (oneK:K) (addK:K->K->K) (p:num).
       !n:num.
         natural_multiple zeroK addK n oneK = zeroK <=>
         p divides n in
   let power =
     \(oneK:K) (mulK:K->K->K) (x:K) (n:num).
       ITLIST mulK (REPLICATE n x) oneK in
   let is_mv_polynomial =
     \(zeroK:K) (q:(V->num)->K).
       FINITE {m | ~(q m = zeroK)} in
   let polynomial_zero =
     \(zeroK:K). \(m:V->num). zeroK in
   let monomial_total_degree =
     \(m:V->num). nsum (UNIV:V->bool) m in
   let polynomial_total_degree =
     \(zeroK:K) (q:(V->num)->K).
       @d:num.
         (!m:V->num.
            ~(q m = zeroK)
            ==> monomial_total_degree m <= d) /\
         ((q = polynomial_zero zeroK /\ d = 0) \/
          (?m:V->num.
             ~(q m = zeroK) /\
             monomial_total_degree m = d)) in
   let polynomial_eval =
     \(zeroK:K) (oneK:K) (addK:K->K->K) (mulK:K->K->K)
      (q:(V->num)->K) (x:V->K).
       iterate addK {m | ~(q m = zeroK)}
         (\m. mulK (q m)
           (iterate mulK (UNIV:V->bool)
             (\v. power oneK mulK (x v) (m v)))) in
   let common_solutions =
     \(zeroK:K) (oneK:K) (addK:K->K->K) (mulK:K->K->K)
      (s:I->bool) (f:I->(V->num)->K).
       {x:V->K |
          !i:I.
            i IN s
            ==> polynomial_eval
                  zeroK oneK addK mulK (f i) x = zeroK} in
   !p:num.
   !s:I->bool.
   !zeroK oneK:K.
   !addK mulK:K->K->K.
   !negK invK:K->K.
   !f:I->(V->num)->K.
     is_field zeroK oneK addK mulK negK invK /\
     FINITE (UNIV:K->bool) /\
     has_characteristic zeroK oneK addK p /\
     FINITE (UNIV:V->bool) /\
     FINITE s /\
     (!i:I. is_mv_polynomial zeroK (f i)) /\
     nsum s (\i:I. polynomial_total_degree zeroK (f i))
       < CARD (UNIV:V->bool)
     ==> p divides
         CARD
           (common_solutions
             zeroK oneK addK mulK s f)`;;
