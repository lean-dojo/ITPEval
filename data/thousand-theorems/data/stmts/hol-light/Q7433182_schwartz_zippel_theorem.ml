(*
  Statement-only formalization of Thousand Theorems corpus artifact Q7433182
  (thousand-theorems__hol-light__Q7433182), "Schwartz-Zippel theorem": for a
  nonzero multivariate polynomial over an integral domain, the fraction of
  zeros in a dependent product of finite subsets is bounded by the maximum,
  over supported monomials, of the sum of coordinate degrees divided by the
  corresponding subset cardinalities. This file contains no proof.
*)

let Q7433182_SCHWARTZ_ZIPPEL_SUP_SUM =
  `let is_integral_domain =
     \(zeroK:K) (oneK:K) (addK:K->K->K) (mulK:K->K->K)
      (negK:K->K).
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
       (!x y:K. mulK x y = zeroK ==> x = zeroK \/ y = zeroK) in
   let power =
     \(oneK:K) (mulK:K->K->K) (x:K) (d:num).
       ITLIST mulK (REPLICATE d x) oneK in
   let is_monomial_on =
     \(n:num) (m:num->num).
       !i:num. n <= i ==> m i = 0 in
   let is_mv_polynomial =
     \(n:num) (zeroK:K) (p:(num->num)->K).
       FINITE {m | ~(p m = zeroK)} /\
       (!m:num->num.
          ~(p m = zeroK) ==> is_monomial_on n m) in
   let polynomial_zero =
     \(zeroK:K). \(m:num->num). zeroK in
   let polynomial_eval =
     \(n:num) (zeroK:K) (oneK:K)
      (addK:K->K->K) (mulK:K->K->K)
      (p:(num->num)->K) (x:num->K).
       iterate addK {m | ~(p m = zeroK)}
         (\m. mulK (p m)
           (iterate mulK {i:num | i < n}
             (\i. power oneK mulK (x i) (m i)))) in
   let product_points =
     \(n:num) (zeroK:K) (S:num->K->bool).
       {x:num->K |
          (!i:num. i < n ==> x i IN S i) /\
          (!i:num. n <= i ==> x i = zeroK)} in
   let zero_points =
     \(n:num) (zeroK:K) (oneK:K)
      (addK:K->K->K) (mulK:K->K->K)
      (p:(num->num)->K) (S:num->K->bool).
       {x:num->K |
          x IN product_points n zeroK S /\
          polynomial_eval n zeroK oneK addK mulK p x = zeroK} in
   let monomial_weight =
     \(n:num) (S:num->K->bool) (m:num->num).
       sum {i:num | i < n}
         (\i. &(m i) / &(CARD (S i))) in
   !n:num.
   !zeroK oneK:K.
   !addK mulK:K->K->K.
   !negK:K->K.
   !p:(num->num)->K.
   !S:num->K->bool.
     is_integral_domain zeroK oneK addK mulK negK /\
     is_mv_polynomial n zeroK p /\
     ~(p = polynomial_zero zeroK) /\
     (!i:num. i < n ==> FINITE (S i))
     ==>
     &(CARD (zero_points n zeroK oneK addK mulK p S)) /
       product {i:num | i < n} (\i. &(CARD (S i)))
     <=
     sup
       (IMAGE (monomial_weight n S)
          {m:num->num | ~(p m = zeroK)})`;;
