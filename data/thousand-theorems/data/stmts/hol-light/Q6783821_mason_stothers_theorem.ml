(*
  Statement-only formalization of Thousand Theorems corpus artifact Q6783821
  (thousand-theorems__hol-light__Q6783821), "Mason–Stothers theorem": for
  three nonzero polynomials over an arbitrary field whose first two are
  coprime and whose sum is zero, each degree plus one is bounded by the degree
  of the product's radical, unless all three formal derivatives vanish. This
  file contains no proof.
*)

let Q6783821_MASON_STOTHERS_THEOREM =
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
   let polynomial =
     \(zeroK:K) (p:num->K). FINITE {n:num | ~(p n = zeroK)} in
   let polynomial_zero =
     \(zeroK:K). \n:num. zeroK in
   let polynomial_one =
     \(zeroK:K) (oneK:K). \n:num. if n = 0 then oneK else zeroK in
   let polynomial_add =
     \(addK:K->K->K) (p:num->K) (q:num->K).
       \n:num. addK (p n) (q n) in
   let polynomial_mul =
     \(zeroK:K) (addK:K->K->K) (mulK:K->K->K)
      (p:num->K) (q:num->K).
       \n:num.
         ITLIST addK
           (GENLIST (\i:num. mulK (p i) (q (n - i))) (n + 1))
           zeroK in
   let polynomial_degree =
     \(zeroK:K) (p:num->K).
       @d:num.
         (!n:num. d < n ==> p n = zeroK) /\
         ((p = polynomial_zero zeroK /\ d = 0) \/ ~(p d = zeroK)) in
   let polynomial_derivative =
     \(zeroK:K) (oneK:K) (addK:K->K->K) (mulK:K->K->K)
      (p:num->K).
       \n:num.
         mulK
           (ITLIST addK (REPLICATE (n + 1) oneK) zeroK)
           (p (n + 1)) in
   let polynomial_divides =
     \(zeroK:K) (addK:K->K->K) (mulK:K->K->K)
      (p:num->K) (q:num->K).
       ?r:num->K.
         polynomial zeroK r /\
         polynomial_mul zeroK addK mulK p r = q in
   let polynomial_unit =
     \(zeroK:K) (oneK:K) (addK:K->K->K) (mulK:K->K->K)
      (p:num->K).
       ?q:num->K.
         polynomial zeroK q /\
         polynomial_mul zeroK addK mulK p q =
           polynomial_one zeroK oneK in
   let polynomial_coprime =
     \(zeroK:K) (oneK:K) (addK:K->K->K) (mulK:K->K->K)
      (p:num->K) (q:num->K).
       ?x y:num->K.
         polynomial zeroK x /\
         polynomial zeroK y /\
         polynomial_add addK
           (polynomial_mul zeroK addK mulK p x)
           (polynomial_mul zeroK addK mulK q y) =
         polynomial_one zeroK oneK in
   let polynomial_monic =
     \(zeroK:K) (oneK:K) (p:num->K).
       p (polynomial_degree zeroK p) = oneK in
   let polynomial_irreducible =
     \(zeroK:K) (oneK:K) (addK:K->K->K) (mulK:K->K->K)
      (p:num->K).
       polynomial zeroK p /\
       ~(p = polynomial_zero zeroK) /\
       ~(polynomial_unit zeroK oneK addK mulK p) /\
       (!q r:num->K.
         polynomial zeroK q /\
         polynomial zeroK r /\
          p = polynomial_mul zeroK addK mulK q r
          ==> polynomial_unit zeroK oneK addK mulK q \/
              polynomial_unit zeroK oneK addK mulK r) in
   let polynomial_radical_degree =
     \(zeroK:K) (oneK:K) (addK:K->K->K) (mulK:K->K->K)
      (p:num->K).
       nsum
         {q:num->K |
            polynomial_irreducible zeroK oneK addK mulK q /\
            polynomial_monic zeroK oneK q /\
            polynomial_divides zeroK addK mulK q p}
         (polynomial_degree zeroK) in
   !zeroK oneK:K.
   !addK mulK:K->K->K.
   !negK invK:K->K.
   !a b c:num->K.
     is_field zeroK oneK addK mulK negK invK /\
     polynomial zeroK a /\
     polynomial zeroK b /\
     polynomial zeroK c /\
     ~(a = polynomial_zero zeroK) /\
     ~(b = polynomial_zero zeroK) /\
     ~(c = polynomial_zero zeroK) /\
     polynomial_coprime zeroK oneK addK mulK a b /\
     polynomial_add addK (polynomial_add addK a b) c =
       polynomial_zero zeroK
     ==>
     let abc =
       polynomial_mul zeroK addK mulK
         (polynomial_mul zeroK addK mulK a b) c in
     let radical_degree =
       polynomial_radical_degree zeroK oneK addK mulK abc in
       (polynomial_degree zeroK a + 1 <=
          radical_degree /\
        polynomial_degree zeroK b + 1 <=
          radical_degree /\
        polynomial_degree zeroK c + 1 <=
          radical_degree) \/
       (polynomial_derivative zeroK oneK addK mulK a =
          polynomial_zero zeroK /\
        polynomial_derivative zeroK oneK addK mulK b =
          polynomial_zero zeroK /\
        polynomial_derivative zeroK oneK addK mulK c =
          polynomial_zero zeroK)`;;
