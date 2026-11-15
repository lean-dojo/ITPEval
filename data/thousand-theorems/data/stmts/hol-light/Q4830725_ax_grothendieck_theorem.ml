(*
  Statement-only formalization of Thousand Theorems corpus artifact Q4830725
  (thousand-theorems__hol-light__Q4830725), "Ax–Grothendieck theorem": over an
  algebraically closed field, a polynomial self-map of the zero locus of an
  ideal in finitely many variables is surjective there if it maps the locus
  to itself and is injective there. This file contains no proof.
*)

let Q4830725_AX_GROTHENDIECK_THEOREM =
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
       (!x:K. ~(x = zeroK) ==> mulK (invK x) x = oneK) in
   let power =
     \(oneK:K) (mulK:K->K->K) (x:K) (d:num).
       ITLIST mulK (REPLICATE d x) oneK in
   let is_univariate_polynomial =
     \(zeroK:K) (q:num->K). FINITE {d | ~(q d = zeroK)} in
   let univariate_eval =
     \(zeroK:K) (oneK:K) (addK:K->K->K) (mulK:K->K->K)
      (q:num->K) (x:K).
       iterate addK {d | ~(q d = zeroK)}
         (\d. mulK (q d) (power oneK mulK x d)) in
   let is_algebraically_closed =
     \(zeroK:K) (oneK:K) (addK:K->K->K) (mulK:K->K->K).
       !q:num->K.
         is_univariate_polynomial zeroK q /\
         (?d:num. ~(d = 0) /\ ~(q d = zeroK))
         ==> ?x:K.
               univariate_eval zeroK oneK addK mulK q x = zeroK in
   let is_monomial_on =
     \(n:num) (m:num->num).
       !i:num. n <= i ==> m i = 0 in
   let is_mv_polynomial =
     \(n:num) (zeroK:K) (q:(num->num)->K).
       FINITE {m | ~(q m = zeroK)} /\
       (!m:num->num.
          ~(q m = zeroK) ==> is_monomial_on n m) in
   let polynomial_zero =
     \(zeroK:K). \(m:num->num). zeroK in
   let polynomial_neg =
     \(negK:K->K) (q:(num->num)->K).
       \m. negK (q m) in
   let polynomial_add =
     \(addK:K->K->K) (q:(num->num)->K) (r:(num->num)->K).
       \m. addK (q m) (r m) in
   let polynomial_mul =
     \(zeroK:K) (addK:K->K->K) (mulK:K->K->K)
      (q:(num->num)->K) (r:(num->num)->K).
       \m. iterate addK
             {(u,v) |
                ~(q u = zeroK) /\
                ~(r v = zeroK) /\
                (!i:num. m i = u i + v i)}
             (\(u,v). mulK (q u) (r v)) in
   let is_ideal =
     \(n:num) (zeroK:K) (addK:K->K->K) (mulK:K->K->K)
      (negK:K->K) (ideal:((num->num)->K)->bool).
       (!q. ideal q ==> is_mv_polynomial n zeroK q) /\
       ideal (polynomial_zero zeroK) /\
       (!q. ideal q ==> ideal (polynomial_neg negK q)) /\
       (!q r.
          ideal q /\ ideal r
          ==> ideal (polynomial_add addK q r)) /\
       (!a q.
          is_mv_polynomial n zeroK a /\ ideal q
          ==> ideal (polynomial_mul zeroK addK mulK a q)) in
   let polynomial_eval =
     \(n:num) (zeroK:K) (oneK:K)
      (addK:K->K->K) (mulK:K->K->K)
      (q:(num->num)->K) (x:num->K).
       iterate addK {m | ~(q m = zeroK)}
         (\m. mulK (q m)
           (iterate mulK {i:num | i < n}
             (\i. power oneK mulK (x i) (m i)))) in
   let canonical_point =
     \(n:num) (zeroK:K) (x:num->K).
       !i:num. n <= i ==> x i = zeroK in
   let zero_locus =
     \(n:num) (zeroK:K) (oneK:K)
      (addK:K->K->K) (mulK:K->K->K)
      (ideal:((num->num)->K)->bool).
       {x:num->K |
          canonical_point n zeroK x /\
          !q. ideal q
              ==> polynomial_eval n zeroK oneK addK mulK q x = zeroK} in
   let polynomial_map =
     \(n:num) (zeroK:K) (oneK:K)
      (addK:K->K->K) (mulK:K->K->K)
      (p:num->(num->num)->K) (x:num->K).
       \i. if i < n
           then polynomial_eval n zeroK oneK addK mulK (p i) x
           else zeroK in
   !n:num.
   !zeroK oneK:K.
   !addK mulK:K->K->K.
   !negK invK:K->K.
   !ideal:((num->num)->K)->bool.
   !p:num->(num->num)->K.
     is_field zeroK oneK addK mulK negK invK /\
     is_algebraically_closed zeroK oneK addK mulK /\
     is_ideal n zeroK addK mulK negK ideal /\
     (!i:num. i < n ==> is_mv_polynomial n zeroK (p i))
     ==>
     let S = zero_locus n zeroK oneK addK mulK ideal in
     let f = polynomial_map n zeroK oneK addK mulK p in
       (!x. x IN S ==> f x IN S) ==>
       (!x y. x IN S /\ y IN S /\ f x = f y ==> x = y) ==>
       (!y. y IN S ==> ?x. x IN S /\ f x = y)`;;
