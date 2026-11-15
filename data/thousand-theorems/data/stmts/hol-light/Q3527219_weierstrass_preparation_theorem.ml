(*
  Statement-only formalization of Thousand Theorems corpus artifact Q3527219
  (thousand-theorems__hol-light__Q3527219), "Weierstrass preparation theorem":
  over a complete local commutative ring, every formal power series
  nonzero modulo the maximal ideal factors as a distinguished polynomial times
  a unit power series. This file contains no proof.
*)

let Q3527219_WEIERSTRASS_PREPARATION_THEOREM =
  `let is_commutative_ring =
     \(zeroA:A) (oneA:A) (addA:A->A->A) (mulA:A->A->A)
      (negA:A->A).
       (!x:A. addA zeroA x = x) /\
       (!x:A. addA (negA x) x = zeroA) /\
       (!x y:A. addA x y = addA y x) /\
       (!x y z:A. addA x (addA y z) = addA (addA x y) z) /\
       (!x:A. mulA oneA x = x) /\
       (!x y:A. mulA x y = mulA y x) /\
       (!x y z:A. mulA x (mulA y z) = mulA (mulA x y) z) /\
       (!x y z:A.
          mulA x (addA y z) = addA (mulA x y) (mulA x z)) in
   let is_unit =
     \(oneA:A) (mulA:A->A->A) (x:A).
       ?y:A. mulA x y = oneA in
   let is_ideal =
     \(zeroA:A) (addA:A->A->A) (mulA:A->A->A)
      (negA:A->A) (ideal:A->bool).
       ideal zeroA /\
       (!x:A. ideal x ==> ideal (negA x)) /\
       (!x y:A. ideal x /\ ideal y ==> ideal (addA x y)) /\
       (!a x:A. ideal x ==> ideal (mulA a x)) in
   let is_local_ring =
     \(zeroA:A) (oneA:A) (addA:A->A->A) (mulA:A->A->A).
       ~(zeroA = oneA) /\
       (!x y:A.
          addA x y = oneA
          ==> is_unit oneA mulA x \/ is_unit oneA mulA y) in
   let maximal_ideal =
     \(oneA:A) (mulA:A->A->A).
       \x:A. ~(is_unit oneA mulA x) in
   let finite_sum =
     \(zeroA:A) (addA:A->A->A) (k:num) (term:num->A).
       ITLIST addA (list_of_seq term k) zeroA in
   let finite_product =
     \(oneA:A) (mulA:A->A->A) (k:num) (term:num->A).
       ITLIST mulA (list_of_seq term k) oneA in
   let ideal_power_mem =
     \(zeroA:A) (oneA:A) (addA:A->A->A) (mulA:A->A->A)
      (ideal:A->bool) (n:num) (x:A).
       ?k:num. ?coefficient:num->A. ?factor:num->num->A.
         x =
           finite_sum zeroA addA k
             (\i:num.
                mulA (coefficient i)
                  (finite_product oneA mulA n (factor i))) /\
         (!i j:num.
            i < k /\ j < n ==> ideal (factor i j)) in
   let is_adically_complete =
     \(zeroA:A) (oneA:A) (addA:A->A->A) (mulA:A->A->A)
      (negA:A->A) (ideal:A->bool).
       (!x:A.
          (!n:num.
             ideal_power_mem zeroA oneA addA mulA ideal n x)
          ==> x = zeroA) /\
       (!sequence:num->A.
          (!m n:num.
             m <= n
             ==> ideal_power_mem
                   zeroA oneA addA mulA ideal m
                   (addA (sequence m) (negA (sequence n))))
          ==> ?limit:A.
                !n:num.
                  ideal_power_mem
                    zeroA oneA addA mulA ideal n
                    (addA (sequence n) (negA limit))) in
   let is_polynomial =
     \(zeroA:A) (polynomial:num->A).
       FINITE {n:num | ~(polynomial n = zeroA)} in
   let is_distinguished_polynomial =
     \(zeroA:A) (oneA:A) (ideal:A->bool)
      (polynomial:num->A).
       is_polynomial zeroA polynomial /\
       ?degree:num.
         polynomial degree = oneA /\
         (!n:num. degree < n ==> polynomial n = zeroA) /\
         (!n:num. n < degree ==> ideal (polynomial n)) in
   let power_series_one =
     \(zeroA:A) (oneA:A).
       \n:num. if n = 0 then oneA else zeroA in
   let power_series_mul =
     \(zeroA:A) (addA:A->A->A) (mulA:A->A->A)
      (left:num->A) (right:num->A).
       \n:num.
         finite_sum zeroA addA (SUC n)
           (\i:num. mulA (left i) (right (n - i))) in
   let is_unit_power_series =
     \(zeroA:A) (oneA:A) (addA:A->A->A) (mulA:A->A->A)
      (series:num->A).
       ?inverse:num->A.
         power_series_mul zeroA addA mulA series inverse =
           power_series_one zeroA oneA /\
         power_series_mul zeroA addA mulA inverse series =
           power_series_one zeroA oneA in
   !zeroA oneA:A.
   !addA mulA:A->A->A.
   !negA:A->A.
   !g:num->A.
     let maximal =
       maximal_ideal oneA mulA in
     is_commutative_ring zeroA oneA addA mulA negA /\
     is_local_ring zeroA oneA addA mulA /\
     is_adically_complete
       zeroA oneA addA mulA negA maximal /\
     (?n:num. ~(maximal (g n)))
     ==>
     ?f:num->A. ?h:num->A.
       is_distinguished_polynomial zeroA oneA maximal f /\
       is_unit_power_series zeroA oneA addA mulA h /\
       g = power_series_mul zeroA addA mulA f h`;;
