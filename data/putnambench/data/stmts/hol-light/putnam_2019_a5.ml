(*
  Statement-only formalization of PutnamBench corpus artifact putnam_2019_a5
  (putnambench__hol-light__putnam_2019_a5): the greatest power of x - 1
  dividing a polynomial over the finite field of odd prime order p whose
  kth coefficient is k^((p - 1)/2). This file contains no proof.
*)

needs "Library/iter.ml";;

let statement =
  `let pmul_mod =
     \p:num. \a b:num->num. \k:num.
       nsum (0..k) (\i:num. a i * b (k - i)) MOD p in
   let one_poly =
     \k:num. if k = 0 then 1 else 0 in
   let x_minus_one =
     \p:num. \k:num.
       if k = 0 then p - 1 else if k = 1 then 1 else 0 in
   let ppow_mod =
     \p:num. \a:num->num. \n:num.
       ITER n (pmul_mod p a) one_poly in
   let finite_poly =
     \a:num->num. ?d:num. !k:num. d < k ==> a k = 0 in
   let poly_divides_mod =
     \p:num. \a b:num->num.
       ?c:num->num.
         finite_poly c /\
         !k:num. b k MOD p = pmul_mod p a c k in
   !p:num. !q:num->num.
     ODD p /\
     prime p /\
     (!k:num.
        q k =
        if 1 <= k /\ k <= p - 1
        then k EXP ((p - 1) DIV 2) MOD p
        else 0)
     ==>
     poly_divides_mod p
       (ppow_mod p (x_minus_one p) ((p - 1) DIV 2)) q /\
     (!n:num.
        poly_divides_mod p (ppow_mod p (x_minus_one p) n) q
        ==> n <= (p - 1) DIV 2)`;;
