(*
  Statement-only formalization of Thousand Theorems corpus artifact Q570779,
  "Vieta's formulas": over an arbitrary commutative semiring, the product of
  the linear polynomials X + C r is the polynomial whose coefficients are the
  elementary symmetric sums of the finite multiset of r's. This file contains
  no proof.
*)

let q570779_comm_semiring = new_definition
  `q570779_comm_semiring (zero:A) (un:A)
      (add:A->A->A) (mul:A->A->A) <=>
     (!x y:A. add x y = add y x) /\
     (!x y z:A. add (add x y) z = add x (add y z)) /\
     (!x:A. add zero x = x /\ add x zero = x) /\
     (!x y:A. mul x y = mul y x) /\
     (!x y z:A. mul (mul x y) z = mul x (mul y z)) /\
     (!x:A. mul un x = x /\ mul x un = x) /\
     (!x:A. mul zero x = zero /\ mul x zero = zero) /\
     (!x y z:A.
        mul x (add y z) = add (mul x y) (mul x z) /\
        mul (add x y) z = add (mul x z) (mul y z))`;;

let q570779_poly_zero = new_definition
  `q570779_poly_zero (zero:A) = (\n:num. zero)`;;

let q570779_poly_one = new_definition
  `q570779_poly_one (zero:A) (un:A) =
     (\n:num. if n = 0 then un else zero)`;;

let q570779_poly_add = new_definition
  `q570779_poly_add (add:A->A->A) (p:num->A) (q:num->A) =
     (\n. add (p n) (q n))`;;

let q570779_poly_mul = new_definition
  `q570779_poly_mul (zero:A) (add:A->A->A) (mul:A->A->A)
      (p:num->A) (q:num->A) =
     (\n. iterate add (0..n) (\i. mul (p i) (q (n - i))))`;;

let q570779_C = new_definition
  `q570779_C (zero:A) (c:A) =
     (\n:num. if n = 0 then c else zero)`;;

let q570779_X = new_definition
  `q570779_X (zero:A) (un:A) =
     (\n:num. if n = 1 then un else zero)`;;

let q570779_poly_pow = new_recursive_definition num_RECURSION
  `(q570779_poly_pow (onep:num->A) (mulp:(num->A)->(num->A)->(num->A))
       (p:num->A) 0 = onep) /\
   (!n. q570779_poly_pow onep mulp p (SUC n) =
        mulp (q570779_poly_pow onep mulp p n) p)`;;

let q570779_poly_prod = new_recursive_definition list_RECURSION
  `(q570779_poly_prod (onep:num->A)
       (mulp:(num->A)->(num->A)->(num->A)) [] = onep) /\
   (!h t. q570779_poly_prod onep mulp (CONS h t) =
          mulp h (q570779_poly_prod onep mulp t))`;;

let q570779_poly_sum = new_recursive_definition num_RECURSION
  `(q570779_poly_sum (zerop:num->A)
       (addp:(num->A)->(num->A)->(num->A)) (f:num->num->A) 0 = zerop) /\
   (!n. q570779_poly_sum zerop addp f (SUC n) =
        addp (q570779_poly_sum zerop addp f n) (f n))`;;

let q570779_esymm = new_recursive_definition list_RECURSION
  `(q570779_esymm (zero:A) (un:A) (add:A->A->A) (mul:A->A->A)
       [] k = if k = 0 then un else zero) /\
   (!h t k. q570779_esymm zero un add mul (CONS h t) k =
      if k = 0 then un
      else add (q570779_esymm zero un add mul t k)
               (mul h (q570779_esymm zero un add mul t (PRE k))))`;;

let Q570779_VIETA_S_FORMULAS =
  `!zero un:A. !add mul:A->A->A. !s:A list.
     q570779_comm_semiring zero un add mul
     ==>
     q570779_poly_prod
       (q570779_poly_one zero un)
       (q570779_poly_mul zero add mul)
       (MAP
         (\r. q570779_poly_add add
                (q570779_X zero un) (q570779_C zero r))
         s) =
     q570779_poly_sum
       (q570779_poly_zero zero)
       (q570779_poly_add add)
       (\j. q570779_poly_mul zero add mul
              (q570779_C zero (q570779_esymm zero un add mul s j))
              (q570779_poly_pow
                (q570779_poly_one zero un)
                (q570779_poly_mul zero add mul)
                (q570779_X zero un)
                (LENGTH s - j)))
       (SUC (LENGTH s))`;;
