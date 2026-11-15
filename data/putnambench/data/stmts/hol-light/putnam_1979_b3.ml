(*
  Statement-only formalization of PutnamBench artifact putnam_1979_b3:
  over an odd finite field, exactly (n - 1) / 2 constant shifts of an
  irreducible monic quadratic remain irreducible. This file contains no proof.
*)

let statement =
  `let field_axioms =
     \(zero_F:A) (one_F:A) (add_F:A->A->A) (mul_F:A->A->A)
      (neg_F:A->A) (inv_F:A->A).
       ~(zero_F = one_F) /\
       (!x y:A. add_F x y = add_F y x) /\
       (!x y z:A. add_F (add_F x y) z = add_F x (add_F y z)) /\
       (!x:A. add_F x zero_F = x) /\
       (!x:A. add_F (neg_F x) x = zero_F) /\
       (!x y:A. mul_F x y = mul_F y x) /\
       (!x y z:A. mul_F (mul_F x y) z = mul_F x (mul_F y z)) /\
       (!x:A. mul_F one_F x = x) /\
       (!x:A. ~(x = zero_F) ==> mul_F (inv_F x) x = one_F) /\
       (!x y z:A.
          mul_F x (add_F y z) = add_F (mul_F x y) (mul_F x z)) in
   let quadratic_rootless =
     \(zero_F:A) (add_F:A->A->A) (mul_F:A->A->A) (b:A) (c:A).
       !x:A.
         ~(add_F (add_F (mul_F x x) (mul_F b x)) c = zero_F) in
   !n:num (zero_F:A) (one_F:A)
    (add_F:A->A->A) (mul_F:A->A->A)
    (neg_F:A->A) (inv_F:A->A) (b:A) (c:A).
     field_axioms zero_F one_F add_F mul_F neg_F inv_F /\
     FINITE (UNIV:A->bool) /\
     CARD (UNIV:A->bool) = n /\
     ODD n /\
     quadratic_rootless zero_F add_F mul_F b c
     ==>
     CARD
       {d:A |
          quadratic_rootless zero_F add_F mul_F b (add_F c d)} =
     (n - 1) DIV 2`;;
