(*
  Statement-only formalization of PutnamBench corpus artifact putnam_1987_b6:
  parity of the overlap between a sign-representative subset of a finite
  field of order p^2 and its image under doubling. This file contains no proof.
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
          mul_F x (add_F y z) =
          add_F (mul_F x y) (mul_F x z)) in
   !p:num (zero_F:A) (one_F:A)
    (add_F:A->A->A) (mul_F:A->A->A)
    (neg_F:A->A) (inv_F:A->A) (S:A->bool).
     ODD p /\
     prime p /\
     field_axioms zero_F one_F add_F mul_F neg_F inv_F /\
     FINITE (UNIV:A->bool) /\
     CARD (UNIV:A->bool) = p EXP 2 /\
     (!x:A. x IN S ==> ~(x = zero_F)) /\
     CARD S = (p EXP 2 - 1) DIV 2 /\
     (!a:A.
        ~(a = zero_F)
        ==> ~((a IN S) <=> (neg_F a IN S)))
     ==>
     EVEN
       (CARD
         (S INTER
          {x:A | ?a:A. a IN S /\ x = add_F a a}))`;;
