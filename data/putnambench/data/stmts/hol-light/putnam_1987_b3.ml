(*
  Statement-only formalization of PutnamBench artifact putnam_1987_b3:
  the rational parametrization of the unit circle over an arbitrary field
  of characteristic not two. This file contains no proof.
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
   let square = \(mul_F:A->A->A) (x:A). mul_F x x in
   let sub_F =
     \(add_F:A->A->A) (neg_F:A->A) (x:A) (y:A).
       add_F x (neg_F y) in
   let div_F =
     \(mul_F:A->A->A) (inv_F:A->A) (x:A) (y:A).
       mul_F x (inv_F y) in
   !(zero_F:A) (one_F:A)
    (add_F:A->A->A) (mul_F:A->A->A)
    (neg_F:A->A) (inv_F:A->A).
     field_axioms zero_F one_F add_F mul_F neg_F inv_F /\
     ~(add_F one_F one_F = zero_F)
     ==>
     {p:A#A |
        add_F (square mul_F (FST p)) (square mul_F (SND p)) =
        one_F} =
     {(one_F,zero_F)} UNION
     {p:A#A |
        ?r:A.
          ~(square mul_F r = neg_F one_F) /\
          p =
          (div_F mul_F inv_F
             (sub_F add_F neg_F (square mul_F r) one_F)
             (add_F (square mul_F r) one_F),
           div_F mul_F inv_F
             (mul_F (add_F one_F one_F) r)
             (add_F (square mul_F r) one_F))}`;;
