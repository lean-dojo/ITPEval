(*
  Statement-only formalization of PutnamBench artifact putnam_1986_b6:
  a matrix identity over an arbitrary field under symmetry hypotheses for
  two products involving transposes. This file contains no proof.
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
   let matrix_mul =
     \(zero_F:A) (add_F:A->A->A) (mul_F:A->A->A)
      (M:I->I->A) (N:I->I->A).
       \i j:I.
         ITSET
           (\k:I. \acc:A. add_F (mul_F (M i k) (N k j)) acc)
           (UNIV:I->bool) zero_F in
   let matrix_transpose =
     \(M:I->I->A). \i j:I. M j i in
   let matrix_sub =
     \(add_F:A->A->A) (neg_F:A->A)
      (M:I->I->A) (N:I->I->A).
       \i j:I. add_F (M i j) (neg_F (N i j)) in
   let identity_matrix =
     \(zero_F:A) (one_F:A). \i j:I. if i = j then one_F else zero_F in
   !n:num (zero_F:A) (one_F:A)
    (add_F:A->A->A) (mul_F:A->A->A)
    (neg_F:A->A) (inv_F:A->A)
    (A:I->I->A) (B:I->I->A) (C:I->I->A) (D:I->I->A).
     field_axioms zero_F one_F add_F mul_F neg_F inv_F /\
     FINITE (UNIV:I->bool) /\
     CARD (UNIV:I->bool) = n /\
     0 < n /\
     matrix_mul zero_F add_F mul_F A (matrix_transpose B) =
       matrix_transpose
         (matrix_mul zero_F add_F mul_F A (matrix_transpose B)) /\
     matrix_mul zero_F add_F mul_F C (matrix_transpose D) =
       matrix_transpose
         (matrix_mul zero_F add_F mul_F C (matrix_transpose D)) /\
     matrix_sub add_F neg_F
       (matrix_mul zero_F add_F mul_F A (matrix_transpose D))
       (matrix_mul zero_F add_F mul_F B (matrix_transpose C)) =
       identity_matrix zero_F one_F
     ==>
     matrix_sub add_F neg_F
       (matrix_mul zero_F add_F mul_F (matrix_transpose A) D)
       (matrix_mul zero_F add_F mul_F (matrix_transpose C) B) =
       identity_matrix zero_F one_F`;;
