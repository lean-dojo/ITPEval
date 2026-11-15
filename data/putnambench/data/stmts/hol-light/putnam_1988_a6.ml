(*
  Statement-only formalization of PutnamBench corpus artifact putnam_1988_a6:
  a linear endomorphism of an n-dimensional vector space with n+1
  eigenvectors, every n of which are linearly independent, is a scalar
  multiple of the identity. This file contains no proof.
*)

let statement =
  `!n:num (zero_F:A) (one_F:A)
    (add_F:A->A->A) (mul_F:A->A->A)
    (neg_F:A->A) (inv_F:A->A)
    (zero_V:V) (add_V:V->V->V) (neg_V:V->V)
    (smul:A->V->V) (Aop:V->V) (evecs:V->bool).
     let field_axioms =
       (~(zero_F = one_F) /\
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
          add_F (mul_F x y) (mul_F x z))) in
     let vector_space_axioms =
       ((!x y:V. add_V x y = add_V y x) /\
       (!x y z:V. add_V (add_V x y) z = add_V x (add_V y z)) /\
       (!x:V. add_V x zero_V = x) /\
       (!x:V. add_V (neg_V x) x = zero_V) /\
       (!a:A. !x y:V.
          smul a (add_V x y) = add_V (smul a x) (smul a y)) /\
       (!a b:A. !x:V.
          smul (add_F a b) x = add_V (smul a x) (smul b x)) /\
       (!a b:A. !x:V.
          smul (mul_F a b) x = smul a (smul b x)) /\
       (!x:V. smul one_F x = x)) in
     let linear_combination =
       \(coeff:num->A) (vectors:num->V).
         ITSET
           (\i:num. \acc:V.
              add_V (smul (coeff i) (vectors i)) acc)
           {i:num | i < n} zero_V in
     let linearly_independent =
       \(vectors:num->V).
         !coeff:num->A.
           linear_combination coeff vectors = zero_V
           ==> !i:num. i < n ==> coeff i = zero_F in
     let basis =
       \(vectors:num->V).
         linearly_independent vectors /\
         (!x:V.
            ?coeff:num->A. linear_combination coeff vectors = x) in
     field_axioms /\
     vector_space_axioms /\
     (!a b:A. !x y:V.
        Aop (add_V (smul a x) (smul b y)) =
        add_V (smul a (Aop x)) (smul b (Aop y))) /\
     (?vectors:num->V. basis vectors) /\
     evecs HAS_SIZE (n + 1) /\
     (!v:V.
        v IN evecs
        ==> ~(v = zero_V) /\ ?a:A. Aop v = smul a v) /\
     (!vectors:num->V.
        IMAGE vectors {i:num | i < n} SUBSET evecs /\
        CARD (IMAGE vectors {i:num | i < n}) = n
        ==> linearly_independent vectors)
     ==> ?c:A. !x:V. Aop x = smul c x`;;
