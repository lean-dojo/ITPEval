(*
  Statement-only formalization of Thousand Theorems corpus artifact Q1660147,
  "Mazur–Ulam theorem": every bijective isometry between arbitrary real normed
  affine spaces is an affine isometry equivalence. This file contains no proof.
*)

let Q1660147_MAZUR_ULAM_THEOREM =
 `let real_normed_vector_space =
    \(zero:A) (add:A->A->A) (neg:A->A)
     (smul:real->A->A) (norm:A->real).
       (!x y z:A. add x (add y z) = add (add x y) z) /\
       (!x y:A. add x y = add y x) /\
       (!x:A. add zero x = x) /\
       (!x:A. add (neg x) x = zero) /\
       (!x:A. smul (&1) x = x) /\
       (!a b:real. !x:A.
          smul (a * b) x = smul a (smul b x)) /\
       (!a b:real. !x:A.
          smul (a + b) x = add (smul a x) (smul b x)) /\
       (!a:real. !x y:A.
          smul a (add x y) = add (smul a x) (smul a y)) /\
       (!x:A. smul (&0) x = zero) /\
       (!a:real. smul a zero = zero) /\
       norm zero = &0 /\
       (!x:A. &0 <= norm x) /\
       (!x:A. norm x = &0 <=> x = zero) /\
       (!x:A. norm (neg x) = norm x) /\
       (!x y:A. norm (add x y) <= norm x + norm y) /\
       (!a:real. !x:A. norm (smul a x) = abs a * norm x) in
  let real_normed_vector_space' =
    \(zero:B) (add:B->B->B) (neg:B->B)
     (smul:real->B->B) (norm:B->real).
       (!x y z:B. add x (add y z) = add (add x y) z) /\
       (!x y:B. add x y = add y x) /\
       (!x:B. add zero x = x) /\
       (!x:B. add (neg x) x = zero) /\
       (!x:B. smul (&1) x = x) /\
       (!a b:real. !x:B.
          smul (a * b) x = smul a (smul b x)) /\
       (!a b:real. !x:B.
          smul (a + b) x = add (smul a x) (smul b x)) /\
       (!a:real. !x y:B.
          smul a (add x y) = add (smul a x) (smul a y)) /\
       (!x:B. smul (&0) x = zero) /\
       (!a:real. smul a zero = zero) /\
       norm zero = &0 /\
       (!x:B. &0 <= norm x) /\
       (!x:B. norm x = &0 <=> x = zero) /\
       (!x:B. norm (neg x) = norm x) /\
       (!x y:B. norm (add x y) <= norm x + norm y) /\
       (!a:real. !x:B. norm (smul a x) = abs a * norm x) in
  let affine_torsor =
    \(zero:A) (add:A->A->A)
     (vadd:A->C->C) (vsub:C->C->A).
       (!p:C. vadd zero p = p) /\
       (!v w:A. !p:C.
          vadd (add v w) p = vadd v (vadd w p)) /\
       (!p:C. vsub p p = zero) /\
       (!p q:C. vadd (vsub p q) q = p) /\
       (!v:A. !p:C. vsub (vadd v p) p = v) in
  let affine_torsor' =
    \(zero:B) (add:B->B->B)
     (vadd:B->D->D) (vsub:D->D->B).
       (!p:D. vadd zero p = p) /\
       (!v w:B. !p:D.
          vadd (add v w) p = vadd v (vadd w p)) /\
       (!p:D. vsub p p = zero) /\
       (!p q:D. vadd (vsub p q) q = p) /\
       (!v:B. !p:D. vsub (vadd v p) p = v) in
  let isometry_equiv =
    \(vsubE:C->C->A) (normE:A->real)
     (vsubF:D->D->B) (normF:B->real)
     (f:C->D) (finv:D->C).
       (!p:C. finv (f p) = p) /\
       (!q:D. f (finv q) = q) /\
       (!p q:C.
          normF (vsubF (f p) (f q)) =
          normE (vsubE p q)) in
  let linear_isometry_equiv =
    \(addE:A->A->A) (smulE:real->A->A) (normE:A->real)
     (addF:B->B->B) (smulF:real->B->B) (normF:B->real)
     (L:A->B) (Linv:B->A).
       (!x y:A. L (addE x y) = addF (L x) (L y)) /\
       (!a:real. !x:A. L (smulE a x) = smulF a (L x)) /\
       (!x:A. normF (L x) = normE x) /\
       (!x:A. Linv (L x) = x) /\
       (!y:B. L (Linv y) = y) in
  !zeroE:A.
  !addE:A->A->A.
  !negE:A->A.
  !smulE:real->A->A.
  !normE:A->real.
  !zeroF:B.
  !addF:B->B->B.
  !negF:B->B.
  !smulF:real->B->B.
  !normF:B->real.
  !vaddE:A->C->C.
  !vsubE:C->C->A.
  !vaddF:B->D->D.
  !vsubF:D->D->B.
  !f:C->D.
  !finv:D->C.
    real_normed_vector_space zeroE addE negE smulE normE /\
    real_normed_vector_space' zeroF addF negF smulF normF /\
    affine_torsor zeroE addE vaddE vsubE /\
    affine_torsor' zeroF addF vaddF vsubF /\
    isometry_equiv vsubE normE vsubF normF f finv
    ==> ?L:A->B. ?Linv:B->A.
          linear_isometry_equiv
            addE smulE normE addF smulF normF L Linv /\
          (!v:A. !p:C.
             f (vaddE v p) = vaddF (L v) (f p))`;;
