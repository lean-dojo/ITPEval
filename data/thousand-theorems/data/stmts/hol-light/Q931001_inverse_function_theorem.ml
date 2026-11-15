(*
  Statement-only formalization of Thousand Theorems corpus artifact Q931001
  (thousand-theorems__hol-light__Q931001), "Inverse function theorem": a map
  between normed spaces whose strict derivative at a point is a continuous
  linear equivalence has a local two-sided inverse with the inverse strict
  derivative at the image point. This file contains no proof.
*)

let Q931001_INVERSE_FUNCTION_THEOREM =
 `!zeroK oneK:A.
  !addK mulK:A->A->A.
  !negK invK:A->A.
  !normK:A->real.
  !zeroE:B.
  !addE:B->B->B.
  !negE:B->B.
  !smulE:A->B->B.
  !normE:B->real.
  !zeroF:C.
  !addF:C->C->C.
  !negF:C->C.
  !smulF:A->C->C.
  !normF:C->real.
  !f:B->C.
  !derivative:B->C.
  !inverse_derivative:C->B.
  !point:B.
  let nontrivially_normed_field =
    \(zeroK:A) (oneK:A)
     (addK:A->A->A) (mulK:A->A->A)
     (negK:A->A) (invK:A->A) (normK:A->real).
       ~(zeroK = oneK) /\
       (!a b c:A. addK a (addK b c) = addK (addK a b) c) /\
       (!a b:A. addK a b = addK b a) /\
       (!a:A. addK zeroK a = a) /\
       (!a:A. addK (negK a) a = zeroK) /\
       (!a b c:A. mulK a (mulK b c) = mulK (mulK a b) c) /\
       (!a b:A. mulK a b = mulK b a) /\
       (!a:A. mulK oneK a = a) /\
       (!a:A. mulK zeroK a = zeroK) /\
       invK zeroK = zeroK /\
       (!a:A. ~(a = zeroK) ==> mulK a (invK a) = oneK) /\
       (!a b c:A.
          mulK a (addK b c) = addK (mulK a b) (mulK a c)) /\
       normK zeroK = &0 /\
       (!a:A. &0 <= normK a) /\
       (!a:A. normK a = &0 <=> a = zeroK) /\
       (!a:A. normK (negK a) = normK a) /\
       (!a b:A. normK (addK a b) <= normK a + normK b) /\
       (!a b:A. normK (mulK a b) = normK a * normK b) /\
       (?a:A. &1 < normK a) in
  let normed_space_E =
    \(zeroE:B) (addE:B->B->B) (negE:B->B)
     (smulE:A->B->B) (normE:B->real).
       (!x y z:B. addE x (addE y z) = addE (addE x y) z) /\
       (!x y:B. addE x y = addE y x) /\
       (!x:B. addE zeroE x = x) /\
       (!x:B. addE (negE x) x = zeroE) /\
       (!x:B. smulE oneK x = x) /\
       (!a b:A. !x:B.
          smulE (mulK a b) x = smulE a (smulE b x)) /\
       (!a b:A. !x:B.
          smulE (addK a b) x = addE (smulE a x) (smulE b x)) /\
       (!a:A. !x y:B.
          smulE a (addE x y) = addE (smulE a x) (smulE a y)) /\
       (!x:B. smulE zeroK x = zeroE) /\
       (!a:A. smulE a zeroE = zeroE) /\
       normE zeroE = &0 /\
       (!x:B. &0 <= normE x) /\
       (!x:B. normE x = &0 <=> x = zeroE) /\
       (!x:B. normE (negE x) = normE x) /\
       (!a:A. !x:B. normE (smulE a x) = normK a * normE x) /\
       (!x y:B. normE (addE x y) <= normE x + normE y) in
  let normed_space_F =
    \(zeroF:C) (addF:C->C->C) (negF:C->C)
     (smulF:A->C->C) (normF:C->real).
       (!x y z:C. addF x (addF y z) = addF (addF x y) z) /\
       (!x y:C. addF x y = addF y x) /\
       (!x:C. addF zeroF x = x) /\
       (!x:C. addF (negF x) x = zeroF) /\
       (!x:C. smulF oneK x = x) /\
       (!a b:A. !x:C.
          smulF (mulK a b) x = smulF a (smulF b x)) /\
       (!a b:A. !x:C.
          smulF (addK a b) x = addF (smulF a x) (smulF b x)) /\
       (!a:A. !x y:C.
          smulF a (addF x y) = addF (smulF a x) (smulF a y)) /\
       (!x:C. smulF zeroK x = zeroF) /\
       (!a:A. smulF a zeroF = zeroF) /\
       normF zeroF = &0 /\
       (!x:C. &0 <= normF x) /\
       (!x:C. normF x = &0 <=> x = zeroF) /\
       (!x:C. normF (negF x) = normF x) /\
       (!a:A. !x:C. normF (smulF a x) = normK a * normF x) /\
       (!x y:C. normF (addF x y) <= normF x + normF y) in
  let tends_E =
    \(u:num->B) (x:B).
       !epsilon:real.
         &0 < epsilon
         ==> ?N:num. !n:num.
               N <= n
               ==> normE (addE (u n) (negE x)) < epsilon in
  let complete_space_E =
    !u:num->B.
       (!epsilon:real.
          &0 < epsilon
          ==> ?N:num. !m n:num.
                N <= m /\ N <= n
                ==> normE (addE (u m) (negE (u n))) < epsilon)
       ==> ?x:B. tends_E u x in
  let continuous_linear_map_EF =
    \l:B->C.
       (!x y:B. l (addE x y) = addF (l x) (l y)) /\
       (!a:A. !x:B. l (smulE a x) = smulF a (l x)) /\
       (?bound:real.
          &0 <= bound /\
          !x:B. normF (l x) <= bound * normE x) in
  let continuous_linear_map_FE =
    \l:C->B.
       (!x y:C. l (addF x y) = addE (l x) (l y)) /\
       (!a:A. !x:C. l (smulF a x) = smulE a (l x)) /\
       (?bound:real.
          &0 <= bound /\
          !x:C. normE (l x) <= bound * normF x) in
  let has_strict_fderiv_at_EF =
    \(f:B->C) (l:B->C) (point:B).
       !epsilon:real.
         &0 < epsilon
         ==> ?radius:real.
               &0 < radius /\
               !x y:B.
                 normE (addE x (negE point)) < radius /\
                 normE (addE y (negE point)) < radius
                 ==> normF
                       (addF
                         (addF (f x) (negF (f y)))
                         (negF (l (addE x (negE y)))))
                     <= epsilon * normE (addE x (negE y)) in
  let has_strict_fderiv_at_FE =
    \(g:C->B) (l:C->B) (point:C).
       !epsilon:real.
         &0 < epsilon
         ==> ?radius:real.
               &0 < radius /\
               !x y:C.
                 normF (addF x (negF point)) < radius /\
                 normF (addF y (negF point)) < radius
                 ==> normE
                       (addE
                         (addE (g x) (negE (g y)))
                         (negE (l (addF x (negF y)))))
                     <= epsilon * normF (addF x (negF y)) in
  let local_inverse_at =
    \(f:B->C) (g:C->B) (point:B).
       (?source_radius:real.
          &0 < source_radius /\
          !x:B.
            normE (addE x (negE point)) < source_radius
            ==> g (f x) = x) /\
       (?target_radius:real.
          &0 < target_radius /\
          !y:C.
            normF (addF y (negF (f point))) < target_radius
            ==> f (g y) = y) in
    nontrivially_normed_field
      zeroK oneK addK mulK negK invK normK /\
    normed_space_E zeroE addE negE smulE normE /\
    normed_space_F zeroF addF negF smulF normF /\
    complete_space_E /\
    continuous_linear_map_EF derivative /\
    continuous_linear_map_FE inverse_derivative /\
    (!x:B. inverse_derivative (derivative x) = x) /\
    (!y:C. derivative (inverse_derivative y) = y) /\
    has_strict_fderiv_at_EF f derivative point
    ==> ?local_inverse:C->B.
          local_inverse_at f local_inverse point /\
          has_strict_fderiv_at_FE
            local_inverse inverse_derivative (f point)`;;
