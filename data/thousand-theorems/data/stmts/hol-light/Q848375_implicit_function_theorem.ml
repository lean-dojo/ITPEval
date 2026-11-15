(*
  Statement-only formalization of Thousand Theorems corpus artifact Q848375
  (thousand-theorems__hol-light__Q848375), "Implicit function theorem":
  implicit-function data over complete normed spaces, with strict derivatives,
  surjective derivatives, and complementary kernels, determines an associated
  local open partial homeomorphism whose inverse curries to the implicit
  function. This file contains no proof.
*)

let Q848375_IMPLICIT_FUNCTION =
 `let normed_field =
    \(zeroK:K) (oneK:K) (addK:K->K->K) (mulK:K->K->K)
     (negK:K->K) (invK:K->K) (normK:K->real).
       ~(zeroK = oneK) /\
       (!a b c:K. addK a (addK b c) = addK (addK a b) c) /\
       (!a b:K. addK a b = addK b a) /\
       (!a:K. addK zeroK a = a) /\
       (!a:K. addK (negK a) a = zeroK) /\
       (!a b c:K. mulK a (mulK b c) = mulK (mulK a b) c) /\
       (!a b:K. mulK a b = mulK b a) /\
       (!a:K. mulK oneK a = a) /\
       invK zeroK = zeroK /\
       (!a:K. ~(a = zeroK) ==> mulK (invK a) a = oneK) /\
       (!a b c:K.
          mulK a (addK b c) = addK (mulK a b) (mulK a c)) /\
       normK zeroK = &0 /\
       (!a:K. &0 <= normK a) /\
       (!a:K. normK a = &0 <=> a = zeroK) /\
       (!a:K. normK (negK a) = normK a) /\
       (!a b:K. normK (addK a b) <= normK a + normK b) /\
       (!a b:K. normK (mulK a b) = normK a * normK b) /\
       (?a:K. &1 < normK a) in
  let normed_space_E =
    \(zeroK:K) (oneK:K) (addK:K->K->K) (mulK:K->K->K)
     (normK:K->real) (zeroE:A) (addE:A->A->A) (negE:A->A)
     (smulE:K->A->A) (normE:A->real).
       (!x y z:A. addE x (addE y z) = addE (addE x y) z) /\
       (!x y:A. addE x y = addE y x) /\
       (!x:A. addE zeroE x = x) /\
       (!x:A. addE (negE x) x = zeroE) /\
       (!x:A. smulE oneK x = x) /\
       (!a b:K. !x:A.
          smulE (mulK a b) x = smulE a (smulE b x)) /\
       (!a b:K. !x:A.
          smulE (addK a b) x = addE (smulE a x) (smulE b x)) /\
       (!a:K. !x y:A.
          smulE a (addE x y) = addE (smulE a x) (smulE a y)) /\
       (!x:A. smulE zeroK x = zeroE) /\
       (!a:K. smulE a zeroE = zeroE) /\
       normE zeroE = &0 /\
       (!x:A. &0 <= normE x) /\
       (!x:A. normE x = &0 <=> x = zeroE) /\
       (!x:A. normE (negE x) = normE x) /\
       (!x y:A. normE (addE x y) <= normE x + normE y) /\
       (!a:K. !x:A. normE (smulE a x) = normK a * normE x) in
  let normed_space_F =
    \(zeroK:K) (oneK:K) (addK:K->K->K) (mulK:K->K->K)
     (normK:K->real) (zeroF:B) (addF:B->B->B) (negF:B->B)
     (smulF:K->B->B) (normF:B->real).
       (!x y z:B. addF x (addF y z) = addF (addF x y) z) /\
       (!x y:B. addF x y = addF y x) /\
       (!x:B. addF zeroF x = x) /\
       (!x:B. addF (negF x) x = zeroF) /\
       (!x:B. smulF oneK x = x) /\
       (!a b:K. !x:B.
          smulF (mulK a b) x = smulF a (smulF b x)) /\
       (!a b:K. !x:B.
          smulF (addK a b) x = addF (smulF a x) (smulF b x)) /\
       (!a:K. !x y:B.
          smulF a (addF x y) = addF (smulF a x) (smulF a y)) /\
       (!x:B. smulF zeroK x = zeroF) /\
       (!a:K. smulF a zeroF = zeroF) /\
       normF zeroF = &0 /\
       (!x:B. &0 <= normF x) /\
       (!x:B. normF x = &0 <=> x = zeroF) /\
       (!x:B. normF (negF x) = normF x) /\
       (!x y:B. normF (addF x y) <= normF x + normF y) /\
       (!a:K. !x:B. normF (smulF a x) = normK a * normF x) in
  let normed_space_G =
    \(zeroK:K) (oneK:K) (addK:K->K->K) (mulK:K->K->K)
     (normK:K->real) (zeroG:C) (addG:C->C->C) (negG:C->C)
     (smulG:K->C->C) (normG:C->real).
       (!x y z:C. addG x (addG y z) = addG (addG x y) z) /\
       (!x y:C. addG x y = addG y x) /\
       (!x:C. addG zeroG x = x) /\
       (!x:C. addG (negG x) x = zeroG) /\
       (!x:C. smulG oneK x = x) /\
       (!a b:K. !x:C.
          smulG (mulK a b) x = smulG a (smulG b x)) /\
       (!a b:K. !x:C.
          smulG (addK a b) x = addG (smulG a x) (smulG b x)) /\
       (!a:K. !x y:C.
          smulG a (addG x y) = addG (smulG a x) (smulG a y)) /\
       (!x:C. smulG zeroK x = zeroG) /\
       (!a:K. smulG a zeroG = zeroG) /\
       normG zeroG = &0 /\
       (!x:C. &0 <= normG x) /\
       (!x:C. normG x = &0 <=> x = zeroG) /\
       (!x:C. normG (negG x) = normG x) /\
       (!x y:C. normG (addG x y) <= normG x + normG y) /\
       (!a:K. !x:C. normG (smulG a x) = normK a * normG x) in
  let complete_E =
    \(addE:A->A->A) (negE:A->A) (normE:A->real).
       !u:num->A.
         (!epsilon:real.
            &0 < epsilon
            ==> ?N:num.
                  !m n:num.
                    N <= m /\ N <= n
                    ==> normE (addE (u m) (negE (u n))) < epsilon)
         ==> ?x:A.
               !epsilon:real.
                 &0 < epsilon
                 ==> ?N:num.
                       !n:num.
                         N <= n
                         ==> normE (addE (u n) (negE x)) < epsilon in
  let complete_F =
    \(addF:B->B->B) (negF:B->B) (normF:B->real).
       !u:num->B.
         (!epsilon:real.
            &0 < epsilon
            ==> ?N:num.
                  !m n:num.
                    N <= m /\ N <= n
                    ==> normF (addF (u m) (negF (u n))) < epsilon)
         ==> ?x:B.
               !epsilon:real.
                 &0 < epsilon
                 ==> ?N:num.
                       !n:num.
                         N <= n
                         ==> normF (addF (u n) (negF x)) < epsilon in
  let complete_G =
    \(addG:C->C->C) (negG:C->C) (normG:C->real).
       !u:num->C.
         (!epsilon:real.
            &0 < epsilon
            ==> ?N:num.
                  !m n:num.
                    N <= m /\ N <= n
                    ==> normG (addG (u m) (negG (u n))) < epsilon)
         ==> ?x:C.
               !epsilon:real.
                 &0 < epsilon
                 ==> ?N:num.
                       !n:num.
                         N <= n
                         ==> normG (addG (u n) (negG x)) < epsilon in
  let subE =
    \(addE:A->A->A) (negE:A->A) (x:A) (y:A).
       addE x (negE y) in
  let subF =
    \(addF:B->B->B) (negF:B->B) (x:B) (y:B).
       addF x (negF y) in
  let subG =
    \(addG:C->C->C) (negG:C->C) (x:C) (y:C).
       addG x (negG y) in
  let continuous_linear_EF =
    \(addE:A->A->A) (smulE:K->A->A) (normE:A->real)
     (addF:B->B->B) (smulF:K->B->B) (normF:B->real)
     (L:A->B).
       (!x y:A. L (addE x y) = addF (L x) (L y)) /\
       (!a:K. !x:A. L (smulE a x) = smulF a (L x)) /\
       (?bound:real.
          &0 <= bound /\
          !x:A. normF (L x) <= bound * normE x) in
  let continuous_linear_EG =
    \(addE:A->A->A) (smulE:K->A->A) (normE:A->real)
     (addG:C->C->C) (smulG:K->C->C) (normG:C->real)
     (L:A->C).
       (!x y:A. L (addE x y) = addG (L x) (L y)) /\
       (!a:K. !x:A. L (smulE a x) = smulG a (L x)) /\
       (?bound:real.
          &0 <= bound /\
          !x:A. normG (L x) <= bound * normE x) in
  let has_strict_fderiv_left =
    \(addE:A->A->A) (negE:A->A) (smulE:K->A->A)
     (normE:A->real) (addF:B->B->B) (negF:B->B)
     (smulF:K->B->B) (normF:B->real)
     (f:A->B) (f':A->B) (a:A).
       continuous_linear_EF
         addE smulE normE addF smulF normF f' /\
       !epsilon:real.
         &0 < epsilon
         ==> ?delta:real.
               &0 < delta /\
               !x y:A.
                 normE (subE addE negE x a) < delta /\
                 normE (subE addE negE y a) < delta
                 ==> normF
                       (subF addF negF
                         (subF addF negF (f x) (f y))
                         (f' (subE addE negE x y)))
                     <= epsilon * normE (subE addE negE x y) in
  let has_strict_fderiv_right =
    \(addE:A->A->A) (negE:A->A) (smulE:K->A->A)
     (normE:A->real) (addG:C->C->C) (negG:C->C)
     (smulG:K->C->C) (normG:C->real)
     (g:A->C) (g':A->C) (a:A).
       continuous_linear_EG
         addE smulE normE addG smulG normG g' /\
       !epsilon:real.
         &0 < epsilon
         ==> ?delta:real.
               &0 < delta /\
               !x y:A.
                 normE (subE addE negE x a) < delta /\
                 normE (subE addE negE y a) < delta
                 ==> normG
                       (subG addG negG
                         (subG addG negG (g x) (g y))
                         (g' (subE addE negE x y)))
                     <= epsilon * normE (subE addE negE x y) in
  let complementary_kernels =
    \(zeroE:A) (addE:A->A->A) (zeroF:B) (zeroG:C)
     (f':A->B) (g':A->C).
       (!x:A.
          ?u v:A.
            f' u = zeroF /\
            g' v = zeroG /\
            x = addE u v) /\
       (!x:A.
          f' x = zeroF /\ g' x = zeroG
          ==> x = zeroE) in
  let open_E =
    \(addE:A->A->A) (negE:A->A) (normE:A->real)
     (s:A->bool).
       !x:A.
         x IN s
         ==> ?radius:real.
               &0 < radius /\
               !y:A.
                 normE (subE addE negE y x) < radius
                 ==> y IN s in
  let open_FG =
    \(addF:B->B->B) (negF:B->B) (normF:B->real)
     (addG:C->C->C) (negG:C->C) (normG:C->real)
     (s:(B#C)->bool).
       !p:B#C.
         p IN s
         ==> ?radius:real.
               &0 < radius /\
               !q:B#C.
                 normF (subF addF negF (FST q) (FST p)) < radius /\
                 normG (subG addG negG (SND q) (SND p)) < radius
                 ==> q IN s in
  let continuous_prod_on =
    \(addE:A->A->A) (negE:A->A) (normE:A->real)
     (addF:B->B->B) (negF:B->B) (normF:B->real)
     (addG:C->C->C) (negG:C->C) (normG:C->real)
     (f:A->B) (g:A->C) (s:A->bool).
       !x:A.
         x IN s
         ==> !epsilon:real.
               &0 < epsilon
               ==> ?delta:real.
                     &0 < delta /\
                     !y:A.
                       y IN s /\
                       normE (subE addE negE y x) < delta
                       ==> normF (subF addF negF (f y) (f x)) < epsilon /\
                           normG (subG addG negG (g y) (g x)) < epsilon in
  let continuous_inverse_on =
    \(addE:A->A->A) (negE:A->A) (normE:A->real)
     (addF:B->B->B) (negF:B->B) (normF:B->real)
     (addG:C->C->C) (negG:C->C) (normG:C->real)
     (h:(B#C)->A) (s:(B#C)->bool).
       !p:B#C.
         p IN s
         ==> !epsilon:real.
               &0 < epsilon
               ==> ?delta:real.
                     &0 < delta /\
                     !q:B#C.
                       q IN s /\
                       normF
                         (subF addF negF (FST q) (FST p)) < delta /\
                       normG
                         (subG addG negG (SND q) (SND p)) < delta
                       ==> normE
                             (subE addE negE (h q) (h p)) < epsilon in
  !zeroK oneK:K.
  !addK mulK:K->K->K.
  !negK invK:K->K.
  !normK:K->real.
  !zeroE:A.
  !addE:A->A->A.
  !negE:A->A.
  !smulE:K->A->A.
  !normE:A->real.
  !zeroF:B.
  !addF:B->B->B.
  !negF:B->B.
  !smulF:K->B->B.
  !normF:B->real.
  !zeroG:C.
  !addG:C->C->C.
  !negG:C->C.
  !smulG:K->C->C.
  !normG:C->real.
  !leftFun:A->B.
  !leftDeriv:A->B.
  !rightFun:A->C.
  !rightDeriv:A->C.
  !pt:A.
    normed_field zeroK oneK addK mulK negK invK normK /\
    normed_space_E
      zeroK oneK addK mulK normK
      zeroE addE negE smulE normE /\
    normed_space_F
      zeroK oneK addK mulK normK
      zeroF addF negF smulF normF /\
    normed_space_G
      zeroK oneK addK mulK normK
      zeroG addG negG smulG normG /\
    complete_E addE negE normE /\
    complete_F addF negF normF /\
    complete_G addG negG normG /\
    has_strict_fderiv_left
      addE negE smulE normE
      addF negF smulF normF
      leftFun leftDeriv pt /\
    has_strict_fderiv_right
      addE negE smulE normE
      addG negG smulG normG
      rightFun rightDeriv pt /\
    (!y:B. ?x:A. leftDeriv x = y) /\
    (!z:C. ?x:A. rightDeriv x = z) /\
    complementary_kernels
      zeroE addE zeroF zeroG leftDeriv rightDeriv
    ==> ?source:A->bool.
        ?target:(B#C)->bool.
        ?localInverse:(B#C)->A.
        ?implicitFunction:B->C->A.
          open_E addE negE normE source /\
          open_FG addF negF normF addG negG normG target /\
          pt IN source /\
          (leftFun pt,rightFun pt) IN target /\
          continuous_prod_on
            addE negE normE
            addF negF normF
            addG negG normG
            leftFun rightFun source /\
          continuous_inverse_on
            addE negE normE
            addF negF normF
            addG negG normG
            localInverse target /\
          (!x:A.
             x IN source
             ==> (leftFun x,rightFun x) IN target /\
                 localInverse (leftFun x,rightFun x) = x) /\
          (!p:B#C.
             p IN target
             ==> localInverse p IN source /\
                 leftFun (localInverse p) = FST p /\
                 rightFun (localInverse p) = SND p) /\
          (!y:B. !z:C.
             implicitFunction y z = localInverse (y,z))`;;
