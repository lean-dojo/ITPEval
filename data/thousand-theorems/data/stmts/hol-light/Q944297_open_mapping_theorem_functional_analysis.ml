(*
  Statement-only formalization of Thousand Theorems corpus artifact Q944297,
  "Open mapping theorem (functional analysis)": a surjective continuous
  semilinear map between Banach spaces over isometrically isomorphic
  nontrivially normed fields is an open map. This file contains no proof.
*)

let Q944297_OPEN_MAPPING_THEOREM_FUNCTIONAL_ANALYSIS =
 `let nontrivially_normed_field =
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
       (!a b:A. normK (addK a b) <= normK a + normK b) /\
       (!a b:A. normK (mulK a b) = normK a * normK b) /\
       (?a:A. &1 < normK a) in
  let nontrivially_normed_field' =
    \(zeroK:D) (oneK:D)
     (addK:D->D->D) (mulK:D->D->D)
     (negK:D->D) (invK:D->D) (normK:D->real).
       ~(zeroK = oneK) /\
       (!a b c:D. addK a (addK b c) = addK (addK a b) c) /\
       (!a b:D. addK a b = addK b a) /\
       (!a:D. addK zeroK a = a) /\
       (!a:D. addK (negK a) a = zeroK) /\
       (!a b c:D. mulK a (mulK b c) = mulK (mulK a b) c) /\
       (!a b:D. mulK a b = mulK b a) /\
       (!a:D. mulK oneK a = a) /\
       (!a:D. mulK zeroK a = zeroK) /\
       invK zeroK = zeroK /\
       (!a:D. ~(a = zeroK) ==> mulK a (invK a) = oneK) /\
       (!a b c:D.
          mulK a (addK b c) = addK (mulK a b) (mulK a c)) /\
       normK zeroK = &0 /\
       (!a:D. &0 <= normK a) /\
       (!a:D. normK a = &0 <=> a = zeroK) /\
       (!a b:D. normK (addK a b) <= normK a + normK b) /\
       (!a b:D. normK (mulK a b) = normK a * normK b) /\
       (?a:D. &1 < normK a) in
  let normed_add_comm_group =
    \(zero:B) (add:B->B->B) (neg:B->B) (norm:B->real).
       (!x y z:B. add x (add y z) = add (add x y) z) /\
       (!x y:B. add x y = add y x) /\
       (!x:B. add zero x = x) /\
       (!x:B. add (neg x) x = zero) /\
       norm zero = &0 /\
       (!x:B. &0 <= norm x) /\
       (!x:B. norm x = &0 <=> x = zero) /\
       (!x:B. norm (neg x) = norm x) /\
       (!x y:B. norm (add x y) <= norm x + norm y) in
  let normed_add_comm_group' =
    \(zero:C) (add:C->C->C) (neg:C->C) (norm:C->real).
       (!x y z:C. add x (add y z) = add (add x y) z) /\
       (!x y:C. add x y = add y x) /\
       (!x:C. add zero x = x) /\
       (!x:C. add (neg x) x = zero) /\
       norm zero = &0 /\
       (!x:C. &0 <= norm x) /\
       (!x:C. norm x = &0 <=> x = zero) /\
       (!x:C. norm (neg x) = norm x) /\
       (!x y:C. norm (add x y) <= norm x + norm y) in
  let normed_space =
    \(zeroK:A) (oneK:A) (addK:A->A->A) (mulK:A->A->A)
     (normK:A->real) (zero:B) (add:B->B->B) (norm:B->real)
     (smul:A->B->B).
       (!x:B. smul oneK x = x) /\
       (!a b:A. !x:B.
          smul (mulK a b) x = smul a (smul b x)) /\
       (!a b:A. !x:B.
          smul (addK a b) x = add (smul a x) (smul b x)) /\
       (!a:A. !x y:B.
          smul a (add x y) = add (smul a x) (smul a y)) /\
       (!a:A. smul a zero = zero) /\
       (!x:B. smul zeroK x = zero) /\
       (!a:A. !x:B. norm (smul a x) = normK a * norm x) in
  let normed_space' =
    \(zeroK:D) (oneK:D) (addK:D->D->D) (mulK:D->D->D)
     (normK:D->real) (zero:C) (add:C->C->C) (norm:C->real)
     (smul:D->C->C).
       (!x:C. smul oneK x = x) /\
       (!a b:D. !x:C.
          smul (mulK a b) x = smul a (smul b x)) /\
       (!a b:D. !x:C.
          smul (addK a b) x = add (smul a x) (smul b x)) /\
       (!a:D. !x y:C.
          smul a (add x y) = add (smul a x) (smul a y)) /\
       (!a:D. smul a zero = zero) /\
       (!x:C. smul zeroK x = zero) /\
       (!a:D. !x:C. norm (smul a x) = normK a * norm x) in
  let isometric_ring_hom =
    \(zeroK:A) (oneK:A) (addK:A->A->A) (mulK:A->A->A)
     (normK:A->real) (zeroL:D) (oneL:D)
     (addL:D->D->D) (mulL:D->D->D) (normL:D->real)
     (sigma:A->D).
       sigma zeroK = zeroL /\
       sigma oneK = oneL /\
       (!a b:A. sigma (addK a b) = addL (sigma a) (sigma b)) /\
       (!a b:A. sigma (mulK a b) = mulL (sigma a) (sigma b)) /\
       (!a:A. normL (sigma a) = normK a) in
  let isometric_ring_hom' =
    \(zeroK:D) (oneK:D) (addK:D->D->D) (mulK:D->D->D)
     (normK:D->real) (zeroL:A) (oneL:A)
     (addL:A->A->A) (mulL:A->A->A) (normL:A->real)
     (sigma:D->A).
       sigma zeroK = zeroL /\
       sigma oneK = oneL /\
       (!a b:D. sigma (addK a b) = addL (sigma a) (sigma b)) /\
       (!a b:D. sigma (mulK a b) = mulL (sigma a) (sigma b)) /\
       (!a:D. normL (sigma a) = normK a) in
  let ring_hom_inv_pair =
    \(sigma:A->D) (sigma':D->A).
       (!a:A. sigma' (sigma a) = a) /\
       (!b:D. sigma (sigma' b) = b) in
  let tends_to =
    \(add:B->B->B) (neg:B->B) (norm:B->real)
     (u:num->B) (x:B).
       !epsilon:real.
         &0 < epsilon
         ==> ?N:num. !n:num.
               N <= n
               ==> norm (add (u n) (neg x)) < epsilon in
  let tends_to' =
    \(add:C->C->C) (neg:C->C) (norm:C->real)
     (u:num->C) (x:C).
       !epsilon:real.
         &0 < epsilon
         ==> ?N:num. !n:num.
               N <= n
               ==> norm (add (u n) (neg x)) < epsilon in
  let complete_space =
    \(add:B->B->B) (neg:B->B) (norm:B->real).
       !u:num->B.
         (!epsilon:real.
            &0 < epsilon
            ==> ?N:num. !m n:num.
                  N <= m /\ N <= n
                  ==> norm (add (u m) (neg (u n))) < epsilon)
         ==> ?x:B. tends_to add neg norm u x in
  let complete_space' =
    \(add:C->C->C) (neg:C->C) (norm:C->real).
       !u:num->C.
         (!epsilon:real.
            &0 < epsilon
            ==> ?N:num. !m n:num.
                  N <= m /\ N <= n
                  ==> norm (add (u m) (neg (u n))) < epsilon)
         ==> ?x:C. tends_to' add neg norm u x in
  let continuous_semilinear_map =
    \(addE:B->B->B) (smulE:A->B->B) (normE:B->real)
     (addF:C->C->C) (smulF:D->C->C) (normF:C->real)
     (sigma:A->D) (f:B->C).
       (!x y:B. f (addE x y) = addF (f x) (f y)) /\
       (!a:A. !x:B. f (smulE a x) = smulF (sigma a) (f x)) /\
       (!epsilon:real.
          &0 < epsilon
          ==> ?delta:real.
                &0 < delta /\
                !x:B. normE x < delta ==> normF (f x) < epsilon) in
  let norm_open =
    \(add:B->B->B) (neg:B->B) (norm:B->real) (s:B->bool).
       !x:B.
         x IN s
         ==> ?epsilon:real.
               &0 < epsilon /\
               !y:B.
                 norm (add y (neg x)) < epsilon ==> y IN s in
  let norm_open' =
    \(add:C->C->C) (neg:C->C) (norm:C->real) (s:C->bool).
       !x:C.
         x IN s
         ==> ?epsilon:real.
               &0 < epsilon /\
               !y:C.
                 norm (add y (neg x)) < epsilon ==> y IN s in
  let is_open_map =
    \(addE:B->B->B) (negE:B->B) (normE:B->real)
     (addF:C->C->C) (negF:C->C) (normF:C->real)
     (f:B->C).
       !s:B->bool.
         norm_open addE negE normE s
         ==> norm_open' addF negF normF (IMAGE f s) in
  !zeroK oneK:A.
  !addK mulK:A->A->A.
  !negK invK:A->A.
  !normK:A->real.
  !zeroL oneL:D.
  !addL mulL:D->D->D.
  !negL invL:D->D.
  !normL:D->real.
  !sigma:A->D.
  !sigma':D->A.
  !zeroE:B.
  !addE:B->B->B.
  !negE:B->B.
  !smulE:A->B->B.
  !normE:B->real.
  !zeroF:C.
  !addF:C->C->C.
  !negF:C->C.
  !smulF:D->C->C.
  !normF:C->real.
  !f:B->C.
    nontrivially_normed_field
      zeroK oneK addK mulK negK invK normK /\
    nontrivially_normed_field'
      zeroL oneL addL mulL negL invL normL /\
    normed_add_comm_group zeroE addE negE normE /\
    normed_add_comm_group' zeroF addF negF normF /\
    normed_space
      zeroK oneK addK mulK normK zeroE addE normE smulE /\
    normed_space'
      zeroL oneL addL mulL normL zeroF addF normF smulF /\
    isometric_ring_hom
      zeroK oneK addK mulK normK
      zeroL oneL addL mulL normL sigma /\
    isometric_ring_hom'
      zeroL oneL addL mulL normL
      zeroK oneK addK mulK normK sigma' /\
    ring_hom_inv_pair sigma sigma' /\
    complete_space addE negE normE /\
    complete_space' addF negF normF /\
    continuous_semilinear_map
      addE smulE normE addF smulF normF sigma f /\
    (!y:C. ?x:B. f x = y)
    ==> is_open_map addE negE normE addF negF normF f`;;
