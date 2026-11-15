(*
  Statement-only formalization of Thousand Theorems corpus artifact Q1426292,
  "Banach-Steinhaus theorem": a pointwise bounded family of continuous
  semilinear maps from an arbitrary complete seminormed space is uniformly
  bounded in operator norm. This file contains no proof.
*)

let Q1426292_BANACH_STEINHAUS_THEOREM =
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
  let seminormed_add_comm_group =
    \(zero:B) (add:B->B->B) (neg:B->B) (norm:B->real).
       (!x y z:B. add x (add y z) = add (add x y) z) /\
       (!x y:B. add x y = add y x) /\
       (!x:B. add zero x = x) /\
       (!x:B. add (neg x) x = zero) /\
       norm zero = &0 /\
       (!x:B. &0 <= norm x) /\
       (!x:B. norm (neg x) = norm x) /\
       (!x y:B. norm (add x y) <= norm x + norm y) in
  let seminormed_add_comm_group' =
    \(zero:C) (add:C->C->C) (neg:C->C) (norm:C->real).
       (!x y z:C. add x (add y z) = add (add x y) z) /\
       (!x y:C. add x y = add y x) /\
       (!x:C. add zero x = x) /\
       (!x:C. add (neg x) x = zero) /\
       norm zero = &0 /\
       (!x:C. &0 <= norm x) /\
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
  let tends_to =
    \(add:B->B->B) (neg:B->B) (norm:B->real)
     (u:num->B) (x:B).
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
  let continuous_semilinear_map =
    \(addE:B->B->B) (smulE:A->B->B) (normE:B->real)
     (addF:C->C->C) (smulF:D->C->C) (normF:C->real)
     (sigma:A->D) (g:B->C).
       (!x y:B. g (addE x y) = addF (g x) (g y)) /\
       (!a:A. !x:B. g (smulE a x) = smulF (sigma a) (g x)) /\
       (!epsilon:real.
          &0 < epsilon
          ==> ?delta:real.
                &0 < delta /\
                !x:B. normE x < delta ==> normF (g x) < epsilon) in
  !zeroK oneK:A.
  !addK mulK:A->A->A.
  !negK invK:A->A.
  !normK:A->real.
  !zeroL oneL:D.
  !addL mulL:D->D->D.
  !negL invL:D->D.
  !normL:D->real.
  !sigma:A->D.
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
  !indices:J->bool.
  !g:J->B->C.
    nontrivially_normed_field
      zeroK oneK addK mulK negK invK normK /\
    nontrivially_normed_field'
      zeroL oneL addL mulL negL invL normL /\
    seminormed_add_comm_group zeroE addE negE normE /\
    seminormed_add_comm_group' zeroF addF negF normF /\
    normed_space
      zeroK oneK addK mulK normK zeroE addE normE smulE /\
    normed_space'
      zeroL oneL addL mulL normL zeroF addF normF smulF /\
    isometric_ring_hom
      zeroK oneK addK mulK normK
      zeroL oneL addL mulL normL sigma /\
    complete_space addE negE normE /\
    (!i:J.
       i IN indices
       ==> continuous_semilinear_map
             addE smulE normE addF smulF normF sigma (g i)) /\
    (!x:B.
       ?C:real.
         &0 <= C /\
         !i:J. i IN indices ==> normF (g i x) <= C)
    ==> ?C':real.
          &0 <= C' /\
          !i:J.
            i IN indices
            ==> !x:B. normF (g i x) <= C' * normE x`;;
