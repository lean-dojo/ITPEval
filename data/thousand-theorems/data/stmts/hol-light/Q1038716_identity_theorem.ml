(*
  Statement-only formalization of Thousand Theorems corpus artifact Q1038716,
  "Identity theorem": two functions analytic on a preconnected set over an
  arbitrary nontrivially normed field, with values in a normed vector space,
  agree throughout the set if their coincidence points accumulate at a point
  of the set. This file contains no proof.
*)

let Q1038716_IDENTITY_THEOREM =
 `let nontrivially_normed_field =
    \(zeroK:A) (oneK:A)
     (addK:A->A->A) (mulK:A->A->A)
     (negK:A->A) (invK:A->A) (normK:A->real).
       ~(zeroK = oneK) /\
       (!a b c. addK a (addK b c) = addK (addK a b) c) /\
       (!a b. addK a b = addK b a) /\
       (!a. addK zeroK a = a) /\
       (!a. addK (negK a) a = zeroK) /\
       (!a b c. mulK a (mulK b c) = mulK (mulK a b) c) /\
       (!a b. mulK a b = mulK b a) /\
       (!a. mulK oneK a = a) /\
       (!a. mulK zeroK a = zeroK) /\
       invK zeroK = zeroK /\
       (!a. ~(a = zeroK) ==> mulK a (invK a) = oneK) /\
       (!a b c. mulK a (addK b c) =
                  addK (mulK a b) (mulK a c)) /\
       normK zeroK = &0 /\
       (!a. &0 <= normK a) /\
       (!a. normK a = &0 <=> a = zeroK) /\
       (!a b. normK (addK a b) <= normK a + normK b) /\
       (!a b. normK (mulK a b) = normK a * normK b) /\
       (?a. &1 < normK a) in
  let normed_add_comm_group =
    \(zeroE:B) (addE:B->B->B) (negE:B->B) (normE:B->real).
       (!x y z. addE x (addE y z) = addE (addE x y) z) /\
       (!x y. addE x y = addE y x) /\
       (!x. addE zeroE x = x) /\
       (!x. addE (negE x) x = zeroE) /\
       normE zeroE = &0 /\
       (!x. &0 <= normE x) /\
       (!x. normE x = &0 <=> x = zeroE) /\
       (!x. normE (negE x) = normE x) /\
       (!x y. normE (addE x y) <= normE x + normE y) in
  let normed_space =
    \(zeroK:A) (oneK:A)
     (addK:A->A->A) (mulK:A->A->A) (normK:A->real)
     (zeroE:B) (addE:B->B->B) (normE:B->real)
     (smul:A->B->B).
       (!x. smul oneK x = x) /\
       (!a b x. smul (mulK a b) x = smul a (smul b x)) /\
       (!a x y. smul a (addE x y) =
                  addE (smul a x) (smul a y)) /\
       (!a b x. smul (addK a b) x =
                  addE (smul a x) (smul b x)) /\
       (!a. smul a zeroE = zeroE) /\
       (!x. smul zeroK x = zeroE) /\
       (!a x. normE (smul a x) = normK a * normE x) in
  let subK =
    \(addK:A->A->A) (negK:A->A) x y. addK x (negK y) in
  let subE =
    \(addE:B->B->B) (negE:B->B) x y. addE x (negE y) in
  let power =
    \(mulK:A->A->A) (oneK:A) (z:A) (n:num).
       ((@p:num->A.
           p 0 = oneK /\
           (!m. p (SUC m) = mulK z (p m))) n) in
  let partial_sum =
    \(addE:B->B->B) (zeroE:B) (term:num->B) (n:num).
       ((@s:num->B.
           s 0 = zeroE /\
           (!m. s (SUC m) = addE (s m) (term m))) n) in
  let tends_to =
    \(normE:B->real) (subE:B->B->B) (u:num->B) (l:B).
       !eps. &0 < eps
             ==> ?N. !n. N <= n ==> normE (subE (u n) l) < eps in
  let open_in_norm =
    \(normK:A->real) (subK:A->A->A) (s:A->bool).
       !x. x IN s
           ==> ?eps. &0 < eps /\
                     !y. normK (subK y x) < eps ==> y IN s in
  let preconnected =
    \(normK:A->real) (subK:A->A->A) (U:A->bool).
       !s t:A->bool.
         open_in_norm normK subK s /\
         open_in_norm normK subK t /\
         U SUBSET (s UNION t) /\
         DISJOINT (U INTER s) (U INTER t)
         ==> U INTER s = {} \/ U INTER t = {} in
  let analytic_at =
    \(mulK:A->A->A) (oneK:A) (normK:A->real)
     (addE:B->B->B) (zeroE:B) (normE:B->real)
     (smul:A->B->B) (subK:A->A->A) (subE:B->B->B)
     (f:A->B) (x:A).
       ?coeff:num->B. ?radius:real.
         &0 < radius /\
         !z. normK (subK z x) < radius
             ==> tends_to normE subE
                   (\n. partial_sum addE zeroE
                          (\m. smul (power mulK oneK (subK z x) m)
                                    (coeff m))
                          n)
                   (f z) in
  let analytic_on_nhd =
    \(mulK:A->A->A) (oneK:A) (normK:A->real)
     (addE:B->B->B) (zeroE:B) (normE:B->real)
     (smul:A->B->B) (subK:A->A->A) (subE:B->B->B)
     (f:A->B) (U:A->bool).
       !x. x IN U
           ==> analytic_at mulK oneK normK addE zeroE normE
                 smul subK subE f x in
  let frequently_equal_near =
    \(normK:A->real) (subK:A->A->A)
     (f:A->B) (g:A->B) (z0:A).
       !eps. &0 < eps
             ==> ?z. ~(z = z0) /\
                     normK (subK z z0) < eps /\
                     f z = g z in
  !zeroK oneK:A.
  !addK mulK:A->A->A.
  !negK invK:A->A.
  !normK:A->real.
  !zeroE:B.
  !addE:B->B->B.
  !negE:B->B.
  !normE:B->real.
  !smul:A->B->B.
  !f g:A->B.
  !U:A->bool.
  !z0:A.
    nontrivially_normed_field
      zeroK oneK addK mulK negK invK normK /\
    normed_add_comm_group zeroE addE negE normE /\
    normed_space
      zeroK oneK addK mulK normK zeroE addE normE smul /\
    analytic_on_nhd
      mulK oneK normK addE zeroE normE smul
      (subK addK negK) (subE addE negE) f U /\
    analytic_on_nhd
      mulK oneK normK addE zeroE normE smul
      (subK addK negK) (subE addE negE) g U /\
    preconnected normK (subK addK negK) U /\
    z0 IN U /\
    frequently_equal_near normK (subK addK negK) f g z0
    ==> !z. z IN U ==> f z = g z`;;
