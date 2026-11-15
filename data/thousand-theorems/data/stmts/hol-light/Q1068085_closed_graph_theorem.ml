(*
  Statement-only formalization of Thousand Theorems corpus artifact Q1068085,
  "Closed graph theorem": a linear map between arbitrary Banach spaces over a
  nontrivially normed field is continuous when its graph is closed. This file
  contains no proof.
*)

let Q1068085_CLOSED_GRAPH_THEOREM =
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
       (!a:A. normK (negK a) = normK a) /\
       (!a b:A. normK (addK a b) <= normK a + normK b) /\
       (!a b:A. normK (mulK a b) = normK a * normK b) /\
       (?a:A. &1 < normK a) in
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
       (!a b:A x:B. smul (mulK a b) x = smul a (smul b x)) /\
       (!a:A x y:B.
          smul a (add x y) = add (smul a x) (smul a y)) /\
       (!a b:A x:B.
          smul (addK a b) x = add (smul a x) (smul b x)) /\
       (!a:A. smul a zero = zero) /\
       (!x:B. smul zeroK x = zero) /\
       (!a:A x:B. norm (smul a x) = normK a * norm x) in
  let normed_space' =
    \(zeroK:A) (oneK:A) (addK:A->A->A) (mulK:A->A->A)
     (normK:A->real) (zero:C) (add:C->C->C) (norm:C->real)
     (smul:A->C->C).
       (!x:C. smul oneK x = x) /\
       (!a b:A x:C. smul (mulK a b) x = smul a (smul b x)) /\
       (!a:A x y:C.
          smul a (add x y) = add (smul a x) (smul a y)) /\
       (!a b:A x:C.
          smul (addK a b) x = add (smul a x) (smul b x)) /\
       (!a:A. smul a zero = zero) /\
       (!x:C. smul zeroK x = zero) /\
       (!a:A x:C. norm (smul a x) = normK a * norm x) in
  let tends_to =
    \(add:B->B->B) (neg:B->B) (norm:B->real)
     (u:num->B) (x:B).
       !eps:real.
         &0 < eps
         ==> ?N:num. !n:num.
               N <= n ==> norm (add (u n) (neg x)) < eps in
  let tends_to' =
    \(add:C->C->C) (neg:C->C) (norm:C->real)
     (u:num->C) (x:C).
       !eps:real.
         &0 < eps
         ==> ?N:num. !n:num.
               N <= n ==> norm (add (u n) (neg x)) < eps in
  let complete_space =
    \(add:B->B->B) (neg:B->B) (norm:B->real).
       !u:num->B.
         (!eps:real.
            &0 < eps
            ==> ?N:num. !m n:num.
                  N <= m /\ N <= n
                  ==> norm (add (u m) (neg (u n))) < eps)
         ==> ?x:B. tends_to add neg norm u x in
  let complete_space' =
    \(add:C->C->C) (neg:C->C) (norm:C->real).
       !u:num->C.
         (!eps:real.
            &0 < eps
            ==> ?N:num. !m n:num.
                  N <= m /\ N <= n
                  ==> norm (add (u m) (neg (u n))) < eps)
         ==> ?x:C. tends_to' add neg norm u x in
  let linear_map =
    \(addE:B->B->B) (smulE:A->B->B)
     (addF:C->C->C) (smulF:A->C->C) (g:B->C).
       (!x y:B. g (addE x y) = addF (g x) (g y)) /\
       (!a:A x:B. g (smulE a x) = smulF a (g x)) in
  let graph_closed =
    \(addE:B->B->B) (negE:B->B) (normE:B->real)
     (addF:C->C->C) (negF:C->C) (normF:C->real)
     (g:B->C).
       !u:num->B. !v:num->C. !x:B. !y:C.
         (!n:num. v n = g (u n)) /\
         tends_to addE negE normE u x /\
         tends_to' addF negF normF v y
         ==> y = g x in
  let continuous =
    \(addE:B->B->B) (negE:B->B) (normE:B->real)
     (addF:C->C->C) (negF:C->C) (normF:C->real)
     (g:B->C).
       !x:B. !eps:real.
         &0 < eps
         ==> ?delta:real.
               &0 < delta /\
               !y:B.
                 normE (addE y (negE x)) < delta
                 ==> normF (addF (g y) (negF (g x))) < eps in
  !zeroK oneK:A.
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
  !g:B->C.
    nontrivially_normed_field
      zeroK oneK addK mulK negK invK normK /\
    normed_add_comm_group zeroE addE negE normE /\
    normed_add_comm_group' zeroF addF negF normF /\
    normed_space
      zeroK oneK addK mulK normK zeroE addE normE smulE /\
    normed_space'
      zeroK oneK addK mulK normK zeroF addF normF smulF /\
    complete_space addE negE normE /\
    complete_space' addF negF normF /\
    linear_map addE smulE addF smulF g /\
    graph_closed addE negE normE addF negF normF g
    ==> continuous addE negE normE addF negF normF g`;;
