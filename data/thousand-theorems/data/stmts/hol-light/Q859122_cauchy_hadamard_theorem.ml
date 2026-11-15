(*
  Statement-only formalization of Thousand Theorems corpus artifact Q859122
  (thousand-theorems__hol-light__Q859122), "Cauchy-Hadamard theorem": for a
  formal multilinear series over an arbitrary nontrivially normed field, the
  inverse of its convergence radius is the extended-nonnegative limsup of the
  nth roots of its coefficient operator norms. This file contains no proof.
*)

let Q859122_CAUCHY_HADAMARD_THEOREM =
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
    \(zeroK:A) (oneK:A) (addK:A->A->A) (mulK:A->A->A)
     (normK:A->real) (zero:C) (add:C->C->C) (norm:C->real)
     (smul:A->C->C).
       (!x:C. smul oneK x = x) /\
       (!a b:A. !x:C.
          smul (mulK a b) x = smul a (smul b x)) /\
       (!a b:A. !x:C.
          smul (addK a b) x = add (smul a x) (smul b x)) /\
       (!a:A. !x y:C.
          smul a (add x y) = add (smul a x) (smul a y)) /\
       (!a:A. smul a zero = zero) /\
       (!x:C. smul zeroK x = zero) /\
       (!a:A. !x:C. norm (smul a x) = normK a * norm x) in
  let coordinate_extensional =
    \(q:(num->B)->C) (n:num).
       !x y:num->B.
         (!i:num. i < n ==> x i = y i) ==> q x = q y in
  let multilinear =
    \(addE:B->B->B) (smulE:A->B->B)
     (addF:C->C->C) (smulF:A->C->C)
     (q:(num->B)->C) (n:num).
       (!x:num->B i:num u v:B.
          i < n
          ==> q (\j. if j = i then addE u v else x j) =
              addF
                (q (\j. if j = i then u else x j))
                (q (\j. if j = i then v else x j))) /\
       (!x:num->B i:num a:A u:B.
          i < n
          ==> q (\j. if j = i then smulE a u else x j) =
              smulF a (q (\j. if j = i then u else x j))) in
  let operator_bound =
    \(normE:B->real) (normF:C->real)
     (q:(num->B)->C) (n:num) (M:real).
      !x:num->B.
        normF (q x) <=
        M * product {i:num | i < n} (\i. normE (x i)) in
  let formal_multilinear_series =
    \(addE:B->B->B) (smulE:A->B->B) (normE:B->real)
     (addF:C->C->C) (smulF:A->C->C) (normF:C->real)
     (p:num->(num->B)->C).
       !n:num.
         coordinate_extensional (p n) n /\
         multilinear addE smulE addF smulF (p n) n /\
         ?M:real.
           &0 <= M /\ operator_bound normE normF (p n) n M in
  let operator_norm =
    \(normE:B->real) (normF:C->real)
     (p:num->(num->B)->C) (n:num).
       @r:real.
         &0 <= r /\
         operator_bound normE normF (p n) n r /\
         (!M:real.
            &0 <= M /\ operator_bound normE normF (p n) n M
            ==> r <= M) in
  let enonnegative =
    \(z:bool#real).
       (FST z /\ SND z = &0) \/
       (~(FST z) /\ &0 <= SND z) in
  let ele =
    \(x:bool#real) (y:bool#real).
       FST y \/ (~(FST x) /\ SND x <= SND y) in
  let esupremum =
    \(s:(bool#real)->bool) (z:bool#real).
       enonnegative z /\
       (!x:bool#real. s x ==> enonnegative x /\ ele x z) /\
       (!w:bool#real.
          enonnegative w /\
          (!x:bool#real. s x ==> ele x w)
          ==> ele z w) in
  let einfimum =
    \(s:(bool#real)->bool) (z:bool#real).
       enonnegative z /\
       (!x:bool#real. s x ==> enonnegative x /\ ele z x) /\
       (!w:bool#real.
          enonnegative w /\
          (!x:bool#real. s x ==> ele w x)
          ==> ele w z) in
  let einverse =
    \(z:bool#real).
       if FST z then (F,&0)
       else if SND z = &0 then (T,&0)
       else (F,inv(SND z)) in
  let radius_value =
    \(normE:B->real) (normF:C->real)
     (p:num->(num->B)->C) (radius:bool#real).
       esupremum
         (\z:bool#real.
            ?r:real.
              z = (F,r) /\
              &0 <= r /\
              ?M:real.
                !n:num.
                  operator_norm normE normF p n * r pow n <= M)
         radius in
  let nth_root =
    \(c:real) (n:num).
       if n = 0 then &1
       else @x:real. &0 <= x /\ x pow n = c in
  let extended_limsup =
    \(u:num->bool#real) (z:bool#real).
       einfimum
         (\b:bool#real.
            enonnegative b /\
            ?N:num. !n:num. N <= n ==> ele (u n) b)
         z in
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
  !p:num->(num->B)->C.
    nontrivially_normed_field
      zeroK oneK addK mulK negK invK normK /\
    normed_add_comm_group zeroE addE negE normE /\
    normed_add_comm_group' zeroF addF negF normF /\
    normed_space
      zeroK oneK addK mulK normK zeroE addE normE smulE /\
    normed_space'
      zeroK oneK addK mulK normK zeroF addF normF smulF /\
    formal_multilinear_series
      addE smulE normE addF smulF normF p
    ==>
    !radius limsup:bool#real.
      radius_value normE normF p radius /\
      extended_limsup
        (\n:num.
           (F,nth_root (operator_norm normE normF p n) n))
        limsup
      ==> einverse radius = limsup`;;
