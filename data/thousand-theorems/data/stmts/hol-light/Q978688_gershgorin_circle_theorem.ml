(*
  Statement-only formalization of Thousand Theorems corpus artifact Q978688
  (thousand-theorems__hol-light__Q978688), "Gershgorin circle theorem":
  every eigenvalue of a finite square matrix over an arbitrary normed field
  lies in a closed ball centered at a diagonal entry with radius the sum of
  the norms of the off-diagonal entries in that row. This file contains no
  proof.
*)

let Q978688_GERSHGORIN_CIRCLE_THEOREM =
 `let is_normed_field =
    \(zeroK:K) (oneK:K)
     (addK:K->K->K) (mulK:K->K->K)
     (negK:K->K) (invK:K->K) (normK:K->real).
       ~(zeroK = oneK) /\
       (!a b c:K. addK a (addK b c) = addK (addK a b) c) /\
       (!a b:K. addK a b = addK b a) /\
       (!a:K. addK zeroK a = a) /\
       (!a:K. addK (negK a) a = zeroK) /\
       (!a b c:K. mulK a (mulK b c) = mulK (mulK a b) c) /\
       (!a b:K. mulK a b = mulK b a) /\
       (!a:K. mulK oneK a = a) /\
       (!a:K. mulK zeroK a = zeroK) /\
       invK zeroK = zeroK /\
       (!a:K. ~(a = zeroK) ==> mulK (invK a) a = oneK) /\
       (!a b c:K.
          mulK a (addK b c) = addK (mulK a b) (mulK a c)) /\
       normK zeroK = &0 /\
       normK oneK = &1 /\
       (!a:K. &0 <= normK a) /\
       (!a:K. normK a = &0 <=> a = zeroK) /\
       (!a:K. normK (negK a) = normK a) /\
       (!a b:K. normK (addK a b) <= normK a + normK b) /\
       (!a b:K. normK (mulK a b) = normK a * normK b) in
  let has_eigenvalue =
    \(zeroK:K) (addK:K->K->K) (mulK:K->K->K)
     (indices:I->bool) (A:I->I->K) (mu:K).
       ?v:I->K.
         (?i:I. i IN indices /\ ~(v i = zeroK)) /\
         (!i:I.
            i IN indices
            ==> iterate addK indices (\j:I. mulK (A i j) (v j)) =
                mulK mu (v i)) in
  !zeroK oneK:K.
  !addK mulK:K->K->K.
  !negK invK:K->K.
  !normK:K->real.
  !indices:I->bool.
  !A:I->I->K.
  !mu:K.
    is_normed_field zeroK oneK addK mulK negK invK normK /\
    FINITE indices /\
    has_eigenvalue zeroK addK mulK indices A mu
    ==> ?k:I.
          k IN indices /\
          normK (addK mu (negK (A k k))) <=
          sum (indices DELETE k) (\j:I. normK (A k j))`;;
