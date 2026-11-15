(*
  Statement-only formalization of PutnamBench corpus artifact putnam_1988_a6:
  a linear endomorphism of an n-dimensional vector space with n+1 nonzero
  eigenvectors, every n of which are linearly independent, is a scalar
  multiple of the identity. This file contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory listTheory pred_setTheory;

val putnam_1988_a6 =
  ``let is_field =
      \(zeroF : 'f) (oneF : 'f)
       (addF : 'f -> 'f -> 'f) (mulF : 'f -> 'f -> 'f)
       (negF : 'f -> 'f) (invF : 'f -> 'f).
        zeroF <> oneF /\
        (!a b : 'f. addF a b = addF b a) /\
        (!a b c : 'f. addF (addF a b) c = addF a (addF b c)) /\
        (!a : 'f. addF zeroF a = a) /\
        (!a : 'f. addF (negF a) a = zeroF) /\
        (!a b : 'f. mulF a b = mulF b a) /\
        (!a b c : 'f. mulF (mulF a b) c = mulF a (mulF b c)) /\
        (!a : 'f. mulF oneF a = a) /\
        (!a b c : 'f.
           mulF a (addF b c) = addF (mulF a b) (mulF a c)) /\
        (!a : 'f. a <> zeroF ==> mulF (invF a) a = oneF)
    in
    let is_vector_space =
      \(zeroF : 'f) (oneF : 'f)
       (addF : 'f -> 'f -> 'f) (mulF : 'f -> 'f -> 'f)
       (zeroV : 'v) (addV : 'v -> 'v -> 'v) (negV : 'v -> 'v)
       (smul : 'f -> 'v -> 'v).
        (!x y : 'v. addV x y = addV y x) /\
        (!x y z : 'v. addV (addV x y) z = addV x (addV y z)) /\
        (!x : 'v. addV zeroV x = x) /\
        (!x : 'v. addV (negV x) x = zeroV) /\
        (!a : 'f. !x y : 'v.
           smul a (addV x y) = addV (smul a x) (smul a y)) /\
        (!a b : 'f. !x : 'v.
           smul (addF a b) x = addV (smul a x) (smul b x)) /\
        (!a b : 'f. !x : 'v.
           smul (mulF a b) x = smul a (smul b x)) /\
        (!x : 'v. smul oneF x = x)
    in
    let is_linear =
      \(addV : 'v -> 'v -> 'v) (smul : 'f -> 'v -> 'v)
       (A : 'v -> 'v).
        (!x y : 'v. A (addV x y) = addV (A x) (A y)) /\
        (!a : 'f. !x : 'v. A (smul a x) = smul a (A x))
    in
    let lincomb =
      \(zeroV : 'v) (addV : 'v -> 'v -> 'v)
       (smul : 'f -> 'v -> 'v) (m : num)
       (coeff : num -> 'f) (vec : num -> 'v).
        FOLDL
          (\acc i. addV acc (smul (coeff i) (vec i)))
          zeroV
          (GENLIST (\i. i) m)
    in
    let independent =
      \(zeroF : 'f) (zeroV : 'v) (addV : 'v -> 'v -> 'v)
       (smul : 'f -> 'v -> 'v) (s : 'v -> bool).
        !m : num. !vec : num -> 'v. !coeff : num -> 'f.
          (!i : num. i < m ==> s (vec i)) /\
          (!i j : num.
             i < m /\ j < m /\ vec i = vec j ==> i = j) /\
          lincomb zeroV addV smul m coeff vec = zeroV
          ==>
          !i : num. i < m ==> coeff i = zeroF
    in
    let has_dimension =
      \(zeroF : 'f) (zeroV : 'v) (addV : 'v -> 'v -> 'v)
       (smul : 'f -> 'v -> 'v) (n : num).
        ?basis : 'v list.
          LENGTH basis = n /\
          ALL_DISTINCT basis /\
          independent zeroF zeroV addV smul
            (\x : 'v. MEM x basis) /\
          !x : 'v.
            ?coeff : num -> 'f.
              lincomb zeroV addV smul n coeff
                (\i : num. EL i basis) = x
    in
    let putnam_1988_a6_solution = T
    in
      (!(zeroF : 'f) (oneF : 'f)
         (addF : 'f -> 'f -> 'f) (mulF : 'f -> 'f -> 'f)
         (negF : 'f -> 'f) (invF : 'f -> 'f)
         (zeroV : 'v) (addV : 'v -> 'v -> 'v) (negV : 'v -> 'v)
         (smul : 'f -> 'v -> 'v) (n : num) (A : 'v -> 'v)
         (evecs : 'v -> bool).
          is_field zeroF oneF addF mulF negF invF /\
          is_vector_space zeroF oneF addF mulF
            zeroV addV negV smul /\
          is_linear addV smul A /\
          has_dimension zeroF zeroV addV smul n /\
          FINITE evecs /\
          CARD evecs = n + 1 /\
          (!v : 'v.
             evecs v ==>
             v <> zeroV /\
             ?a : 'f. A v = smul a v) /\
          (!s : 'v -> bool.
             s SUBSET evecs /\ FINITE s /\ CARD s = n
             ==>
             independent zeroF zeroV addV smul s)
          ==>
          ?c : 'f. !x : 'v. A x = smul c x)
      <=>
      putnam_1988_a6_solution``;
