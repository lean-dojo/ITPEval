(*
  Statement-only formalization of Thousand Theorems corpus artifact Q537618,
  "Banach–Alaoglu theorem": over a proper nontrivially normed field, the polar
  of a neighborhood of zero in a seminormed space is compact in the weak-star
  topology on the continuous dual. This file contains no proof.
*)

let Q537618_BANACH_ALAOGLU_THEOREM =
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
  let seminormed_add_comm_group =
    \(zeroE:B) (addE:B->B->B) (negE:B->B) (normE:B->real).
       (!x y z:B. addE x (addE y z) = addE (addE x y) z) /\
       (!x y:B. addE x y = addE y x) /\
       (!x:B. addE zeroE x = x) /\
       (!x:B. addE (negE x) x = zeroE) /\
       normE zeroE = &0 /\
       (!x:B. &0 <= normE x) /\
       (!x:B. normE (negE x) = normE x) /\
       (!x y:B. normE (addE x y) <= normE x + normE y) in
  let normed_space =
    \(zeroK:A) (oneK:A)
     (addK:A->A->A) (mulK:A->A->A) (normK:A->real)
     (zeroE:B) (addE:B->B->B) (normE:B->real)
     (smul:A->B->B).
       (!x:B. smul oneK x = x) /\
       (!a b:A. !x:B.
          smul (mulK a b) x = smul a (smul b x)) /\
       (!a b:A. !x:B.
          smul (addK a b) x = addE (smul a x) (smul b x)) /\
       (!a:A. !x y:B.
          smul a (addE x y) = addE (smul a x) (smul a y)) /\
       (!a:A. smul a zeroE = zeroE) /\
       (!x:B. smul zeroK x = zeroE) /\
       (!a:A. !x:B. normE (smul a x) = normK a * normE x) in
  let norm_open =
    \(addK:A->A->A) (negK:A->A) (normK:A->real)
     (U:A->bool).
       !x:A.
         x IN U
         ==> ?epsilon:real.
               &0 < epsilon /\
               !y:A.
                 normK (addK y (negK x)) < epsilon
                 ==> y IN U in
  let is_compact_field =
    \(opens:(A->bool)->bool) (compact_set:A->bool).
       !open_cover:(A->bool)->bool.
         (!cover_member:A->bool.
            cover_member IN open_cover ==> opens cover_member) /\
         compact_set SUBSET UNIONS open_cover
         ==> ?finite_subcover:(A->bool)->bool.
               finite_subcover SUBSET open_cover /\
               FINITE finite_subcover /\
               compact_set SUBSET UNIONS finite_subcover in
  let proper_space =
    \(addK:A->A->A) (negK:A->A) (normK:A->real).
       !center:A. !radius:real.
         is_compact_field
           (norm_open addK negK normK)
           {x:A | normK (addK x (negK center)) <= radius} in
  let continuous_linear_functional =
    \(addK:A->A->A) (mulK:A->A->A) (normK:A->real)
     (addE:B->B->B) (smul:A->B->B) (normE:B->real)
     (f:B->A).
       (!x y:B. f (addE x y) = addK (f x) (f y)) /\
       (!a:A. !x:B. f (smul a x) = mulK a (f x)) /\
       (!epsilon:real.
          &0 < epsilon
          ==> ?delta:real.
                &0 < delta /\
                !x:B. normE x < delta ==> normK (f x) < epsilon) in
  let weak_dual =
    \(addK:A->A->A) (mulK:A->A->A) (normK:A->real)
     (addE:B->B->B) (smul:A->B->B) (normE:B->real).
       {f:B->A |
          continuous_linear_functional
            addK mulK normK addE smul normE f} in
  let weak_star_open =
    \(addK:A->A->A) (negK:A->A) (normK:A->real)
     (dual:(B->A)->bool) (U:(B->A)->bool).
       U SUBSET dual /\
       !f:B->A.
         f IN U
         ==> ?coordinates:B->bool. ?epsilon:B->real.
               FINITE coordinates /\
               (!x:B. x IN coordinates ==> &0 < epsilon x) /\
               {g:B->A |
                  g IN dual /\
                  !x:B.
                    x IN coordinates
                    ==> normK (addK (g x) (negK (f x))) < epsilon x}
               SUBSET U in
  let polar =
    \(normK:A->real) (dual:(B->A)->bool) (s:B->bool).
       {f:B->A |
          f IN dual /\
          !x:B. x IN s ==> normK (f x) <= &1} in
  let is_compact_weak_dual =
    \(dual:(B->A)->bool)
     (opens:((B->A)->bool)->bool)
     (compact_set:(B->A)->bool).
       compact_set SUBSET dual /\
       !open_cover:((B->A)->bool)->bool.
         (!cover_member:(B->A)->bool.
            cover_member IN open_cover ==> opens cover_member) /\
         compact_set SUBSET UNIONS open_cover
         ==> ?finite_subcover:((B->A)->bool)->bool.
               finite_subcover SUBSET open_cover /\
               FINITE finite_subcover /\
               compact_set SUBSET UNIONS finite_subcover in
  !zeroK oneK:A.
  !addK mulK:A->A->A.
  !negK invK:A->A.
  !normK:A->real.
  !zeroE:B.
  !addE:B->B->B.
  !negE:B->B.
  !smul:A->B->B.
  !normE:B->real.
  !s:B->bool.
    nontrivially_normed_field
      zeroK oneK addK mulK negK invK normK /\
    seminormed_add_comm_group zeroE addE negE normE /\
    normed_space
      zeroK oneK addK mulK normK zeroE addE normE smul /\
    proper_space addK negK normK /\
    (?epsilon:real.
       &0 < epsilon /\
       !x:B. normE x < epsilon ==> x IN s)
    ==> let dual =
          weak_dual addK mulK normK addE smul normE in
        is_compact_weak_dual
          dual
          (weak_star_open addK negK normK dual)
          (polar normK dual s)`;;
