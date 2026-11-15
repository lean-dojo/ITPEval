(*
  Statement-only formalization of Thousand Theorems corpus artifact Q3527205,
  "Dimension theorem for vector spaces": over a semiring with invariant basis
  number, any two bases of the same module have equipotent index types. This
  file contains no proof.
*)

let Q3527205_DIMENSION_THEOREM_FOR_VECTOR_SPACES =
  `let is_semiring =
     \(zeroR:R) (oneR:R) (addR:R->R->R) (mulR:R->R->R).
       (!a:R. addR zeroR a = a /\ addR a zeroR = a) /\
       (!a b:R. addR a b = addR b a) /\
       (!a b c:R. addR (addR a b) c = addR a (addR b c)) /\
       (!a:R. mulR oneR a = a /\ mulR a oneR = a) /\
       (!a b c:R. mulR (mulR a b) c = mulR a (mulR b c)) /\
       (!a b c:R.
          mulR a (addR b c) = addR (mulR a b) (mulR a c)) /\
       (!a b c:R.
          mulR (addR a b) c = addR (mulR a c) (mulR b c)) /\
       (!a:R. mulR zeroR a = zeroR /\ mulR a zeroR = zeroR) in
   let is_module =
     \(zeroR:R) (oneR:R) (addR:R->R->R) (mulR:R->R->R)
      (zeroM:M) (addM:M->M->M) (smul:R->M->M).
       (!x:M. addM zeroM x = x /\ addM x zeroM = x) /\
       (!x y:M. addM x y = addM y x) /\
       (!x y z:M. addM (addM x y) z = addM x (addM y z)) /\
       (!x:M. smul zeroR x = zeroM) /\
       (!a:R. smul a zeroM = zeroM) /\
       (!x:M. smul oneR x = x) /\
       (!a b:R. !x:M.
          smul (addR a b) x = addM (smul a x) (smul b x)) /\
       (!a:R. !x y:M.
          smul a (addM x y) = addM (smul a x) (smul a y)) /\
       (!a b:R. !x:M.
          smul (mulR a b) x = smul a (smul b x)) in
   let finite_tuple =
     \(zeroR:R) (n:num) (x:num->R).
       !i:num. n <= i ==> x i = zeroR in
   let finite_free_linear_equiv =
     \(zeroR:R) (addR:R->R->R) (mulR:R->R->R)
      (n:num) (m:num) (f:(num->R)->(num->R)).
       (!x:num->R.
          finite_tuple zeroR n x
          ==> finite_tuple zeroR m (f x)) /\
       (!x y:num->R.
          finite_tuple zeroR n x /\ finite_tuple zeroR n y
          ==> f (\i:num. addR (x i) (y i)) =
              (\i:num. addR (f x i) (f y i))) /\
       (!a:R. !x:num->R.
          finite_tuple zeroR n x
          ==> f (\i:num. mulR a (x i)) =
              (\i:num. mulR a (f x i))) /\
       (!y:num->R.
          finite_tuple zeroR m y
          ==> ?!x:num->R.
                finite_tuple zeroR n x /\ f x = y) in
   let invariant_basis_number =
     \(zeroR:R) (addR:R->R->R) (mulR:R->R->R).
       !n m:num.
         (?f:(num->R)->(num->R).
            finite_free_linear_equiv zeroR addR mulR n m f)
         ==> n = m in
   let is_basisI =
     \(zeroR:R) (addM:M->M->M) (smul:R->M->M)
      (index:I->bool) (basis:I->M).
       !x:M.
         ?!c:I->R.
           FINITE {i:I | ~(c i = zeroR)} /\
           {i:I | ~(c i = zeroR)} SUBSET index /\
           x = iterate addM {i:I | ~(c i = zeroR)}
                 (\i:I. smul (c i) (basis i)) in
   let is_basisJ =
     \(zeroR:R) (addM:M->M->M) (smul:R->M->M)
      (index:J->bool) (basis:J->M).
       !x:M.
         ?!c:J->R.
           FINITE {j:J | ~(c j = zeroR)} /\
           {j:J | ~(c j = zeroR)} SUBSET index /\
           x = iterate addM {j:J | ~(c j = zeroR)}
                 (\j:J. smul (c j) (basis j)) in
   !zeroR oneR:R.
   !addR mulR:R->R->R.
   !zeroM:M.
   !addM:M->M->M.
   !smul:R->M->M.
   !indexI:I->bool.
   !indexJ:J->bool.
   !basisI:I->M.
   !basisJ:J->M.
     is_semiring zeroR oneR addR mulR /\
     is_module zeroR oneR addR mulR zeroM addM smul /\
     invariant_basis_number zeroR addR mulR /\
     is_basisI zeroR addM smul indexI basisI /\
     is_basisJ zeroR addM smul indexJ basisJ
     ==> indexI =_c indexJ`;;
