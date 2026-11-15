(*
  Statement-only formalization of Thousand Theorems corpus artifact Q576478,
  "Liouville's theorem (complex analysis)": an everywhere complex
  Frechet-differentiable function between arbitrary complex normed spaces
  with bounded range takes the same value at every two points. This file
  contains no proof.
*)

let Q576478_LIOUVILLE_THEOREM_COMPLEX_ANALYSIS =
 `let czero = ((&0:real),(&0:real)) in
  let cone = ((&1:real),(&0:real)) in
  let cadd =
    \(a:real#real) (b:real#real).
      (FST a + FST b,SND a + SND b) in
  let cmul =
    \(a:real#real) (b:real#real).
      (FST a * FST b - SND a * SND b,
       FST a * SND b + SND a * FST b) in
  let cnorm =
    \(a:real#real).
      sqrt (FST a * FST a + SND a * SND a) in
  let normed_add_comm_group_E =
    \(zeroE:A) (addE:A->A->A) (negE:A->A) (normE:A->real).
      (!x y z:A. addE x (addE y z) = addE (addE x y) z) /\
      (!x y:A. addE x y = addE y x) /\
      (!x:A. addE zeroE x = x) /\
      (!x:A. addE (negE x) x = zeroE) /\
      normE zeroE = &0 /\
      (!x:A. &0 <= normE x) /\
      (!x:A. normE x = &0 <=> x = zeroE) /\
      (!x y:A. normE (addE x y) <= normE x + normE y) in
  let normed_add_comm_group_F =
    \(zeroF:B) (addF:B->B->B) (negF:B->B) (normF:B->real).
      (!x y z:B. addF x (addF y z) = addF (addF x y) z) /\
      (!x y:B. addF x y = addF y x) /\
      (!x:B. addF zeroF x = x) /\
      (!x:B. addF (negF x) x = zeroF) /\
      normF zeroF = &0 /\
      (!x:B. &0 <= normF x) /\
      (!x:B. normF x = &0 <=> x = zeroF) /\
      (!x y:B. normF (addF x y) <= normF x + normF y) in
  let complex_normed_space_E =
    \(zeroE:A) (addE:A->A->A) (normE:A->real)
     (smulE:(real#real)->A->A).
      (!x:A. smulE cone x = x) /\
      (!a b:real#real. !x:A.
         smulE (cmul a b) x = smulE a (smulE b x)) /\
      (!a b:real#real. !x:A.
         smulE (cadd a b) x = addE (smulE a x) (smulE b x)) /\
      (!a:real#real. !x y:A.
         smulE a (addE x y) = addE (smulE a x) (smulE a y)) /\
      (!a:real#real. smulE a zeroE = zeroE) /\
      (!x:A. smulE czero x = zeroE) /\
      (!a:real#real. !x:A.
         normE (smulE a x) = cnorm a * normE x) in
  let complex_normed_space_F =
    \(zeroF:B) (addF:B->B->B) (normF:B->real)
     (smulF:(real#real)->B->B).
      (!x:B. smulF cone x = x) /\
      (!a b:real#real. !x:B.
         smulF (cmul a b) x = smulF a (smulF b x)) /\
      (!a b:real#real. !x:B.
         smulF (cadd a b) x = addF (smulF a x) (smulF b x)) /\
      (!a:real#real. !x y:B.
         smulF a (addF x y) = addF (smulF a x) (smulF a y)) /\
      (!a:real#real. smulF a zeroF = zeroF) /\
      (!x:B. smulF czero x = zeroF) /\
      (!a:real#real. !x:B.
         normF (smulF a x) = cnorm a * normF x) in
  let subF =
    \(addF:B->B->B) (negF:B->B) (x:B) (y:B).
      addF x (negF y) in
  let continuous_complex_linear =
    \(addE:A->A->A) (normE:A->real)
     (smulE:(real#real)->A->A)
     (addF:B->B->B) (normF:B->real)
     (smulF:(real#real)->B->B) (L:A->B).
      (!x y:A. L (addE x y) = addF (L x) (L y)) /\
      (!a:real#real. !x:A. L (smulE a x) = smulF a (L x)) /\
      (?C:real. &0 <= C /\ !x:A. normF (L x) <= C * normE x) in
  let everywhere_complex_frechet_differentiable =
    \(zeroE:A) (addE:A->A->A) (normE:A->real)
     (smulE:(real#real)->A->A)
     (addF:B->B->B) (negF:B->B) (normF:B->real)
     (smulF:(real#real)->B->B) (f:A->B).
      !x:A.
        ?L:A->B.
          continuous_complex_linear
            addE normE smulE addF normF smulF L /\
          !epsilon:real.
            &0 < epsilon
            ==> ?delta:real.
                  &0 < delta /\
                  !h:A.
                    normE h < delta
                    ==> normF
                          (subF addF negF
                            (subF addF negF
                              (f (addE x h)) (f x))
                            (L h))
                        <= epsilon * normE h in
  let bounded_range =
    \(normF:B->real) (f:A->B).
      ?C:real. &0 <= C /\ !x:A. normF (f x) <= C in
  !zeroE:A.
  !addE:A->A->A.
  !negE:A->A.
  !normE:A->real.
  !smulE:(real#real)->A->A.
  !zeroF:B.
  !addF:B->B->B.
  !negF:B->B.
  !normF:B->real.
  !smulF:(real#real)->B->B.
  !f:A->B.
  !z w:A.
    normed_add_comm_group_E zeroE addE negE normE /\
    normed_add_comm_group_F zeroF addF negF normF /\
    complex_normed_space_E zeroE addE normE smulE /\
    complex_normed_space_F zeroF addF normF smulF /\
    everywhere_complex_frechet_differentiable
      zeroE addE normE smulE addF negF normF smulF f /\
    bounded_range normF f
    ==> f z = f w`;;
