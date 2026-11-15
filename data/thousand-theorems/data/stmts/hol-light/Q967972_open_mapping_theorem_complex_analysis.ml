(*
  Statement-only formalization of the Thousand Theorems corpus artifact
  Q967972 (thousand-theorems__hol-light__Q967972), "Open mapping theorem
  (complex analysis)": an analytic function from an arbitrary complex normed
  vector space to the complex numbers, on a preconnected set, is constant
  there or maps every open subset of that set to an open set. This file
  contains no proof.
*)

let Q967972_OPEN_MAPPING_THEOREM_COMPLEX_ANALYSIS =
 `let czero = ((&0:real),(&0:real)) in
  let cone = ((&1:real),(&0:real)) in
  let cadd =
    \(a:real#real) (b:real#real).
      (FST a + FST b,SND a + SND b) in
  let cneg =
    \(a:real#real). (--(FST a),--(SND a)) in
  let csub =
    \(a:real#real) (b:real#real).
      cadd a (cneg b) in
  let cmul =
    \(a:real#real) (b:real#real).
      (FST a * FST b - SND a * SND b,
       FST a * SND b + SND a * FST b) in
  let cnorm =
    \(a:real#real).
      sqrt(FST a * FST a + SND a * SND a) in
  let normed_add_comm_group =
    \(zeroE:A) (addE:A->A->A) (negE:A->A)
     (normE:A->real).
      (!x y z:A.
         addE x (addE y z) = addE (addE x y) z) /\
      (!x y:A. addE x y = addE y x) /\
      (!x:A. addE zeroE x = x) /\
      (!x:A. addE (negE x) x = zeroE) /\
      normE zeroE = &0 /\
      (!x:A. &0 <= normE x) /\
      (!x:A. normE x = &0 <=> x = zeroE) /\
      (!x:A. normE (negE x) = normE x) /\
      (!x y:A. normE (addE x y) <= normE x + normE y) in
  let complex_normed_space =
    \(zeroE:A) (addE:A->A->A) (negE:A->A) (normE:A->real)
     (smulE:(real#real)->A->A).
      (!x:A. smulE cone x = x) /\
      (!a b:real#real. !x:A.
         smulE (cmul a b) x = smulE a (smulE b x)) /\
      (!a b:real#real. !x:A.
         smulE (cadd a b) x =
         addE (smulE a x) (smulE b x)) /\
      (!a:real#real. !x y:A.
         smulE a (addE x y) =
         addE (smulE a x) (smulE a y)) /\
      (!a:real#real. smulE a zeroE = zeroE) /\
      (!x:A. smulE czero x = zeroE) /\
      (!x:A. negE x = smulE (cneg cone) x) /\
      (!a:real#real. !x:A.
         normE (smulE a x) = cnorm a * normE x) in
  let subE =
    \(addE:A->A->A) (negE:A->A) (x:A) (y:A).
      addE x (negE y) in
  let continuous_complex_linear =
    \(addE:A->A->A) (normE:A->real)
     (smulE:(real#real)->A->A) (L:A->real#real).
      (!x y:A. L (addE x y) = cadd (L x) (L y)) /\
      (!a:real#real. !x:A.
         L (smulE a x) = cmul a (L x)) /\
      (?C:real.
         &0 <= C /\
         !x:A. cnorm (L x) <= C * normE x) in
  let complex_frechet_differentiable_at =
    \(addE:A->A->A) (normE:A->real)
     (smulE:(real#real)->A->A)
     (f:A->real#real) (x:A).
      ?L:A->real#real.
        continuous_complex_linear addE normE smulE L /\
        !epsilon:real.
          &0 < epsilon
          ==> ?delta:real.
                &0 < delta /\
                !h:A.
                  &0 < normE h /\ normE h < delta
                  ==> cnorm
                        (csub
                          (csub (f (addE x h)) (f x))
                          (L h))
                      < epsilon * normE h in
  let analytic_on_nhd =
    \(addE:A->A->A) (negE:A->A) (normE:A->real)
     (smulE:(real#real)->A->A)
     (f:A->real#real) (U:A->bool).
      !x:A.
        x IN U
        ==> ?radius:real.
              &0 < radius /\
              !y:A.
                normE (subE addE negE y x) < radius
                ==> complex_frechet_differentiable_at
                      addE normE smulE f y in
  let norm_open =
    \(addE:A->A->A) (negE:A->A) (normE:A->real)
     (s:A->bool).
      !x:A.
        x IN s
        ==> ?epsilon:real.
              &0 < epsilon /\
              !y:A.
                normE (subE addE negE y x) < epsilon
                ==> y IN s in
  let complex_open =
    \(s:(real#real)->bool).
      !z:real#real.
        z IN s
        ==> ?epsilon:real.
              &0 < epsilon /\
              !w:real#real.
                cnorm (csub w z) < epsilon
                ==> w IN s in
  let preconnected =
    \(addE:A->A->A) (negE:A->A) (normE:A->real)
     (U:A->bool).
      !s t:A->bool.
        norm_open addE negE normE s /\
        norm_open addE negE normE t /\
        U SUBSET (s UNION t) /\
        DISJOINT (U INTER s) (U INTER t)
        ==> U INTER s = {} \/ U INTER t = {} in
  !zeroE:A.
  !addE:A->A->A.
  !negE:A->A.
  !normE:A->real.
  !smulE:(real#real)->A->A.
  !f:A->real#real.
  !U:A->bool.
    normed_add_comm_group zeroE addE negE normE /\
    complex_normed_space zeroE addE negE normE smulE /\
    analytic_on_nhd addE negE normE smulE f U /\
    preconnected addE negE normE U
    ==> ((?w:real#real. !z:A. z IN U ==> f z = w) \/
         (!s:A->bool.
            s SUBSET U /\
            norm_open addE negE normE s
            ==> complex_open (IMAGE f s)))`;;
