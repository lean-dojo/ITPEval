(*
  Statement-only formalization of Thousand Theorems corpus artifact Q1050932,
  "Hartogs's theorem": a function from two complex variables to a separable
  complex Banach space that is analytic in each variable separately on an open
  set is jointly analytic there. This file contains no proof.
*)

let Q1050932_HARTOGS_S_THEOREM =
 `let czero = ((&0:real),(&0:real)) in
  let cone = ((&1:real),(&0:real)) in
  let cadd =
    \(z:real#real) (w:real#real).
      (FST z + FST w,SND z + SND w) in
  let cneg =
    \(z:real#real).
      (--(FST z),--(SND z)) in
  let csub =
    \(z:real#real) (w:real#real).
      cadd z (cneg w) in
  let cmul =
    \(z:real#real) (w:real#real).
      (FST z * FST w - SND z * SND w,
       FST z * SND w + SND z * FST w) in
  let cnorm =
    \(z:real#real).
      sqrt(FST z * FST z + SND z * SND z) in
  let cpadd =
    \(z:(real#real)#(real#real))
     (w:(real#real)#(real#real)).
      (cadd (FST z) (FST w),cadd (SND z) (SND w)) in
  let cpsub =
    \(z:(real#real)#(real#real))
     (w:(real#real)#(real#real)).
      (csub (FST z) (FST w),csub (SND z) (SND w)) in
  let cpnorm =
    \(z:(real#real)#(real#real)).
      max (cnorm (FST z)) (cnorm (SND z)) in
  !(zeroE:A) (addE:A->A->A) (negE:A->A)
   (smulE:(real#real)->A->A) (normE:A->real)
   (f:((real#real)#(real#real))->A)
   (s:((real#real)#(real#real))->bool).
    let subE =
      \(x:A) (y:A). addE x (negE y) in
    let is_complex_normed_space =
      ((!x y z:A.
         addE x (addE y z) = addE (addE x y) z) /\
      (!x y:A. addE x y = addE y x) /\
      (!x:A. addE zeroE x = x) /\
      (!x:A. addE (negE x) x = zeroE) /\
      normE zeroE = &0 /\
      (!x:A. &0 <= normE x) /\
      (!x:A. normE x = &0 <=> x = zeroE) /\
      (!x:A. normE (negE x) = normE x) /\
      (!x y:A. normE (addE x y) <= normE x + normE y) /\
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
      (!a:real#real. !x:A.
         normE (smulE a x) = cnorm a * normE x)) in
    let tends_to =
      \(u:num->A) (x:A).
        !epsilon:real.
          &0 < epsilon
          ==> ?N:num. !n:num.
                N <= n
                ==> normE (subE (u n) x) < epsilon in
    let complete_space =
      (!u:num->A.
        (!epsilon:real.
           &0 < epsilon
           ==> ?N:num. !m n:num.
                 N <= m /\ N <= n
                 ==> normE (subE (u m) (u n)) < epsilon)
        ==> ?x:A. tends_to u x) in
    let norm_open =
      \(U:A->bool).
        !x:A.
          x IN U
          ==> ?epsilon:real.
                &0 < epsilon /\
                !y:A.
                  normE (subE y x) < epsilon
                  ==> y IN U in
    let second_countable =
      (?basis:(A->bool)->bool.
        COUNTABLE basis /\
        (!b:A->bool. b IN basis ==> norm_open b) /\
        (!U:A->bool. !x:A.
           norm_open U /\ x IN U
           ==> ?b:A->bool.
                 b IN basis /\ x IN b /\ b SUBSET U)) in
    let complex_differentiable_at_1 =
      \(g:(real#real)->A) (x:real#real).
        ?d:A.
          !epsilon:real.
            &0 < epsilon
            ==> ?delta:real.
                  &0 < delta /\
                  !h:real#real.
                    cnorm h < delta
                    ==> normE
                          (subE
                            (subE (g (cadd x h)) (g x))
                            (smulE h d))
                        <= epsilon * cnorm h in
    let complex_differentiable_at_2 =
      \(g:((real#real)#(real#real))->A)
       (x:(real#real)#(real#real)).
        ?d0 d1:A.
          !epsilon:real.
            &0 < epsilon
            ==> ?delta:real.
                  &0 < delta /\
                  !h:(real#real)#(real#real).
                    cpnorm h < delta
                    ==> normE
                          (subE
                            (subE (g (cpadd x h)) (g x))
                            (addE
                              (smulE (FST h) d0)
                              (smulE (SND h) d1)))
                        <= epsilon * cpnorm h in
    let analytic_at_1 =
      \(g:(real#real)->A) (x:real#real).
        ?radius:real.
          &0 < radius /\
          !y:real#real.
            cnorm (csub y x) < radius
            ==> complex_differentiable_at_1 g y in
    let analytic_at_2 =
      \(g:((real#real)#(real#real))->A)
       (x:(real#real)#(real#real)).
        ?radius:real.
          &0 < radius /\
          !y:(real#real)#(real#real).
            cpnorm (cpsub y x) < radius
            ==> complex_differentiable_at_2 g y in
    let product_open =
      \(U:((real#real)#(real#real))->bool).
        !x:(real#real)#(real#real).
          x IN U
          ==> ?epsilon:real.
                &0 < epsilon /\
                !y:(real#real)#(real#real).
                  cpnorm (cpsub y x) < epsilon
                  ==> y IN U in
    let analytic_on_nhd_2 =
      \(g:((real#real)#(real#real))->A)
       (U:((real#real)#(real#real))->bool).
        !x:(real#real)#(real#real).
          x IN U ==> analytic_at_2 g x in
      is_complex_normed_space /\
      complete_space /\
      second_countable /\
      product_open s /\
      (!c0 c1:real#real.
         (c0,c1) IN s
         ==> analytic_at_1 (\z0. f (z0,c1)) c0) /\
      (!c0 c1:real#real.
         (c0,c1) IN s
         ==> analytic_at_1 (\z1. f (c0,z1)) c1)
      ==> analytic_on_nhd_2 f s`;;
