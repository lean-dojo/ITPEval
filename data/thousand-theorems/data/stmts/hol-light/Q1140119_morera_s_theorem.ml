(*
  Statement-only formalization of Thousand Theorems corpus artifact Q1140119
  (thousand-theorems__hol-light__Q1140119), "Morera's theorem": on an
  arbitrary open subset of the complex plane, a function into a complete
  complex normed vector space is continuous with zero integral around every
  axis-aligned rectangle exactly when it is complex differentiable there.
  This file contains no proof.
*)

let Q1140119_MORERA_S_THEOREM =
 `let czero = ((&0:real),(&0:real)) in
  let cone = ((&1:real),(&0:real)) in
  let ci = ((&0:real),(&1:real)) in
  let cadd =
    \(z:real#real) (w:real#real).
      (FST z + FST w,SND z + SND w) in
  let csub =
    \(z:real#real) (w:real#real).
      (FST z - FST w,SND z - SND w) in
  let cmul =
    \(z:real#real) (w:real#real).
      (FST z * FST w - SND z * SND w,
       FST z * SND w + SND z * FST w) in
  let cnorm =
    \(z:real#real).
      sqrt(FST z * FST z + SND z * SND z) in
  let subE =
    \(addE:A->A->A) (negE:A->A) (x:A) (y:A).
      addE x (negE y) in
  let normed_add_comm_group =
    \(zeroE:A) (addE:A->A->A) (negE:A->A) (normE:A->real).
      (!x y z:A. addE x (addE y z) = addE (addE x y) z) /\
      (!x y:A. addE x y = addE y x) /\
      (!x:A. addE zeroE x = x) /\
      (!x:A. addE (negE x) x = zeroE) /\
      normE zeroE = &0 /\
      (!x:A. &0 <= normE x) /\
      (!x:A. normE x = &0 <=> x = zeroE) /\
      (!x y:A. normE (addE x y) <= normE x + normE y) in
  let complex_normed_space =
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
  let tends_to =
    \(normE:A->real) (subE:A->A->A) (u:num->A) (l:A).
      !epsilon:real.
        &0 < epsilon
        ==> ?N:num. !n:num.
              N <= n ==> normE (subE (u n) l) < epsilon in
  let cauchy_sequence =
    \(normE:A->real) (subE:A->A->A) (u:num->A).
      !epsilon:real.
        &0 < epsilon
        ==> ?N:num. !m n:num.
              N <= m /\ N <= n
              ==> normE (subE (u m) (u n)) < epsilon in
  let complete_space =
    \(normE:A->real) (subE:A->A->A).
      !u:num->A.
        cauchy_sequence normE subE u
        ==> ?l:A. tends_to normE subE u l in
  let finite_sum =
    \(zeroE:A) (addE:A->A->A) (term:num->A) (n:num).
      ((@s:num->A.
          s 0 = zeroE /\
          (!j:num. s (SUC j) = addE (s j) (term j))) n) in
  let midpoint_sum =
    \(zeroE:A) (addE:A->A->A)
     (smulE:(real#real)->A->A)
     (g:real->A) (a:real) (b:real) (n:num).
      finite_sum zeroE addE
        (\k:num.
          smulE ((b - a) / &(SUC n),&0)
            (g (a + ((&k + &1 / &2) / &(SUC n)) * (b - a))))
        (SUC n) in
  let has_interval_integral =
    \(zeroE:A) (addE:A->A->A) (normE:A->real)
     (smulE:(real#real)->A->A) (subE:A->A->A)
     (g:real->A) (a:real) (b:real) (v:A).
      tends_to normE subE
        (\n:num. midpoint_sum zeroE addE smulE g a b n) v in
  let interval_integral =
    \(zeroE:A) (addE:A->A->A) (normE:A->real)
     (smulE:(real#real)->A->A) (subE:A->A->A)
     (g:real->A) (a:real) (b:real).
      @v:A.
        has_interval_integral
          zeroE addE normE smulE subE g a b v in
  let open_set =
    \(U:(real#real)->bool).
      !z:real#real.
        U z
        ==> ?r:real.
              &0 < r /\
              !w:real#real.
                cnorm (csub w z) < r ==> U w in
  let continuous_on =
    \(normE:A->real) (subE:A->A->A)
     (f:(real#real)->A) (U:(real#real)->bool).
      !x:real#real.
        U x
        ==> !epsilon:real.
              &0 < epsilon
              ==> ?delta:real.
                    &0 < delta /\
                    !y:real#real.
                      U y /\ cnorm (csub y x) < delta
                      ==> normE (subE (f y) (f x)) < epsilon in
  let differentiable_on =
    \(normE:A->real) (smulE:(real#real)->A->A)
     (subE:A->A->A) (f:(real#real)->A)
     (U:(real#real)->bool).
      !x:real#real.
        U x
        ==> ?d:A.
              !epsilon:real.
                &0 < epsilon
                ==> ?delta:real.
                      &0 < delta /\
                      !y:real#real.
                        U y /\ cnorm (csub y x) < delta
                        ==> normE
                              (subE
                                (subE (f y) (f x))
                                (smulE (csub y x) d))
                            <= epsilon * cnorm (csub y x) in
  let rectangle_subset =
    \(U:(real#real)->bool) (z:real#real) (w:real#real).
      !x y:real.
        min (FST z) (FST w) <= x /\
        x <= max (FST z) (FST w) /\
        min (SND z) (SND w) <= y /\
        y <= max (SND z) (SND w)
        ==> U (x,y) in
  let wedge_integral =
    \(zeroE:A) (addE:A->A->A) (normE:A->real)
     (smulE:(real#real)->A->A) (subE:A->A->A)
     (z:real#real) (w:real#real) (f:(real#real)->A).
      addE
        (interval_integral zeroE addE normE smulE subE
          (\x:real. f (x,SND z)) (FST z) (FST w))
        (smulE ci
          (interval_integral zeroE addE normE smulE subE
            (\y:real. f (FST w,y)) (SND z) (SND w))) in
  let conservative_on =
    \(zeroE:A) (addE:A->A->A) (negE:A->A) (normE:A->real)
     (smulE:(real#real)->A->A) (subE:A->A->A)
     (f:(real#real)->A) (U:(real#real)->bool).
      !z w:real#real.
        rectangle_subset U z w
        ==> wedge_integral zeroE addE normE smulE subE z w f =
            negE
              (wedge_integral
                zeroE addE normE smulE subE w z f) in
  !zeroE:A.
  !addE:A->A->A.
  !negE:A->A.
  !normE:A->real.
  !smulE:(real#real)->A->A.
  !f:(real#real)->A.
  !U:(real#real)->bool.
    normed_add_comm_group zeroE addE negE normE /\
    complex_normed_space zeroE addE normE smulE /\
    complete_space normE (subE addE negE) /\
    open_set U
    ==>
    (conservative_on
       zeroE addE negE normE smulE (subE addE negE) f U /\
     continuous_on normE (subE addE negE) f U
     <=>
     differentiable_on
       normE smulE (subE addE negE) f U)`;;
