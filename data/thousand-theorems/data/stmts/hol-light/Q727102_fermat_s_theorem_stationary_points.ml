(*
  Statement-only formalization of Thousand Theorems corpus artifact Q727102,
  "Fermat's theorem (stationary points)": the totalized Frechet derivative of
  a real-valued function on a real normed vector space, and in particular its
  totalized real derivative, vanishes at a local extremum. This file contains
  no proof.
*)

let Q727102_FERMAT_S_THEOREM_STATIONARY_POINTS =
 `let normed_real_vector_space =
    \(zero:A) (add:A->A->A) (neg:A->A)
     (smul:real->A->A) (normA:A->real).
       (!x y z:A. add x (add y z) = add (add x y) z) /\
       (!x y:A. add x y = add y x) /\
       (!x:A. add zero x = x) /\
       (!x:A. add (neg x) x = zero) /\
       (!x:A. smul (&1) x = x) /\
       (!c d:real. !x:A. smul (c * d) x = smul c (smul d x)) /\
       (!c d:real. !x:A.
          smul (c + d) x = add (smul c x) (smul d x)) /\
       (!c:real. !x y:A.
          smul c (add x y) = add (smul c x) (smul c y)) /\
       normA zero = &0 /\
       (!x:A. &0 <= normA x) /\
       (!x:A. normA x = &0 <=> x = zero) /\
       (!x:A. normA (neg x) = normA x) /\
       (!x y:A. normA (add x y) <= normA x + normA y) /\
       (!c:real. !x:A. normA (smul c x) = abs c * normA x) in
  let continuous_linear_functional =
    \(add:A->A->A) (smul:real->A->A) (normA:A->real)
     (d:A->real).
       (!x y:A. d (add x y) = d x + d y) /\
       (!c:real. !x:A. d (smul c x) = c * d x) /\
       (?bound:real.
          &0 <= bound /\
          !x:A. abs(d x) <= bound * normA x) in
  let has_frechet_derivative =
    \(add:A->A->A) (smul:real->A->A) (normA:A->real)
     (f:A->real) (d:A->real) (a:A).
       continuous_linear_functional add smul normA d /\
       !epsilon:real.
         &0 < epsilon
         ==> ?delta:real.
               &0 < delta /\
               !h:A.
                 &0 < normA h /\ normA h < delta
                 ==> abs(f (add a h) - f a - d h) / normA h < epsilon in
  let local_extremum =
    \(add:A->A->A) (neg:A->A) (normA:A->real)
     (f:A->real) (a:A).
       (?radius:real.
          &0 < radius /\
          !x:A.
            normA (add x (neg a)) < radius ==> f a <= f x) \/
       (?radius:real.
          &0 < radius /\
          !x:A.
            normA (add x (neg a)) < radius ==> f x <= f a) in
  let total_frechet_derivative =
    \(add:A->A->A) (smul:real->A->A) (normA:A->real)
     (f:A->real) (a:A).
       if ?d:A->real. has_frechet_derivative add smul normA f d a
       then @d:A->real. has_frechet_derivative add smul normA f d a
       else \h:A. &0 in
  let has_real_derivative =
    \(f:real->real) (d:real) (a:real).
       !epsilon:real.
         &0 < epsilon
         ==> ?delta:real.
               &0 < delta /\
               !h:real.
                 &0 < abs h /\ abs h < delta
                 ==> abs((f (a + h) - f a) / h - d) < epsilon in
  let real_local_extremum =
    \(f:real->real) (a:real).
       (?radius:real.
          &0 < radius /\
          !x:real. abs(x - a) < radius ==> f a <= f x) \/
       (?radius:real.
          &0 < radius /\
          !x:real. abs(x - a) < radius ==> f x <= f a) in
  let total_real_derivative =
    \(f:real->real) (a:real).
       if ?d:real. has_real_derivative f d a
       then @d:real. has_real_derivative f d a
       else &0 in
  ((!zero:A. !add:A->A->A. !neg:A->A.
    !smul:real->A->A. !normA:A->real.
    !f:A->real. !a:A.
      normed_real_vector_space zero add neg smul normA /\
      local_extremum add neg normA f a
      ==> total_frechet_derivative add smul normA f a = (\h:A. &0))
   /\
   (!f:real->real. !a:real.
      real_local_extremum f a
      ==> total_real_derivative f a = &0))`;;
