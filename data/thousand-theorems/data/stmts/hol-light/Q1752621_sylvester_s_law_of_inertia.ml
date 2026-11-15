(*
  Statement-only formalization of Thousand Theorems corpus artifact Q1752621
  (thousand-theorems__hol-light__Q1752621), "Sylvester's law of inertia":
  every quadratic form on a finite-dimensional real vector space has a basis
  in which it is a weighted sum of squares with every weight equal to -1, 0,
  or 1. This file contains no proof.
*)

let Q1752621_SYLVESTERS_LAW_OF_INERTIA =
 `let real_vector_space =
    \(zero:V) (add:V->V->V) (neg:V->V) (smul:real->V->V).
      (!x y z:V. add x (add y z) = add (add x y) z) /\
      (!x y:V. add x y = add y x) /\
      (!x:V. add zero x = x) /\
      (!x:V. add (neg x) x = zero) /\
      (!x:V. smul (&1) x = x) /\
      (!a b:real. !x:V.
         smul (a * b) x = smul a (smul b x)) /\
      (!a b:real. !x:V.
         smul (a + b) x = add (smul a x) (smul b x)) /\
      (!a:real. !x y:V.
         smul a (add x y) = add (smul a x) (smul a y)) /\
      (!x:V. smul (&0) x = zero) /\
      (!a:real. smul a zero = zero) in
  let symmetric_bilinear =
    \(add:V->V->V) (smul:real->V->V) (B:V->V->real).
      (!x y z:V. B (add x y) z = B x z + B y z) /\
      (!a:real. !x y:V. B (smul a x) y = a * B x y) /\
      (!x y z:V. B x (add y z) = B x y + B x z) /\
      (!a:real. !x y:V. B x (smul a y) = a * B x y) /\
      (!x y:V. B x y = B y x) in
  let real_quadratic_form =
    \(add:V->V->V) (smul:real->V->V) (q:V->real).
      ?B:V->V->real.
        symmetric_bilinear add smul B /\
        (!x:V. q x = B x x) in
  let basis_of_dimension =
    \(zero:V) (add:V->V->V) (smul:real->V->V)
     (n:num) (basis:num->V).
      (!x:V.
         ?!c:num->real.
           (!i:num. n <= i ==> c i = &0) /\
           x = iterate add {i:num | i < n}
                 (\i:num. smul (c i) (basis i))) in
  let finite_dimensional =
    \(zero:V) (add:V->V->V) (smul:real->V->V).
      ?n:num. ?basis:num->V.
        basis_of_dimension zero add smul n basis in
  !zero:V.
  !add:V->V->V.
  !neg:V->V.
  !smul:real->V->V.
  !q:V->real.
    real_vector_space zero add neg smul /\
    real_quadratic_form add smul q /\
    finite_dimensional zero add smul
    ==>
    ?n:num. ?w:num->real. ?diagonal_basis:num->V.
      basis_of_dimension zero add smul n diagonal_basis /\
      (!i:num.
         i < n
         ==> w i = -- &1 \/ w i = &0 \/ w i = &1) /\
      (!c:num->real.
         q (iterate add {i:num | i < n}
              (\i:num. smul (c i) (diagonal_basis i))) =
         sum {i:num | i < n} (\i:num. w i * (c i) pow 2))`;;
