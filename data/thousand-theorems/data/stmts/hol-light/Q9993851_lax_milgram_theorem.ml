(*
  Statement-only formalization of Thousand Theorems corpus artifact Q9993851,
  "Lax–Milgram theorem": a coercive bounded bilinear form on a real Hilbert
  space induces a continuous linear equivalence representing that form through
  the inner product. This file contains no proof.
*)

let Q9993851_LAX_MILGRAM_THEOREM =
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
         smul a (add x y) = add (smul a x) (smul a y)) in
  let real_inner_product =
    \(zero:V) (add:V->V->V) (smul:real->V->V)
     (inner:V->V->real).
      (!x y z:V.
         inner (add x y) z = inner x z + inner y z) /\
      (!a:real. !x y:V.
         inner (smul a x) y = a * inner x y) /\
      (!x y:V. inner x y = inner y x) /\
      (!x:V. &0 <= inner x x) /\
      (!x:V. inner x x = &0 <=> x = zero) in
  let vnorm =
    \(inner:V->V->real) (x:V). sqrt(inner x x) in
  let tends_to =
    \(add:V->V->V) (neg:V->V) (inner:V->V->real)
     (u:num->V) (x:V).
      !epsilon:real.
        &0 < epsilon
        ==> ?N:num. !n:num.
              N <= n
              ==> vnorm inner (add (u n) (neg x)) < epsilon in
  let complete_space =
    \(add:V->V->V) (neg:V->V) (inner:V->V->real).
      !u:num->V.
        (!epsilon:real.
           &0 < epsilon
           ==> ?N:num. !m n:num.
                 N <= m /\ N <= n
                 ==> vnorm inner
                       (add (u m) (neg (u n))) < epsilon)
        ==> ?x:V. tends_to add neg inner u x in
  let bounded_bilinear =
    \(add:V->V->V) (smul:real->V->V)
     (inner:V->V->real) (B:V->V->real).
      (!x y z:V. B (add x y) z = B x z + B y z) /\
      (!a:real. !x y:V. B (smul a x) y = a * B x y) /\
      (!x y z:V. B x (add y z) = B x y + B x z) /\
      (!a:real. !x y:V. B x (smul a y) = a * B x y) /\
      (?C:real.
         &0 <= C /\
         !x y:V.
           abs(B x y) <= C * vnorm inner x * vnorm inner y) in
  let coercive =
    \(inner:V->V->real) (B:V->V->real).
      ?C:real.
        &0 < C /\
        !x:V.
          C * vnorm inner x * vnorm inner x <= B x x in
  let continuous_linear =
    \(add:V->V->V) (smul:real->V->V)
     (inner:V->V->real) (f:V->V).
      (!x y:V. f (add x y) = add (f x) (f y)) /\
      (!a:real. !x:V. f (smul a x) = smul a (f x)) /\
      (?C:real.
         &0 <= C /\
         !x:V. vnorm inner (f x) <= C * vnorm inner x) in
  let continuous_linear_equivalence =
    \(add:V->V->V) (smul:real->V->V)
     (inner:V->V->real) (f:V->V) (g:V->V).
      continuous_linear add smul inner f /\
      continuous_linear add smul inner g /\
      (!x:V. g (f x) = x) /\
      (!x:V. f (g x) = x) in
  !zero:V.
  !add:V->V->V.
  !neg:V->V.
  !smul:real->V->V.
  !inner:V->V->real.
  !B:V->V->real.
    real_vector_space zero add neg smul /\
    real_inner_product zero add smul inner /\
    complete_space add neg inner /\
    bounded_bilinear add smul inner B /\
    coercive inner B
    ==> ?f g:V->V.
          continuous_linear_equivalence add smul inner f g /\
          (!v w:V. inner (f v) w = B v w)`;;
