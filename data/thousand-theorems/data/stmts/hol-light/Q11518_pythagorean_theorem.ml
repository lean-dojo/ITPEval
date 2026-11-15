(*
  Statement-only formalization of Thousand Theorems corpus artifact Q11518,
  "Pythagorean theorem": in an arbitrary real inner-product affine space, the
  squared-distance identity holds exactly when the angle at the middle point
  is a right angle. This file contains no proof.
*)

let Q11518_PYTHAGOREAN_THEOREM =
 `let real_inner_product_space =
    \(zero:V) (add:V->V->V) (neg:V->V)
     (smul:real->V->V) (inner:V->V->real).
       (!x y z:V. add x (add y z) = add (add x y) z) /\
       (!x y:V. add x y = add y x) /\
       (!x:V. add zero x = x) /\
       (!x:V. add (neg x) x = zero) /\
       (!x:V. smul (&1) x = x) /\
       (!a b:real. !x:V. smul (a * b) x = smul a (smul b x)) /\
       (!a b:real. !x:V.
          smul (a + b) x = add (smul a x) (smul b x)) /\
       (!a:real. !x y:V.
          smul a (add x y) = add (smul a x) (smul a y)) /\
       (!x y:V. inner x y = inner y x) /\
       (!x y z:V.
          inner (add x y) z = inner x z + inner y z) /\
       (!a:real. !x y:V.
          inner (smul a x) y = a * inner x y) /\
       (!x:V. &0 <= inner x x) /\
       (!x:V. inner x x = &0 <=> x = zero) in
  let affine_torsor =
    \(zero:V) (add:V->V->V)
     (vadd:V->P->P) (vsub:P->P->V).
       (!p:P. vadd zero p = p) /\
       (!v w:V. !p:P.
          vadd (add v w) p = vadd v (vadd w p)) /\
       (!v:V. !p:P. vsub (vadd v p) p = v) /\
       (!p q:P. vadd (vsub p q) q = p) in
  let norm =
    \(inner:V->V->real) (x:V). sqrt (inner x x) in
  let distance =
    \(inner:V->V->real) (vsub:P->P->V) (p:P) (q:P).
       norm inner (vsub p q) in
  let vector_angle =
    \(inner:V->V->real) (x:V) (y:V).
       acs (inner x y / (norm inner x * norm inner y)) in
  let point_angle =
    \(inner:V->V->real) (vsub:P->P->V) (p1:P) (p2:P) (p3:P).
       vector_angle inner (vsub p1 p2) (vsub p3 p2) in
  !zero:V.
  !add:V->V->V.
  !neg:V->V.
  !smul:real->V->V.
  !inner:V->V->real.
  !vadd:V->P->P.
  !vsub:P->P->V.
  !p1 p2 p3:P.
    real_inner_product_space zero add neg smul inner /\
    affine_torsor zero add vadd vsub
    ==>
    (distance inner vsub p1 p3 * distance inner vsub p1 p3 =
       distance inner vsub p1 p2 * distance inner vsub p1 p2 +
       distance inner vsub p3 p2 * distance inner vsub p3 p2 <=>
     point_angle inner vsub p1 p2 p3 = pi / &2)`;;
