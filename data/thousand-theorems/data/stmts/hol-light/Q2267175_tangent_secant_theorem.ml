(*
  Statement-only formalization of Thousand Theorems corpus artifact Q2267175
  (thousand-theorems__hol-light__Q2267175), "Tangent-secant theorem": in an
  arbitrary real inner-product affine space, the squared distance from a point
  to a tangent point of a sphere equals the product of its distances to two
  sphere points on a secant line. This file contains no proof.
*)

let Q2267175_TANGENT_SECANT_THEOREM =
 `let real_inner_product_space =
    \(zero:V) (add:V->V->V) (neg:V->V)
     (smul:real->V->V) (inner:V->V->real).
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
       (!q:P. vadd zero q = q) /\
       (!v w:V. !q:P.
          vadd (add v w) q = vadd v (vadd w q)) /\
       (!v:V. !q:P. vsub (vadd v q) q = v) /\
       (!q r:P. vadd (vsub q r) r = q) in
  let norm =
    \(inner:V->V->real) (v:V). sqrt (inner v v) in
  let distance =
    \(inner:V->V->real) (vsub:P->P->V) (q:P) (r:P).
       norm inner (vsub q r) in
  let affine_line =
    \(smul:real->V->V) (vsub:P->P->V)
     (q:P) (r:P) (x:P).
       ?c:real. vsub x q = smul c (vsub r q) in
  let sphere_mem =
    \(inner:V->V->real) (vsub:P->P->V)
     (center:P) (radius:real) (x:P).
       distance inner vsub x center = radius in
  let tangent_at =
    \(smul:real->V->V) (inner:V->V->real)
     (vsub:P->P->V) (center:P) (radius:real)
     (t:P) (p:P).
       sphere_mem inner vsub center radius t /\
       affine_line smul vsub p t t /\
       (!x:P.
          affine_line smul vsub p t x
          ==> inner (vsub x t) (vsub t center) = &0) in
  !zero:V.
  !add:V->V->V.
  !neg:V->V.
  !smul:real->V->V.
  !inner:V->V->real.
  !vadd:V->P->P.
  !vsub:P->P->V.
  !center:P.
  !radius:real.
  !a b t p:P.
    real_inner_product_space zero add neg smul inner /\
    affine_torsor zero add vadd vsub /\
    sphere_mem inner vsub center radius a /\
    sphere_mem inner vsub center radius b /\
    affine_line smul vsub a b p /\
    tangent_at smul inner vsub center radius t p
    ==>
    distance inner vsub p t pow 2 =
    distance inner vsub p a * distance inner vsub p b`;;
