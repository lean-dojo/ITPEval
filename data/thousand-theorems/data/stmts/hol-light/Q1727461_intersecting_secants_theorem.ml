(*
  Statement-only formalization of Thousand Theorems corpus artifact Q1727461,
  "Intersecting secants theorem": in an arbitrary real inner-product affine
  space, two same-direction secants through a common point and with
  cospherical endpoints have equal products of endpoint distances. This file
  contains no proof.
*)

let Q1727461_INTERSECTING_SECANTS_THEOREM =
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
       (!q:P. vadd zero q = q) /\
       (!v w:V. !q:P.
          vadd (add v w) q = vadd v (vadd w q)) /\
       (!v:V. !q:P. vsub (vadd v q) q = v) /\
       (!q r:P. vadd (vsub q r) r = q) in
  let norm =
    \(inner:V->V->real) (x:V). sqrt (inner x x) in
  let distance =
    \(inner:V->V->real) (vsub:P->P->V) (q:P) (r:P).
       norm inner (vsub q r) in
  let zero_angle =
    \(zero:V) (inner:V->V->real) (vsub:P->P->V)
     (q1:P) (q2:P) (q3:P).
       ~(vsub q1 q2 = zero) /\
       ~(vsub q3 q2 = zero) /\
       inner (vsub q1 q2) (vsub q3 q2) =
         norm inner (vsub q1 q2) * norm inner (vsub q3 q2) in
  let cospherical_four =
    \(inner:V->V->real) (vsub:P->P->V)
     (a:P) (b:P) (c:P) (d:P).
       ?center:P. ?radius:real.
         distance inner vsub a center = radius /\
         distance inner vsub b center = radius /\
         distance inner vsub c center = radius /\
         distance inner vsub d center = radius in
  !zero:V.
  !add:V->V->V.
  !neg:V->V.
  !smul:real->V->V.
  !inner:V->V->real.
  !vadd:V->P->P.
  !vsub:P->P->V.
  !a b c d p:P.
    real_inner_product_space zero add neg smul inner /\
    affine_torsor zero add vadd vsub /\
    cospherical_four inner vsub a b c d /\
    ~(a = b) /\
    ~(c = d) /\
    zero_angle zero inner vsub a p b /\
    zero_angle zero inner vsub c p d
    ==>
    distance inner vsub a p * distance inner vsub b p =
    distance inner vsub c p * distance inner vsub d p`;;
