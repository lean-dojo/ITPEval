(*
  Statement-only formalization of Thousand Theorems corpus artifact Q877489,
  "Apollonius's theorem": in an arbitrary real inner-product affine space,
  the sum of the squared distances to two points is determined by their
  midpoint and half their mutual distance. This file contains no proof.
*)

let Q877489_APOLLONIUS_S_THEOREM =
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
  let midpoint =
    \(smul:real->V->V) (vadd:V->P->P) (vsub:P->P->V)
     (p:P) (q:P).
       vadd (smul (&1 / &2) (vsub q p)) p in
  !zero:V.
  !add:V->V->V.
  !neg:V->V.
  !smul:real->V->V.
  !inner:V->V->real.
  !vadd:V->P->P.
  !vsub:P->P->V.
  !a b c:P.
    real_inner_product_space zero add neg smul inner /\
    affine_torsor zero add vadd vsub
    ==>
    distance inner vsub a b pow 2 +
    distance inner vsub a c pow 2 =
    &2 *
    (distance inner vsub a (midpoint smul vadd vsub b c) pow 2 +
     (distance inner vsub b c / &2) pow 2)`;;
