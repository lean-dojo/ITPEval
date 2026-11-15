(*
  Statement-only formalization of Thousand Theorems corpus artifact Q3527217
  (thousand-theorems__hol-light__Q3527217), "M. Riesz extension theorem":
  a linear functional on a subspace that is nonnegative on its intersection
  with a convex cone containing zero extends to the whole real vector space
  and remains nonnegative on the cone, provided the subspace plus the cone
  covers the ambient space. This file contains no proof.
*)

let Q3527217_M_RIESZ_EXTENSION_THEOREM =
 `let real_vector_space =
    \(zero:E) (add:E->E->E) (neg:E->E) (smul:real->E->E).
      (!x y z:E. add x (add y z) = add (add x y) z) /\
      (!x y:E. add x y = add y x) /\
      (!x:E. add zero x = x) /\
      (!x:E. add (neg x) x = zero) /\
      (!x:E. smul (&1) x = x) /\
      (!a b:real. !x:E.
         smul (a * b) x = smul a (smul b x)) /\
      (!a b:real. !x:E.
         smul (a + b) x = add (smul a x) (smul b x)) /\
      (!a:real. !x y:E.
         smul a (add x y) = add (smul a x) (smul a y)) in
  let real_subspace =
    \(zero:E) (add:E->E->E) (neg:E->E) (smul:real->E->E)
     (p:E->bool).
      zero IN p /\
      (!x y:E. x IN p /\ y IN p ==> add x y IN p) /\
      (!x:E. x IN p ==> neg x IN p) /\
      (!a:real. !x:E. x IN p ==> smul a x IN p) in
  let pointed_cone =
    \(zero:E) (add:E->E->E) (smul:real->E->E) (s:E->bool).
      zero IN s /\
      (!x y:E. x IN s /\ y IN s ==> add x y IN s) /\
      (!a:real. &0 <= a ==> !x:E. x IN s ==> smul a x IN s) in
  let linear_on =
    \(zero:E) (add:E->E->E) (smul:real->E->E)
     (p:E->bool) (f:E->real).
      f zero = &0 /\
      (!x y:E.
         x IN p /\ y IN p ==> f (add x y) = f x + f y) /\
      (!a:real. !x:E.
         x IN p ==> f (smul a x) = a * f x) in
  let linear_functional =
    \(zero:E) (add:E->E->E) (smul:real->E->E)
     (g:E->real).
      g zero = &0 /\
      (!x y:E. g (add x y) = g x + g y) /\
      (!a:real. !x:E. g (smul a x) = a * g x) in
  !zero:E.
  !add:E->E->E.
  !neg:E->E.
  !smul:real->E->E.
  !p:E->bool.
  !s:E->bool.
  !f:E->real.
    real_vector_space zero add neg smul /\
    real_subspace zero add neg smul p /\
    pointed_cone zero add smul s /\
    linear_on zero add smul p f /\
    (!x:E. x IN p /\ x IN s ==> &0 <= f x) /\
    (!y:E. ?x:E. x IN p /\ add x y IN s)
    ==>
    ?g:E->real.
      linear_functional zero add smul g /\
      (!x:E. x IN p ==> g x = f x) /\
      (!x:E. x IN s ==> &0 <= g x)`;;
