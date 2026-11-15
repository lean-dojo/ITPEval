(*
  Statement-only formalization of Thousand Theorems corpus artifact Q3527215,
  "Hilbert projection theorem": every point in a real inner-product space has
  a nearest point in each nonempty complete convex subset. This file contains
  no proof.
*)

let Q3527215_HILBERT_PROJECTION_THEOREM =
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
  let induced_norm =
    \(inner:V->V->real) (norm:V->real).
      !x:V.
        &0 <= norm x /\
        norm x * norm x = inner x x in
  let sub =
    \(add:V->V->V) (neg:V->V) (x:V) (y:V).
      add x (neg y) in
  let cauchy_sequence =
    \(add:V->V->V) (neg:V->V) (norm:V->real)
     (s:num->V).
      !epsilon:real.
        &0 < epsilon
        ==> ?N:num. !m n:num.
              N <= m /\ N <= n
              ==> norm (sub add neg (s m) (s n)) < epsilon in
  let tends_to =
    \(add:V->V->V) (neg:V->V) (norm:V->real)
     (s:num->V) (v:V).
      !epsilon:real.
        &0 < epsilon
        ==> ?N:num. !n:num.
              N <= n
              ==> norm (sub add neg (s n) v) < epsilon in
  let complete_subset =
    \(add:V->V->V) (neg:V->V) (norm:V->real)
     (K:V->bool).
      !s:num->V.
        (!n:num. K (s n)) /\
        cauchy_sequence add neg norm s
        ==> ?v:V. K v /\ tends_to add neg norm s v in
  let convex_subset =
    \(add:V->V->V) (smul:real->V->V) (K:V->bool).
      !x y:V. !a b:real.
        K x /\ K y /\
        &0 <= a /\ &0 <= b /\ a + b = &1
        ==> K (add (smul a x) (smul b y)) in
  !zero:V. !add:V->V->V. !neg:V->V.
  !smul:real->V->V. !inner:V->V->real.
  !norm:V->real. !K:V->bool.
    real_vector_space zero add neg smul /\
    real_inner_product zero add smul inner /\
    induced_norm inner norm /\
    (?x:V. K x) /\
    complete_subset add neg norm K /\
    convex_subset add smul K
    ==> !u:V.
          ?v:V.
            K v /\
            norm (sub add neg u v) =
              inf {d:real |
                     ?w:V.
                       K w /\ d = norm (sub add neg u w)}`;;
