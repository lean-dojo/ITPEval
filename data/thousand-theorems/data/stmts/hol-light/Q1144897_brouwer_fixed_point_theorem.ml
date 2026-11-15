(*
  Statement-only formalization of Thousand Theorems corpus artifact Q1144897,
  "Brouwer fixed-point theorem": every continuous self-map of a nonempty
  compact convex subset of a finite-dimensional real normed vector space has
  a fixed point. This file contains no proof.
*)

let Q1144897_BROUWER_FIXED_POINT_THEOREM =
  `let real_normed_vector_space =
     \(zero:V) (add:V->V->V) (neg:V->V)
      (smul:real->V->V) (norm:V->real).
       (!x y z:V. add (add x y) z = add x (add y z)) /\
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
       (!a:real. smul a zero = zero) /\
       (!x:V. &0 <= norm x) /\
       (!x:V. norm x = &0 <=> x = zero) /\
       (!a:real. !x:V. norm (smul a x) = abs a * norm x) /\
       (!x y:V. norm (add x y) <= norm x + norm y) in
   let finite_linear_combination =
     \(zero:V) (add:V->V->V) (smul:real->V->V)
      (n:num) (basis:num->V) (coeff:num->real) (x:V).
       ?partial:num->V.
         partial 0 = zero /\
         (!i:num.
            i < n
            ==> partial (SUC i) =
                add (partial i) (smul (coeff i) (basis i))) /\
         partial n = x in
   let finite_dimensional =
     \(zero:V) (add:V->V->V) (smul:real->V->V).
       ?n:num. ?basis:num->V.
         !x:V.
           ?coeff:num->real.
             finite_linear_combination
               zero add smul n basis coeff x in
   let open_set =
     \(add:V->V->V) (neg:V->V) (norm:V->real)
      (u:V->bool).
       !x:V.
         x IN u
         ==> ?epsilon:real.
               &0 < epsilon /\
               !y:V.
                 norm (add y (neg x)) < epsilon
                 ==> y IN u in
   let compact_set =
     \(add:V->V->V) (neg:V->V) (norm:V->real)
      (s:V->bool).
       !cover:(V->bool)->bool.
         (!u:V->bool. u IN cover ==> open_set add neg norm u) /\
         s SUBSET UNIONS cover
         ==> ?subcover:(V->bool)->bool.
               subcover SUBSET cover /\
               FINITE subcover /\
               s SUBSET UNIONS subcover in
   let convex_set =
     \(add:V->V->V) (smul:real->V->V) (s:V->bool).
       !x y:V. !a b:real.
         x IN s /\
         y IN s /\
         &0 <= a /\
         &0 <= b /\
         a + b = &1
         ==> add (smul a x) (smul b y) IN s in
   let continuous_on =
     \(add:V->V->V) (neg:V->V) (norm:V->real)
      (f:V->V) (s:V->bool).
       !x:V.
         x IN s
         ==> !epsilon:real.
               &0 < epsilon
               ==> ?delta:real.
                     &0 < delta /\
                     !y:V.
                       y IN s /\
                       norm (add y (neg x)) < delta
                       ==> norm (add (f y) (neg (f x))) < epsilon in
   !zero:V.
   !add:V->V->V.
   !neg:V->V.
   !smul:real->V->V.
   !norm:V->real.
   !s:V->bool.
   !f:V->V.
     real_normed_vector_space zero add neg smul norm /\
     finite_dimensional zero add smul /\
     convex_set add smul s /\
     compact_set add neg norm s /\
     (?x:V. x IN s) /\
     continuous_on add neg norm f s /\
     (!x:V. x IN s ==> f x IN s)
     ==> ?x:V. x IN s /\ f x = x`;;
