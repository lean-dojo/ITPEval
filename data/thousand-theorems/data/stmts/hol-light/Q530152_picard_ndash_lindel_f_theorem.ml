(*
  Statement-only formalization of Thousand Theorems corpus artifact Q530152,
  "Picard–Lindelöf theorem": local existence for a time-dependent vector field
  on an arbitrary real Banach space under Lipschitz, continuity, norm-bound,
  and interval-size hypotheses. This file contains no proof.
*)

let Q530152_PICARD_LINDELOF_THEOREM =
  `let normed_real_vector_space =
     \(zero:A) (add:A->A->A) (neg:A->A)
      (smul:real->A->A) (norm:A->real).
       (!x y:A. add x y = add y x) /\
       (!x y z:A. add (add x y) z = add x (add y z)) /\
       (!x:A. add x zero = x) /\
       (!x:A. add x (neg x) = zero) /\
       (!x:A. neg (neg x) = x) /\
       (!x:A. smul (&1) x = x) /\
       (!c d:real x:A. smul (c * d) x = smul c (smul d x)) /\
       (!c d:real x:A.
          smul (c + d) x = add (smul c x) (smul d x)) /\
       (!c:real x y:A.
          smul c (add x y) = add (smul c x) (smul c y)) /\
       (!x:A. smul (&0) x = zero) /\
       (!c:real. smul c zero = zero) /\
       (!x:A. &0 <= norm x) /\
       (!x:A. norm x = &0 <=> x = zero) /\
       (!c:real x:A. norm (smul c x) = abs c * norm x) /\
       (!x y:A. norm (add x y) <= norm x + norm y) in
   let complete_space =
     \(add:A->A->A) (neg:A->A) (norm:A->real).
       !u:num->A.
         (!epsilon:real.
            &0 < epsilon
            ==> ?N:num.
                  !m n:num.
                    N <= m /\ N <= n
                    ==> norm (add (u m) (neg (u n))) < epsilon)
         ==> ?limit:A.
               !epsilon:real.
                 &0 < epsilon
                 ==> ?N:num.
                       !n:num.
                         N <= n
                         ==> norm
                               (add (u n) (neg limit)) < epsilon in
   let closed_interval =
     \(lo:real) (hi:real) (t:real). lo <= t /\ t <= hi in
   let closed_ball =
     \(add:A->A->A) (neg:A->A) (norm:A->real)
      (center:A) (radius:real) (y:A).
       norm (add y (neg center)) <= radius in
   let continuous_on_interval =
     \(add:A->A->A) (neg:A->A) (norm:A->real)
      (h:real->A) (lo:real) (hi:real).
       !t:real.
         closed_interval lo hi t
         ==> !epsilon:real.
               &0 < epsilon
               ==> ?delta:real.
                     &0 < delta /\
                     !s:real.
                       closed_interval lo hi s /\
                       abs(s - t) < delta
                       ==> norm (add (h s) (neg (h t))) < epsilon in
   let has_derivative_within_interval =
     \(add:A->A->A) (neg:A->A) (smul:real->A->A)
      (norm:A->real) (alpha:real->A) (v:A)
      (lo:real) (hi:real) (t:real).
       !epsilon:real.
         &0 < epsilon
         ==> ?delta:real.
               &0 < delta /\
               !s:real.
                 closed_interval lo hi s /\
                 abs(s - t) < delta
                 ==> norm
                       (add
                         (add (alpha s) (neg (alpha t)))
                         (neg (smul (s - t) v)))
                     <= epsilon * abs(s - t) in
   !zero:A.
   !add:A->A->A.
   !neg:A->A.
   !smul:real->A->A.
   !norm:A->real.
   !f:real->A->A.
   !tmin tmax t0:real.
   !x0 x:A.
   !a r L K:real.
     normed_real_vector_space zero add neg smul norm /\
     complete_space add neg norm /\
     &0 <= a /\ &0 <= r /\ &0 <= L /\ &0 <= K /\
     closed_interval tmin tmax t0 /\
     (!t:real.
        closed_interval tmin tmax t
        ==> !y z:A.
              closed_ball add neg norm x0 a y /\
              closed_ball add neg norm x0 a z
              ==> norm
                    (add (f t y) (neg (f t z)))
                  <= K * norm (add y (neg z))) /\
     (!y:A.
        closed_ball add neg norm x0 a y
        ==> continuous_on_interval
              add neg norm (\t. f t y) tmin tmax) /\
     (!t:real.
        closed_interval tmin tmax t
        ==> !y:A.
              closed_ball add neg norm x0 a y
              ==> norm (f t y) <= L) /\
     L * max (tmax - t0) (t0 - tmin) <= a - r /\
     closed_ball add neg norm x0 r x
     ==> ?alpha:real->A.
           alpha t0 = x /\
           !t:real.
             closed_interval tmin tmax t
             ==> has_derivative_within_interval
                   add neg smul norm alpha (f t (alpha t))
                   tmin tmax t`;;
