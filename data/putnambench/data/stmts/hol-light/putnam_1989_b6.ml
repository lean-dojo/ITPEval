(*
  Statement-only formalization of PutnamBench corpus artifact putnam_1989_b6:
  the expected right-endpoint Riemann sum over the uniformly sampled ordered
  simplex is integration against a bounded degree-n polynomial independent of
  the continuous function. This file contains no proof.
*)

let statement =
  `let grid =
     \n m. {q:num list |
              LENGTH q = n /\
              (!i. i < n ==> 0 < EL i q /\ EL i q < m) /\
              (!i. i + 1 < n ==> EL i q < EL (i + 1) q)} in
   let coordinate =
     \n m (q:num list) i.
       if i = 0 then &0
       else if i = n + 1 then &1
       else &(EL (i - 1) q) / &m in
   let right_sum =
     \n m (f:real->real) (q:num list).
       sum (0..n)
         (\i. (coordinate n m q (i + 1) -
               coordinate n m q i) *
              f (coordinate n m q (i + 1))) in
   let polynomial =
     \n (p:real list) t.
       sum (0..n) (\k. EL k p * t pow k) in
   let simplex_average =
     \n (f:real->real) m.
       sum (grid n m) (\q. right_sum n m f q) /
       &(CARD (grid n m)) in
   let interval_average =
     \n (p:real list) (f:real->real) m.
       sum (0..m - 1)
         (\j. f (&(j + 1) / &m) *
              polynomial n p (&(j + 1) / &m)) /
       &m in
   let tends_to =
     \(u:num->real) L.
       !e. &0 < e
           ==> ?M. !m. M <= m ==> abs (u m - L) < e in
   let continuous_on_unit =
     \f:real->real.
       !x. &0 <= x /\ x <= &1
           ==> !e. &0 < e
                   ==> ?d. &0 < d /\
                           !y. &0 <= y /\ y <= &1 /\ abs (y - x) < d
                               ==> abs (f y - f x) < e in
   !n:num.
     1 <= n
     ==> ?p:real list.
           LENGTH p = n + 1 /\
           ~(LAST p = &0) /\
           (!t. &0 <= t /\ t <= &1
                ==> &0 <= polynomial n p t /\
                    polynomial n p t <= &1) /\
           (!f:real->real.
              continuous_on_unit f /\
              f (&1) = &0
              ==>
              ?L. tends_to (simplex_average n f) L /\
                  tends_to (interval_average n p f) L)`;;
