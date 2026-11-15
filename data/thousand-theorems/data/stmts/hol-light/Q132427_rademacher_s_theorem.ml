(*
  Statement-only formalization of Thousand Theorems corpus artifact Q132427,
  "Rademacher's theorem": a Lipschitz map between finite-dimensional real
  normed spaces is differentiable within a measurable set almost everywhere
  for an additive Haar measure restricted to that set. This file contains no
  proof.
*)

let Q132427_RADEMACHER_S_THEOREM =
 `let enonnegative =
      \(z:bool#real).
        (FST z /\ SND z = &0) \/
        (~(FST z) /\ &0 <= SND z) in
   let ezero = (F,&0) in
   let ele =
      \(x:bool#real) (y:bool#real).
        FST y \/ (~(FST x) /\ SND x <= SND y) in
   let eadd =
      \(x:bool#real) (y:bool#real).
        if FST x \/ FST y
        then (T,&0)
        else (F,SND x + SND y) in
   let esup_sequence =
      \(u:num->bool#real) (z:bool#real).
        enonnegative z /\
        (!n. enonnegative (u n) /\ ele (u n) z) /\
        (!w. enonnegative w /\ (!n. ele (u n) w) ==> ele z w) in
   let sigma_algebra =
      \(events:(E->bool)->bool).
        events {} /\
        events (:E) /\
        (!s:E->bool.
           events s ==> events ((:E) DIFF s)) /\
        (!sets:num->E->bool.
           (!n. events (sets n))
           ==> events {x:E | ?n. x IN sets n}) in
   let measure_space =
      \(events:(E->bool)->bool)
       (mu:(E->bool)->bool#real).
        sigma_algebra events /\
        (!s:E->bool. enonnegative (mu s)) /\
        mu {} = ezero /\
        (!s t:E->bool.
           events t /\ s SUBSET t ==> ele (mu s) (mu t)) /\
        (!s:E->bool. !z:bool#real.
           enonnegative z /\
           (!t:E->bool.
              events t /\ s SUBSET t ==> ele z (mu t))
           ==> ele z (mu s)) /\
        (!sets:num->E->bool.
           (!n. events (sets n)) /\
           (!m n. ~(m = n) ==> DISJOINT (sets m) (sets n))
           ==> ?partial:num->bool#real.
                 partial 0 = ezero /\
                 (!n.
                    partial (SUC n) =
                    eadd (partial n) (mu (sets n))) /\
                 esup_sequence partial
                   (mu {x:E | ?n. x IN sets n})) in
   let normed_real_vector_spaceE =
      \(zero:E) (add:E->E->E) (neg:E->E)
       (smul:real->E->E) (norm:E->real).
        (!x y z:E. add (add x y) z = add x (add y z)) /\
        (!x y:E. add x y = add y x) /\
        (!x:E. add zero x = x) /\
        (!x:E. add (neg x) x = zero) /\
        (!x:E. smul (&1) x = x) /\
        (!a b:real. !x:E.
           smul (a * b) x = smul a (smul b x)) /\
        (!a b:real. !x:E.
           smul (a + b) x = add (smul a x) (smul b x)) /\
        (!a:real. !x y:E.
           smul a (add x y) = add (smul a x) (smul a y)) /\
        (!x:E. smul (&0) x = zero) /\
        (!a:real. smul a zero = zero) /\
        (!x:E. &0 <= norm x) /\
        (!x:E. norm x = &0 <=> x = zero) /\
        (!a:real. !x:E. norm (smul a x) = abs a * norm x) /\
        (!x y:E. norm (add x y) <= norm x + norm y) in
   let normed_real_vector_spaceF =
      \(zero:F) (add:F->F->F) (neg:F->F)
       (smul:real->F->F) (norm:F->real).
        (!x y z:F. add (add x y) z = add x (add y z)) /\
        (!x y:F. add x y = add y x) /\
        (!x:F. add zero x = x) /\
        (!x:F. add (neg x) x = zero) /\
        (!x:F. smul (&1) x = x) /\
        (!a b:real. !x:F.
           smul (a * b) x = smul a (smul b x)) /\
        (!a b:real. !x:F.
           smul (a + b) x = add (smul a x) (smul b x)) /\
        (!a:real. !x y:F.
           smul a (add x y) = add (smul a x) (smul a y)) /\
        (!x:F. smul (&0) x = zero) /\
        (!a:real. smul a zero = zero) /\
        (!x:F. &0 <= norm x) /\
        (!x:F. norm x = &0 <=> x = zero) /\
        (!a:real. !x:F. norm (smul a x) = abs a * norm x) /\
        (!x y:F. norm (add x y) <= norm x + norm y) in
   let linear_combinationE =
      \(zero:E) (add:E->E->E) (smul:real->E->E)
       (n:num) (basis:num->E) (coeff:num->real) (x:E).
        ?partial:num->E.
          partial 0 = zero /\
          (!i.
             i < n
             ==> partial (SUC i) =
                 add (partial i) (smul (coeff i) (basis i))) /\
          partial n = x in
   let linear_combinationF =
      \(zero:F) (add:F->F->F) (smul:real->F->F)
       (n:num) (basis:num->F) (coeff:num->real) (x:F).
        ?partial:num->F.
          partial 0 = zero /\
          (!i.
             i < n
             ==> partial (SUC i) =
                 add (partial i) (smul (coeff i) (basis i))) /\
          partial n = x in
   let finite_dimensionalE =
      \(zero:E) (add:E->E->E) (smul:real->E->E).
        ?n:num. ?basis:num->E.
          (!x:E.
             ?coeff:num->real.
               linear_combinationE
                 zero add smul n basis coeff x) /\
          (!c d:num->real. !x:E.
             linear_combinationE zero add smul n basis c x /\
             linear_combinationE zero add smul n basis d x
             ==> !i. i < n ==> c i = d i) in
   let finite_dimensionalF =
      \(zero:F) (add:F->F->F) (smul:real->F->F).
        ?n:num. ?basis:num->F.
          (!x:F.
             ?coeff:num->real.
               linear_combinationF
                 zero add smul n basis coeff x) /\
          (!c d:num->real. !x:F.
             linear_combinationF zero add smul n basis c x /\
             linear_combinationF zero add smul n basis d x
             ==> !i. i < n ==> c i = d i) in
   let open_set =
      \(add:E->E->E) (neg:E->E) (norm:E->real)
       (u:E->bool).
        !x:E.
          x IN u
          ==> ?epsilon:real.
                &0 < epsilon /\
                !y:E.
                  norm (add y (neg x)) < epsilon
                  ==> y IN u in
   let tends_to =
      \(add:E->E->E) (neg:E->E) (norm:E->real)
       (seq:num->E) (x:E).
        !epsilon:real.
          &0 < epsilon
          ==> ?N:num.
                !n:num.
                  N <= n
                  ==> norm (add (seq n) (neg x)) < epsilon in
   let compact_set =
      \(add:E->E->E) (neg:E->E) (norm:E->real)
       (k:E->bool).
        !seq:num->E.
          (!n. seq n IN k)
          ==> ?sub:num->num. ?x:E.
                x IN k /\
                (!n. sub n < sub (SUC n)) /\
                tends_to add neg norm (\n. seq (sub n)) x in
   let borel_space =
      \(add:E->E->E) (neg:E->E) (norm:E->real)
       (events:(E->bool)->bool).
        sigma_algebra events /\
        (!u:E->bool.
           open_set add neg norm u ==> events u) /\
        (!other:(E->bool)->bool.
           sigma_algebra other /\
           (!u:E->bool.
              open_set add neg norm u ==> other u)
           ==> !s:E->bool.
                 events s ==> other s) in
   let translate =
      \(add:E->E->E) (neg:E->E) (a:E) (s:E->bool).
        {x:E | add (neg a) x IN s} in
   let is_add_haar_measure =
      \(add:E->E->E) (neg:E->E) (norm:E->real)
       (events:(E->bool)->bool)
       (mu:(E->bool)->bool#real).
        (!a:E. !s:E->bool.
           events s
           ==> mu (translate add neg a s) = mu s) /\
        (!k:E->bool.
           compact_set add neg norm k
           ==> ~(FST (mu k))) /\
        (!u:E->bool.
           open_set add neg norm u /\ ~(u = {})
           ==> ~(mu u = ezero)) in
   let bounded_linear =
      \(zeroE:E) (addE:E->E->E) (smulE:real->E->E)
       (zeroF:F) (addF:F->F->F) (smulF:real->F->F)
       (normE:E->real) (normF:F->real) (L:E->F).
        L zeroE = zeroF /\
        (!x y:E. L (addE x y) = addF (L x) (L y)) /\
        (!a:real. !x:E. L (smulE a x) = smulF a (L x)) /\
        (?K:real.
           &0 <= K /\
           !x:E. normF (L x) <= K * normE x) in
   let has_frechet_derivative_within_at =
      \(zeroE:E) (addE:E->E->E) (negE:E->E)
       (smulE:real->E->E) (normE:E->real)
       (zeroF:F) (addF:F->F->F) (negF:F->F)
       (smulF:real->F->F) (normF:F->real)
       (f:E->F) (s:E->bool) (x:E) (L:E->F).
        bounded_linear
          zeroE addE smulE zeroF addF smulF normE normF L /\
        (!epsilon:real.
           &0 < epsilon
           ==> ?delta:real.
                 &0 < delta /\
                 !y:E.
                   y IN s /\
                   normE (addE y (negE x)) < delta
                   ==>
                   normF
                     (addF
                       (addF (f y) (negF (f x)))
                       (negF (L (addE y (negE x)))))
                   <= epsilon * normE (addE y (negE x))) in
   let differentiable_within_at =
      \(zeroE:E) (addE:E->E->E) (negE:E->E)
       (smulE:real->E->E) (normE:E->real)
       (zeroF:F) (addF:F->F->F) (negF:F->F)
       (smulF:real->F->F) (normF:F->real)
       (f:E->F) (s:E->bool) (x:E).
        ?L:E->F.
          has_frechet_derivative_within_at
            zeroE addE negE smulE normE
            zeroF addF negF smulF normF f s x L in
   let lipschitz_on_with =
      \(addE:E->E->E) (negE:E->E) (normE:E->real)
       (addF:F->F->F) (negF:F->F) (normF:F->real)
       (C:real) (f:E->F) (s:E->bool).
        &0 <= C /\
        !x y:E.
          x IN s /\ y IN s
          ==> normF (addF (f x) (negF (f y)))
              <= C * normE (addE x (negE y)) in
   let restricted_measure =
      \(mu:(E->bool)->bool#real) (s:E->bool) (t:E->bool).
        mu {x:E | x IN t /\ x IN s} in
   let almost_everywhere =
      \(events:(E->bool)->bool)
       (mu:(E->bool)->bool#real)
       (P:E->bool).
        ?N:E->bool.
          events N /\
          mu N = ezero /\
          {x:E | ~(P x)} SUBSET N in
   !zeroE:E.
   !addE:E->E->E.
   !negE:E->E.
   !smulE:real->E->E.
   !normE:E->real.
   !zeroF:F.
   !addF:F->F->F.
   !negF:F->F.
   !smulF:real->F->F.
   !normF:F->real.
   !events:(E->bool)->bool.
   !mu:(E->bool)->bool#real.
   !C:real.
   !f:E->F.
   !s:E->bool.
     normed_real_vector_spaceE zeroE addE negE smulE normE /\
     normed_real_vector_spaceF zeroF addF negF smulF normF /\
     finite_dimensionalE zeroE addE smulE /\
     finite_dimensionalF zeroF addF smulF /\
     borel_space addE negE normE events /\
     measure_space events mu /\
     is_add_haar_measure addE negE normE events mu /\
     events s /\
     lipschitz_on_with
       addE negE normE addF negF normF C f s
     ==>
     almost_everywhere events (restricted_measure mu s)
       (\x:E.
          differentiable_within_at
            zeroE addE negE smulE normE
            zeroF addF negF smulF normF f s x)`;;
