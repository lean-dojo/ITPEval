(*
  Statement-only formalization of Thousand Theorems corpus artifact Q1097021,
  "Minkowski's theorem": a convex symmetric set whose Haar measure is larger
  than 2^n times the measure of a fundamental domain of a countable additive
  subgroup in an n-dimensional real normed vector space contains a nonzero
  subgroup element. This file contains no proof.
*)

let Q1097021_MINKOWSKI_THEOREM =
 `let enonnegative =
      \(z:bool#real).
        (FST z /\ SND z = &0) \/
        (~(FST z) /\ &0 <= SND z) in
   let ezero = (F,&0) in
   let ele =
      \(x:bool#real) (y:bool#real).
        FST y \/ (~(FST x) /\ SND x <= SND y) in
   let elt =
      \(x:bool#real) (y:bool#real).
        ~(FST x) /\ (FST y \/ SND x < SND y) in
   let eadd =
      \(x:bool#real) (y:bool#real).
        if FST x \/ FST y
        then (T,&0)
        else (F,SND x + SND y) in
   let emul =
      \(x:bool#real) (y:bool#real).
        if (~(FST x) /\ SND x = &0) \/
           (~(FST y) /\ SND y = &0)
        then (F,&0)
        else if FST x \/ FST y
        then (T,&0)
        else (F,SND x * SND y) in
   let esup_sequence =
      \(u:num->bool#real) (z:bool#real).
        enonnegative z /\
        (!i. enonnegative (u i) /\ ele (u i) z) /\
        (!w. enonnegative w /\ (!i. ele (u i) w) ==> ele z w) in
   let sigma_algebra =
      \(events:(A->bool)->bool).
        events {} /\
        events (UNIV:A->bool) /\
        (!t:A->bool. events t ==> events ((UNIV:A->bool) DIFF t)) /\
        (!sets:num->A->bool.
           (!i. events (sets i))
           ==> events {x:A | ?i. x IN sets i}) in
   let measure_space =
      \(events:(A->bool)->bool)
       (mu:(A->bool)->bool#real).
        sigma_algebra events /\
        (!t:A->bool. enonnegative (mu t)) /\
        mu {} = ezero /\
        (!s t:A->bool.
           events t /\ s SUBSET t ==> ele (mu s) (mu t)) /\
        (!s:A->bool. !z:bool#real.
           enonnegative z /\
           (!t:A->bool.
              events t /\ s SUBSET t ==> ele z (mu t))
           ==> ele z (mu s)) /\
        (!sets:num->A->bool.
           (!i. events (sets i)) /\
           (!i j. ~(i = j) ==> DISJOINT (sets i) (sets j))
           ==> ?partial:num->bool#real.
                 partial 0 = ezero /\
                 (!i. partial (SUC i) =
                      eadd (partial i) (mu (sets i))) /\
                 esup_sequence partial
                   (mu {x:A | ?i. x IN sets i})) in
   let almost_everywhere =
      \(events:(A->bool)->bool)
       (mu:(A->bool)->bool#real) (P:A->bool).
        ?N:A->bool.
          events N /\
          mu N = ezero /\
          {x:A | ~(P x)} SUBSET N in
   let null_measurable_set =
      \(events:(A->bool)->bool)
       (mu:(A->bool)->bool#real) (t:A->bool).
        ?u:A->bool.
          events u /\
          almost_everywhere events mu
            (\x:A. x IN t <=> x IN u) in
   let normed_real_vector_space =
      \(zero:A) (add:A->A->A) (neg:A->A)
       (smul:real->A->A) (norm:A->real).
        (!x y z:A. add (add x y) z = add x (add y z)) /\
        (!x y:A. add x y = add y x) /\
        (!x:A. add zero x = x) /\
        (!x:A. add (neg x) x = zero) /\
        (!x:A. smul (&1) x = x) /\
        (!a b:real. !x:A.
           smul (a * b) x = smul a (smul b x)) /\
        (!a b:real. !x:A.
           smul (a + b) x = add (smul a x) (smul b x)) /\
        (!a:real. !x y:A.
           smul a (add x y) = add (smul a x) (smul a y)) /\
        (!x:A. smul (&0) x = zero) /\
        (!a:real. smul a zero = zero) /\
        (!x:A. &0 <= norm x) /\
        (!x:A. norm x = &0 <=> x = zero) /\
        (!a:real. !x:A. norm (smul a x) = abs a * norm x) /\
        (!x y:A. norm (add x y) <= norm x + norm y) in
   let linear_combination =
      \(zero:A) (add:A->A->A) (smul:real->A->A)
       (n:num) (basis:num->A) (coeff:num->real) (x:A).
        ?partial:num->A.
          partial 0 = zero /\
          (!i. i < n
               ==> partial (SUC i) =
                   add (partial i) (smul (coeff i) (basis i))) /\
          partial n = x in
   let has_dimension =
      \(zero:A) (add:A->A->A) (smul:real->A->A)
       (n:num) (basis:num->A).
        (!x:A. ?coeff:num->real.
           linear_combination zero add smul n basis coeff x) /\
        (!c d:num->real. !x:A.
           linear_combination zero add smul n basis c x /\
           linear_combination zero add smul n basis d x
           ==> !i. i < n ==> c i = d i) in
   let open_set =
      \(add:A->A->A) (neg:A->A) (norm:A->real) (u:A->bool).
        !x:A.
          x IN u
          ==> ?e:real.
                &0 < e /\
                !y:A.
                  norm (add y (neg x)) < e ==> y IN u in
   let tends_to =
      \(add:A->A->A) (neg:A->A) (norm:A->real)
       (seq:num->A) (x:A).
        !e:real.
          &0 < e
          ==> ?N:num. !i:num.
                N <= i ==> norm (add (seq i) (neg x)) < e in
   let compact_set =
      \(add:A->A->A) (neg:A->A) (norm:A->real) (k:A->bool).
        !seq:num->A.
          (!i. seq i IN k)
          ==> ?sub:num->num. ?x:A.
                x IN k /\
                (!i. sub i < sub (SUC i)) /\
                tends_to add neg norm (\i. seq (sub i)) x in
   let borel_space =
      \(add:A->A->A) (neg:A->A) (norm:A->real)
       (events:(A->bool)->bool).
        sigma_algebra events /\
        (!u:A->bool.
           open_set add neg norm u ==> events u) /\
        (!other:(A->bool)->bool.
           sigma_algebra other /\
           (!u:A->bool.
              open_set add neg norm u ==> other u)
           ==> !t:A->bool. events t ==> other t) in
   let translate =
      \(add:A->A->A) (neg:A->A) (a:A) (t:A->bool).
        {x:A | add (neg a) x IN t} in
   let additive_subgroup =
      \(zero:A) (add:A->A->A) (neg:A->A) (L:A->bool).
        zero IN L /\
        (!x y:A. x IN L /\ y IN L ==> add x y IN L) /\
        (!x:A. x IN L ==> neg x IN L) in
   let is_add_haar_measure =
      \(zero:A) (add:A->A->A) (neg:A->A) (norm:A->real)
       (events:(A->bool)->bool)
       (mu:(A->bool)->bool#real).
        (!a:A. !t:A->bool.
           events t
           ==> mu (translate add neg a t) = mu t) /\
        (!k:A->bool.
           compact_set add neg norm k ==> ~(FST (mu k))) /\
        (!u:A->bool.
           open_set add neg norm u /\ ~(u = {})
           ==> ~(mu u = ezero)) in
   let ae_disjoint =
      \(events:(A->bool)->bool)
       (mu:(A->bool)->bool#real) (s:A->bool) (t:A->bool).
        almost_everywhere events mu
          (\x:A. ~(x IN s /\ x IN t)) in
   let is_add_fundamental_domain =
      \(add:A->A->A) (neg:A->A)
       (events:(A->bool)->bool)
       (mu:(A->bool)->bool#real)
       (L:A->bool) (fd:A->bool).
        null_measurable_set events mu fd /\
        almost_everywhere events mu
          (\x:A. ?g:A. g IN L /\ add g x IN fd) /\
        (!g h:A.
           g IN L /\ h IN L /\ ~(g = h)
           ==> ae_disjoint events mu
                 (translate add neg g fd)
                 (translate add neg h fd)) in
   let convex_set =
      \(add:A->A->A) (smul:real->A->A) (s:A->bool).
        !x y:A. !a b:real.
          x IN s /\ y IN s /\
          &0 <= a /\ &0 <= b /\ a + b = &1
          ==> add (smul a x) (smul b y) IN s in
   !zero:A.
   !add:A->A->A.
   !neg:A->A.
   !smul:real->A->A.
   !norm:A->real.
   !events:(A->bool)->bool.
   !mu:(A->bool)->bool#real.
   !L fd s:A->bool.
     normed_real_vector_space zero add neg smul norm /\
     borel_space add neg norm events /\
     measure_space events mu /\
     is_add_haar_measure zero add neg norm events mu /\
     additive_subgroup zero add neg L /\
     COUNTABLE L /\
     is_add_fundamental_domain add neg events mu L fd /\
     (!x:A. x IN s ==> neg x IN s) /\
     convex_set add smul s /\
     (?n:num. ?basis:num->A.
        has_dimension zero add smul n basis /\
        elt
          (emul (mu fd) (F,&2 pow n))
          (mu s))
     ==> ?x:A. x IN L /\ ~(x = zero) /\ x IN s`;;
