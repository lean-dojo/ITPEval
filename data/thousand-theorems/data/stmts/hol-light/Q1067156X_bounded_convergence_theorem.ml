(*
  Statement-only formalization of Thousand Theorems corpus artifact Q1067156X,
  "Bounded convergence theorem": uniformly bounded continuous nonnegative
  functions converging almost everywhere along a countably generated filter,
  and pointwise in the sequence specialization, have convergent lower Lebesgue
  integrals for a finite measure. This file contains no proof.
*)

let Q1067156X_BOUNDED_CONVERGENCE_THEOREM =
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
   let emul =
      \(x:bool#real) (y:bool#real).
        if (~(FST x) /\ SND x = &0) \/
           (~(FST y) /\ SND y = &0)
        then (F,&0)
        else if FST x \/ FST y
        then (T,&0)
        else (F,SND x * SND y) in
   let eembed =
      \(z:bool#real).
        if FST z then &1 else SND z / (&1 + SND z) in
   let esup_sequence =
      \(u:num->bool#real) (z:bool#real).
        enonnegative z /\
        (!n:num. enonnegative (u n) /\ ele (u n) z) /\
        (!w:bool#real.
           enonnegative w /\ (!n:num. ele (u n) w)
           ==> ele z w) in
   let sigma_algebra =
      \(events:(A->bool)->bool).
        events {} /\
        events (UNIV:A->bool) /\
        (!s:A->bool.
           events s ==> events ((UNIV:A->bool) DIFF s)) /\
        (!sets:num->A->bool.
           (!n:num. events (sets n))
           ==> events {x:A | ?n:num. x IN sets n}) in
   let measure_space =
      \(events:(A->bool)->bool)
       (mu:(A->bool)->bool#real).
        sigma_algebra events /\
        (!s:A->bool. enonnegative (mu s)) /\
        mu {} = ezero /\
        (!sets:num->A->bool.
           (!n:num. events (sets n)) /\
           (!m n:num.
              ~(m = n) ==> DISJOINT (sets m) (sets n))
           ==> ?partial:num->bool#real.
                 partial 0 = ezero /\
                 (!n:num.
                    partial (SUC n) =
                    eadd (partial n) (mu (sets n))) /\
                 esup_sequence partial
                   (mu {x:A | ?n:num. x IN sets n})) in
   let finite_measure =
      \(mu:(A->bool)->bool#real).
        ~(FST (mu (UNIV:A->bool))) in
   let simple_function =
      \(events:(A->bool)->bool)
       (s:A->bool#real).
        (!x:A. enonnegative (s x)) /\
        FINITE (IMAGE s (UNIV:A->bool)) /\
        (!c:bool#real. events {x:A | s x = c}) in
   let finite_esum =
      \(items:(bool#real)->bool)
       (h:(bool#real)->bool#real) (z:bool#real).
        FINITE items /\
        (!x:bool#real.
           x IN items ==> enonnegative (h x)) /\
        ?n:num enum:num->bool#real partial:num->bool#real.
          (!x:bool#real.
             x IN items <=>
             ?i:num. i < n /\ enum i = x) /\
          (!i j:num.
             i < n /\ j < n /\ enum i = enum j ==> i = j) /\
          partial 0 = ezero /\
          (!i:num.
             i < n
             ==> partial (SUC i) =
                 eadd (h (enum i)) (partial i)) /\
          z = partial n in
   let simple_lintegral =
      \(mu:(A->bool)->bool#real)
       (s:A->bool#real) (z:bool#real).
        finite_esum (IMAGE s (UNIV:A->bool))
          (\c:bool#real.
             emul c (mu {x:A | s x = c})) z in
   let is_supremum =
      \(p:(bool#real)->bool) (z:bool#real).
        enonnegative z /\
        (!v:bool#real. p v ==> ele v z) /\
        (!w:bool#real.
           enonnegative w /\
           (!v:bool#real. p v ==> ele v w)
           ==> ele z w) in
   let lintegral =
      \(events:(A->bool)->bool)
       (mu:(A->bool)->bool#real) (f:A->real).
        @z:bool#real.
          is_supremum
            (\v:bool#real.
               ?s:A->bool#real.
                 simple_function events s /\
                 (!x:A. ele (s x) (F,f x)) /\
                 simple_lintegral mu s v)
            z in
   let is_topology =
      \(open_sets:(A->bool)->bool).
        open_sets {} /\
        open_sets (UNIV:A->bool) /\
        (!C:(A->bool)->bool.
           (!U:A->bool. U IN C ==> open_sets U)
           ==> open_sets (UNIONS C)) /\
        (!U V:A->bool.
           open_sets U /\ open_sets V
           ==> open_sets (U INTER V)) in
   let opens_measurable =
      \(open_sets:(A->bool)->bool)
       (events:(A->bool)->bool).
        !U:A->bool. open_sets U ==> events U in
   let real_open =
      \(U:real->bool).
        !y:real.
          y IN U
          ==> ?e:real.
                &0 < e /\
                !z:real. abs(z - y) < e ==> z IN U in
   let continuous_real =
      \(open_sets:(A->bool)->bool) (h:A->real).
        !U:real->bool.
          real_open U
          ==> open_sets {x:A | h x IN U} in
   let bounded_continuous_nonnegative =
      \(open_sets:(A->bool)->bool) (h:A->real).
        (!x:A. &0 <= h x) /\
        continuous_real open_sets h /\
        (?M:real. !x:A. abs(h x) <= M) in
   let almost_everywhere =
      \(events:(A->bool)->bool)
       (mu:(A->bool)->bool#real) (P:A->bool).
        ?N:A->bool.
          events N /\
          mu N = ezero /\
          {x:A | ~(P x)} SUBSET N in
   let is_filter =
      \(sets:(B->bool)->bool).
        sets (UNIV:B->bool) /\
        (!S U:B->bool.
           sets S /\ S SUBSET U ==> sets U) /\
        (!S U:B->bool.
           sets S /\ sets U ==> sets (S INTER U)) in
   let countably_generated =
      \(sets:(B->bool)->bool).
        ?basis:num->B->bool.
          !S:B->bool.
            sets S <=>
            ?n:num. basis n SUBSET S in
   let tends_to_nonnegative =
      \(sets:(B->bool)->bool)
       (u:B->real) (l:real).
        &0 <= l /\
        (!i:B. &0 <= u i) /\
        (!e:real.
           &0 < e
           ==> sets {i:B | abs(u i - l) < e}) in
   let etends =
      \(sets:(B->bool)->bool)
       (u:B->bool#real) (l:bool#real).
        enonnegative l /\
        (!i:B. enonnegative (u i)) /\
        (!e:real.
           &0 < e
           ==> sets
                 {i:B |
                    abs(eembed (u i) - eembed l) < e}) in
   let sequence_tends_nonnegative =
      \(u:num->real) (l:real).
        &0 <= l /\
        (!n:num. &0 <= u n) /\
        (!e:real.
           &0 < e
           ==> ?N:num.
                 !n:num. N <= n ==> abs(u n - l) < e) in
   let sequence_etends =
      \(u:num->bool#real) (l:bool#real).
        enonnegative l /\
        (!n:num. enonnegative (u n)) /\
        (!e:real.
           &0 < e
           ==> ?N:num.
                 !n:num.
                   N <= n
                   ==> abs(eembed (u n) - eembed l) < e) in
   let filter_form =
      !open_sets:(A->bool)->bool
       events:(A->bool)->bool
       mu:(A->bool)->bool#real
       sets:(B->bool)->bool
       fs:B->A->real
       c:real
       f:A->real.
        is_topology open_sets /\
        measure_space events mu /\
        finite_measure mu /\
        opens_measurable open_sets events /\
        is_filter sets /\
        countably_generated sets /\
        &0 <= c /\
        (!i:B.
           bounded_continuous_nonnegative open_sets (fs i)) /\
        sets
          {i:B |
             almost_everywhere events mu
               (\x:A. fs i x <= c)} /\
        (!x:A. &0 <= f x) /\
        almost_everywhere events mu
          (\x:A.
             tends_to_nonnegative sets
               (\i:B. fs i x) (f x))
        ==> etends sets
              (\i:B. lintegral events mu (fs i))
              (lintegral events mu f) in
   let sequence_form =
      !open_sets:(A->bool)->bool
       events:(A->bool)->bool
       mu:(A->bool)->bool#real
       fs:num->A->real
       c:real
       f:A->real.
        is_topology open_sets /\
        measure_space events mu /\
        finite_measure mu /\
        opens_measurable open_sets events /\
        &0 <= c /\
        (!n:num.
           bounded_continuous_nonnegative open_sets (fs n)) /\
        (!n:num. !x:A. fs n x <= c) /\
        (!x:A. &0 <= f x) /\
        (!x:A.
           sequence_tends_nonnegative
             (\n:num. fs n x) (f x))
        ==> sequence_etends
              (\n:num. lintegral events mu (fs n))
              (lintegral events mu f) in
   filter_form /\ sequence_form`;;
