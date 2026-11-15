(*
  Statement-only formalization of "Lebesgue Measure and Integration" from
  Hundred Theorems artifact 086 (hundred-theorems__hol-light__086). It states
  monotonicity of the lower Lebesgue integral for arbitrary
  extended-nonnegative-valued functions on an arbitrary measure space. This
  file contains no proof.
*)

let HUNDRED_THEOREMS_086_LINTEGRAL_MONO =
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
   let esup_sequence =
      \(u:num->bool#real) (z:bool#real).
        enonnegative z /\
        (!n. enonnegative (u n) /\ ele (u n) z) /\
        (!w. enonnegative w /\ (!n. ele (u n) w) ==> ele z w) in
   let sigma_algebra =
      \(events:(A->bool)->bool).
        {} IN events /\
        (UNIV:A->bool) IN events /\
        (!s. s IN events ==> (UNIV:A->bool) DIFF s IN events) /\
        (!sets:num->A->bool.
           (!n. sets n IN events)
           ==> {x:A | ?n. x IN sets n} IN events) in
   let measure_space =
      \(events:(A->bool)->bool) (mu:(A->bool)->bool#real).
        sigma_algebra events /\
        (!s:A->bool. enonnegative (mu s)) /\
        mu {} = ezero /\
        (!sets:num->A->bool.
           (!n. sets n IN events) /\
           (!m n. ~(m = n) ==> DISJOINT (sets m) (sets n))
           ==> ?partial:num->bool#real.
                 partial 0 = ezero /\
                 (!n. partial (SUC n) =
                      eadd (partial n) (mu (sets n))) /\
                 esup_sequence partial
                   (mu {x:A | ?n. x IN sets n})) in
   let simple_function =
      \(events:(A->bool)->bool) (s:A->bool#real).
        (!x. enonnegative (s x)) /\
        FINITE (IMAGE s (UNIV:A->bool)) /\
        (!c:bool#real. {x:A | s x = c} IN events) in
   let finite_esum =
      \(items:(bool#real)->bool)
       (h:(bool#real)->bool#real) (z:bool#real).
        FINITE items /\
        (!x. x IN items ==> enonnegative (h x)) /\
        ?n enum partial.
          (!x. x IN items <=> ?i. i < n /\ enum i = x) /\
          (!i j. i < n /\ j < n /\ enum i = enum j ==> i = j) /\
          partial 0 = ezero /\
          (!i. i < n
               ==> partial (SUC i) =
                   eadd (h (enum i)) (partial i)) /\
          z = partial n in
   let simple_lintegral =
      \(mu:(A->bool)->bool#real) (s:A->bool#real) (z:bool#real).
        finite_esum (IMAGE s (UNIV:A->bool))
          (\c. emul c (mu {x:A | s x = c})) z in
   let is_supremum =
      \(p:(bool#real)->bool) (z:bool#real).
        enonnegative z /\
        (!v. p v ==> ele v z) /\
        (!w. enonnegative w /\ (!v. p v ==> ele v w)
             ==> ele z w) in
   let lintegral =
      \(events:(A->bool)->bool)
       (mu:(A->bool)->bool#real) (f:A->bool#real).
        @z:bool#real.
          is_supremum
            (\v. ?s:A->bool#real.
                   simple_function events s /\
                   (!x. ele (s x) (f x)) /\
                   simple_lintegral mu s v)
            z in
   !events:(A->bool)->bool
    mu:(A->bool)->bool#real
    f:A->bool#real
    g:A->bool#real.
      measure_space events mu /\
      (!x. enonnegative (f x)) /\
      (!x. enonnegative (g x)) /\
      (!x. ele (f x) (g x))
      ==> ele (lintegral events mu f) (lintegral events mu g)`;;
