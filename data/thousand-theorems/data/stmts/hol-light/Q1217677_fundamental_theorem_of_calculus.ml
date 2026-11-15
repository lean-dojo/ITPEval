(*
  Statement-only formalization of Thousand Theorems corpus artifact Q1217677,
  "Fundamental theorem of calculus": the strict-derivative form of FTC-1 for
  Banach-valued Lebesgue interval integrals under local almost-everywhere
  strong measurability and an almost-everywhere endpoint limit, and the
  right-derivative form of FTC-2 for continuous Banach-valued functions.
  This file contains no proof.
*)

let Q1217677_FUNDAMENTAL_THEOREM_OF_CALCULUS =
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
      \(carrier:real->bool) (events:(real->bool)->bool).
        events {} /\
        events carrier /\
        (!s:real->bool. events s ==> s SUBSET carrier) /\
        (!s:real->bool.
           events s ==> events (carrier DIFF s)) /\
        (!sets:num->real->bool.
           (!n. events (sets n))
           ==> events {x:real | ?n. x IN sets n}) in
   let measure_space =
      \(carrier:real->bool) (events:(real->bool)->bool)
       (mu:(real->bool)->bool#real).
        sigma_algebra carrier events /\
        (!s:real->bool. enonnegative (mu s)) /\
        mu {} = ezero /\
        (!sets:num->real->bool.
           (!n. events (sets n)) /\
           (!m n. ~(m = n) ==> DISJOINT (sets m) (sets n))
           ==> ?partial:num->bool#real.
                 partial 0 = ezero /\
                 (!n. partial (SUC n) =
                      eadd (partial n) (mu (sets n))) /\
                 esup_sequence partial
                   (mu {x:real | ?n. x IN sets n})) in
   let borel_events =
      \(events:(real->bool)->bool).
        sigma_algebra (:real) events /\
        (!a b:real. events {x:real | a < x /\ x <= b}) /\
        (!other:(real->bool)->bool.
           sigma_algebra (:real) other /\
           (!a b:real. other {x:real | a < x /\ x <= b})
           ==> !s:real->bool. events s ==> other s) in
   let lebesgue_measure =
      \(events:(real->bool)->bool)
       (mu:(real->bool)->bool#real).
        borel_events events /\
        measure_space (:real) events mu /\
        (!a b:real.
           mu {x:real | a < x /\ x <= b} =
           if a <= b then (F,b - a) else ezero) in
   !events:(real->bool)->bool
    mu:(real->bool)->bool#real.
    lebesgue_measure events mu
    ==>
   (let real_lebesgue_measurable =
      \(s:real->bool). events s in
   let real_negligible =
      \(s:real->bool).
        ?N:real->bool.
          events N /\ mu N = ezero /\ s SUBSET N in
   let real_measurable =
      \(s:real->bool).
        events s /\ ~(FST (mu s)) in
   let real_measure =
      \(s:real->bool). SND (mu s) in
   let normed_real_vector_space =
      \(zero:A) (add:A->A->A) (neg:A->A)
       (smul:real->A->A) (norm:A->real).
        (!x y:A. add x y = add y x) /\
        (!x y z:A. add (add x y) z = add x (add y z)) /\
        (!x:A. add x zero = x) /\
        (!x:A. add x (neg x) = zero) /\
        (!x:A. neg (neg x) = x) /\
        (!x:A. smul (&1) x = x) /\
        (!a b:real x:A. smul (a * b) x = smul a (smul b x)) /\
        (!a b:real x:A.
           smul (a + b) x = add (smul a x) (smul b x)) /\
        (!a:real x y:A.
           smul a (add x y) = add (smul a x) (smul a y)) /\
        (!x:A. smul (&0) x = zero) /\
        (!a:real. smul a zero = zero) /\
        (!x:A. &0 <= norm x) /\
        (!x:A. norm x = &0 <=> x = zero) /\
        (!a:real x:A. norm (smul a x) = abs a * norm x) /\
        (!x y:A. norm (add x y) <= norm x + norm y) in
   let vector_tends =
      \(zero:A) (add:A->A->A) (neg:A->A) (norm:A->real)
       (u:num->A) (l:A).
        !e. &0 < e
            ==> ?N. !n. N <= n
                       ==> norm (add (u n) (neg l)) < e in
   let complete_space =
      \(zero:A) (add:A->A->A) (neg:A->A) (norm:A->real).
        !u:num->A.
          (!e. &0 < e
               ==> ?N. !m n.
                     N <= m /\ N <= n
                     ==> norm (add (u m) (neg (u n))) < e)
          ==> ?l:A. vector_tends zero add neg norm u l in
   let simple_scalar_on =
      \(carrier:real->bool) (s:real->real).
        FINITE (IMAGE s carrier) /\
        (!c:real.
           real_lebesgue_measurable
             {x:real | x IN carrier /\ s x = c}) in
   let simple_vector_on =
      \(carrier:real->bool) (s:real->A).
        FINITE (IMAGE s carrier) /\
        (!c:A.
           real_lebesgue_measurable
             {x:real | x IN carrier /\ s x = c}) in
   let strongly_measurable_vector_on =
      \(carrier:real->bool) (zero:A) (add:A->A->A)
       (neg:A->A) (norm:A->real) (h:real->A).
        ?s:num->real->A.
          (!n. simple_vector_on carrier (s n)) /\
          (!x:real.
             x IN carrier
             ==> vector_tends zero add neg norm
                   (\n. s n x) (h x)) in
   let ae_strongly_measurable_vector_on =
      \(carrier:real->bool) (zero:A) (add:A->A->A)
       (neg:A->A) (norm:A->real) (h:real->A).
        ?g:real->A.
          strongly_measurable_vector_on
            carrier zero add neg norm g /\
          real_negligible
            {x:real | x IN carrier /\ ~(h x = g x)} in
   let integrable_simple_scalar_on =
      \(carrier:real->bool) (s:real->real).
        simple_scalar_on carrier s /\
        (!c:real.
           c IN IMAGE s carrier /\ ~(c = &0)
           ==> real_measurable
                 {x:real | x IN carrier /\ s x = c}) in
   let integrable_simple_vector_on =
      \(carrier:real->bool) (zero:A) (s:real->A).
        simple_vector_on carrier s /\
        (!c:A.
           c IN IMAGE s carrier /\ ~(c = zero)
           ==> real_measurable
                 {x:real | x IN carrier /\ s x = c}) in
   let simple_scalar_integral_on =
      \(carrier:real->bool) (s:real->real) (z:real).
        ?n enum partial.
          (!c:real.
             c IN IMAGE s carrier <=>
             ?i. i < n /\ enum i = c) /\
          (!i j. i < n /\ j < n /\ enum i = enum j ==> i = j) /\
          partial 0 = &0 /\
          (!i. i < n
               ==> partial (SUC i) =
                   real_measure
                     {x:real |
                        x IN carrier /\ s x = enum i} *
                   enum i + partial i) /\
          z = partial n in
   let simple_vector_integral_on =
      \(carrier:real->bool) (zero:A) (add:A->A->A)
       (smul:real->A->A) (s:real->A) (z:A).
        ?n enum partial.
          (!c:A.
             c IN IMAGE s carrier <=>
             ?i. i < n /\ enum i = c) /\
          (!i j. i < n /\ j < n /\ enum i = enum j ==> i = j) /\
          partial 0 = zero /\
          (!i. i < n
               ==> partial (SUC i) =
                   add
                     (smul
                       (real_measure
                         {x:real |
                            x IN carrier /\ s x = enum i})
                       (enum i))
                     (partial i)) /\
          z = partial n in
   let nonnegative_integral_upper_bound_on =
      \(carrier:real->bool) (h:real->real) (u:real).
        !s:real->real z:real.
          integrable_simple_scalar_on carrier s /\
          (!x:real.
             x IN carrier ==> &0 <= s x /\ s x <= h x) /\
          simple_scalar_integral_on carrier s z
          ==> z <= u in
   let has_nonnegative_integral_on =
      \(carrier:real->bool) (h:real->real) (r:real).
        &0 <= r /\
        nonnegative_integral_upper_bound_on carrier h r /\
        (!u:real.
           &0 <= u /\
           nonnegative_integral_upper_bound_on carrier h u
           ==> r <= u) in
   let vector_integrable_on =
      \(carrier:real->bool) (zero:A) (add:A->A->A)
       (neg:A->A) (norm:A->real) (h:real->A).
        ae_strongly_measurable_vector_on
          carrier zero add neg norm h /\
        (?r:real.
           has_nonnegative_integral_on carrier
             (\x:real. norm(h x)) r) in
   let has_bochner_integral_on =
      \(carrier:real->bool) (zero:A) (add:A->A->A)
       (neg:A->A) (smul:real->A->A) (norm:A->real)
       (h:real->A) (z:A).
        ?s:num->real->A ints:num->A.
          (!n. integrable_simple_vector_on carrier zero (s n)) /\
          (!n. simple_vector_integral_on
                 carrier zero add smul (s n) (ints n)) /\
          (!e. &0 < e
               ==> ?N. !n. N <= n
                     ==> ?d:real.
                           has_nonnegative_integral_on carrier
                             (\x:real.
                                norm
                                  (add (s n x) (neg (h x)))) d /\
                           d < e) /\
          vector_tends zero add neg norm ints z in
   let bochner_integral_on =
      \(carrier:real->bool) (zero:A) (add:A->A->A)
       (neg:A->A) (smul:real->A->A) (norm:A->real)
       (h:real->A).
        if complete_space zero add neg norm /\
           vector_integrable_on
             carrier zero add neg norm h
        then @z:A.
               has_bochner_integral_on
                 carrier zero add neg smul norm h z
        else zero in
   let interval_integrable =
      \(zero:A) (add:A->A->A) (neg:A->A) (norm:A->real)
       (h:real->A) (a:real) (b:real).
        vector_integrable_on
          {x:real | a < x /\ x <= b} zero add neg norm h /\
        vector_integrable_on
          {x:real | b < x /\ x <= a} zero add neg norm h in
   let interval_integral =
      \(zero:A) (add:A->A->A) (neg:A->A)
       (smul:real->A->A) (norm:A->real)
       (h:real->A) (a:real) (b:real).
        add
          (bochner_integral_on
             {x:real | a < x /\ x <= b}
             zero add neg smul norm h)
          (neg
            (bochner_integral_on
              {x:real | b < x /\ x <= a}
              zero add neg smul norm h)) in
   let locally_ae_strongly_measurable_at =
      \(zero:A) (add:A->A->A) (neg:A->A) (norm:A->real)
       (h:real->A) (b:real).
        ?d. &0 < d /\
            ae_strongly_measurable_vector_on
              {x:real | abs(x - b) < d}
              zero add neg norm h in
   let ae_tends_at =
      \(zero:A) (add:A->A->A) (neg:A->A) (norm:A->real)
       (h:real->A) (b:real) (c:A).
        !e. &0 < e
            ==> ?d N.
                  &0 < d /\
                  real_negligible N /\
                  (!x:real.
                     abs(x - b) < d /\ ~(x IN N)
                     ==> norm (add (h x) (neg c)) < e) in
   let continuous_on =
      \(add:A->A->A) (neg:A->A) (norm:A->real)
       (h:real->A) (carrier:real->bool).
        !x. x IN carrier
            ==> !e. &0 < e
                    ==> ?d. &0 < d /\
                            !y. y IN carrier /\
                                abs(y - x) < d
                                ==> norm
                                      (add (h y) (neg (h x))) < e in
   let has_strict_derivative_at =
      \(add:A->A->A) (neg:A->A) (smul:real->A->A)
       (norm:A->real) (h:real->A) (c:A) (b:real).
        !e. &0 < e
            ==> ?d. &0 < d /\
                    !x y.
                      abs(x - b) < d /\ abs(y - b) < d
                      ==> norm
                            (add
                              (add (h x) (neg (h y)))
                              (neg (smul (x - y) c)))
                          <= e * abs(x - y) in
   let has_right_derivative_within =
      \(add:A->A->A) (neg:A->A) (smul:real->A->A)
       (norm:A->real) (h:real->A) (c:A) (x:real).
        !e. &0 < e
            ==> ?d. &0 < d /\
                    !y. x < y /\ abs(y - x) < d
                        ==> norm
                              (add
                                (add (h y) (neg (h x)))
                                (neg (smul (y - x) c)))
                            <= e * abs(y - x) in
   !zero:A
    add:A->A->A
    neg:A->A
    smul:real->A->A
    norm:A->real.
      normed_real_vector_space zero add neg smul norm /\
      complete_space zero add neg norm
      ==>
      ((!f:real->A c:A a b:real.
          interval_integrable zero add neg norm f a b /\
          locally_ae_strongly_measurable_at
            zero add neg norm f b /\
          ae_tends_at zero add neg norm f b c
          ==> has_strict_derivative_at
                add neg smul norm
                (\u. interval_integral
                       zero add neg smul norm f a u)
                c b) /\
       (!f f':real->A a b:real.
          a <= b /\
          continuous_on add neg norm f
            {x:real | a <= x /\ x <= b} /\
          (!x. a < x /\ x < b
               ==> has_right_derivative_within
                     add neg smul norm f (f' x) x) /\
          interval_integrable zero add neg norm f' a b
          ==> interval_integral
                zero add neg smul norm f' a b =
              add (f b) (neg (f a)))))`;;
