(*
  Statement-only formalization of Thousand Theorems corpus artifact Q338886
  (thousand-theorems__hol-light__Q338886), "Divergence theorem": for a
  continuous vector field on a real box, differentiable off a countable
  subset of the interior with integrable Bochner-valued divergence, the
  integral of the divergence equals the signed sum of the face integrals.
  This file contains no proof.
*)

let Q338886_DIVERGENCE_THEOREM () =
 `let enonnegative =
      \(z:bool#real).
        (FST z /\ SND z = &0) \/
        (~(FST z) /\ &0 <= SND z) in
   let ezero = (F,&0) in
   let eadd =
      \(x:bool#real) (y:bool#real).
        if FST x \/ FST y
        then (T,&0)
        else (F,SND x + SND y) in
   let esup_sequence =
      \(u:num->bool#real) (z:bool#real).
        enonnegative z /\
        (!n. enonnegative (u n) /\
             (FST z \/ (~(FST (u n)) /\ SND (u n) <= SND z))) /\
        (!w. enonnegative w /\
             (!n. FST w \/
                  (~(FST (u n)) /\ SND (u n) <= SND w))
             ==> FST w \/ (~(FST z) /\ SND z <= SND w)) in
   let finite_real_product =
      \(d:num) (h:num->real).
        @z:real.
          ?partial:num->real.
            partial 0 = &1 /\
            (!i. i < d
                 ==> partial (SUC i) = partial i * h i) /\
            partial d = z in
   let finite_real_max =
      \(d:num) (h:num->real).
        @z:real.
          ?partial:num->real.
            partial 0 = &0 /\
            (!i. i < d
                 ==> partial (SUC i) =
                     if partial i <= h i then h i else partial i) /\
            partial d = z in
   let rvector =
      \(d:num) (x:num->real).
        !i. d <= i ==> x i = &0 in
   let rvector_norm =
      \(d:num) (x:num->real).
        finite_real_max d (\i. abs(x i)) in
   let avector =
      \(d:num) (zero:A) (x:num->A).
        !i. d <= i ==> x i = zero in
   let avector_norm =
      \(d:num) (norm:A->real) (x:num->A).
        finite_real_max d (\i. norm(x i)) in
   let closed_box =
      \(d:num) (a:num->real) (b:num->real).
        {x:num->real |
           rvector d x /\
           (!i. i < d ==> a i <= x i /\ x i <= b i)} in
   let open_box =
      \(d:num) (a:num->real) (b:num->real).
        {x:num->real |
           rvector d x /\
           (!i. i < d ==> a i < x i /\ x i < b i)} in
   let half_open_box =
      \(d:num) (a:num->real) (b:num->real).
        {x:num->real |
           rvector d x /\
           (!i. i < d ==> a i < x i /\ x i <= b i)} in
   let box_order =
      \(d:num) (a:num->real) (b:num->real).
        !i. i < d ==> a i <= b i in
   let remove_coordinate =
      \(i:num) (x:num->real) (j:num).
        if j < i then x j else x (SUC j) in
   let insert_coordinate =
      \(d:num) (i:num) (c:real) (x:num->real) (j:num).
        if d <= j then &0
        else if j < i then x j
        else if j = i then c
        else x (j - 1) in
   let basis_vector =
      \(i:num) (j:num).
        if j = i then &1 else &0 in
   let sigma_algebra =
      \(carrier:(num->real)->bool)
       (events:((num->real)->bool)->bool).
        events {} /\
        events carrier /\
        (!s:(num->real)->bool. events s ==> s SUBSET carrier) /\
        (!s:(num->real)->bool.
           events s ==> events (carrier DIFF s)) /\
        (!sets:num->(num->real)->bool.
           (!n. events (sets n))
           ==> events {x:num->real | ?n. x IN sets n}) in
   let measure_space =
      \(carrier:(num->real)->bool)
       (events:((num->real)->bool)->bool)
       (mu:((num->real)->bool)->bool#real).
        sigma_algebra carrier events /\
        (!s:(num->real)->bool. enonnegative (mu s)) /\
        mu {} = ezero /\
        (!sets:num->(num->real)->bool.
           (!n. events (sets n)) /\
           (!m n. ~(m = n) ==> DISJOINT (sets m) (sets n))
           ==> ?partial:num->bool#real.
                 partial 0 = ezero /\
                 (!n. partial (SUC n) =
                      eadd (partial n) (mu (sets n))) /\
                 esup_sequence partial
                   (mu {x:num->real | ?n. x IN sets n})) in
   let open_set =
      \(d:num) (u:(num->real)->bool).
        !x:num->real.
          x IN u
          ==> ?epsilon:real.
                &0 < epsilon /\
                !y:num->real.
                  rvector d y /\
                  rvector_norm d (\j. y j - x j) < epsilon
                  ==> y IN u in
   let borel_events =
      \(d:num) (events:((num->real)->bool)->bool).
        sigma_algebra (rvector d) events /\
        (!u:(num->real)->bool.
           open_set d u /\ u SUBSET rvector d ==> events u) /\
        (!other:((num->real)->bool)->bool.
           sigma_algebra (rvector d) other /\
           (!u:(num->real)->bool.
              open_set d u /\ u SUBSET rvector d ==> other u)
           ==> !s:(num->real)->bool.
                 events s ==> other s) in
   let lebesgue_measure_dimension =
      \(d:num) (events:((num->real)->bool)->bool)
       (mu:((num->real)->bool)->bool#real).
        borel_events d events /\
        measure_space (rvector d) events mu /\
        (!a b:num->real.
           rvector d a /\ rvector d b
           ==> mu (half_open_box d a b) =
               if box_order d a b
               then
                 (F,finite_real_product d (\i. b i - a i))
               else ezero) in
   let negligible =
      \(events:((num->real)->bool)->bool)
       (mu:((num->real)->bool)->bool#real)
       (s:(num->real)->bool).
        ?N:(num->real)->bool.
          events N /\ mu N = ezero /\ s SUBSET N in
   let measurable_finite =
      \(events:((num->real)->bool)->bool)
       (mu:((num->real)->bool)->bool#real)
       (s:(num->real)->bool).
        events s /\ ~(FST (mu s)) in
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
      \(carrier:(num->real)->bool)
       (events:((num->real)->bool)->bool)
       (s:(num->real)->real).
        FINITE (IMAGE s carrier) /\
        (!c:real.
           events {x:num->real | x IN carrier /\ s x = c}) in
   let simple_vector_on =
      \(carrier:(num->real)->bool)
       (events:((num->real)->bool)->bool)
       (s:(num->real)->A).
        FINITE (IMAGE s carrier) /\
        (!c:A.
           events {x:num->real | x IN carrier /\ s x = c}) in
   let strongly_measurable_vector_on =
      \(carrier:(num->real)->bool)
       (events:((num->real)->bool)->bool)
       (zero:A) (add:A->A->A) (neg:A->A) (norm:A->real)
       (h:(num->real)->A).
        ?s:num->(num->real)->A.
          (!n. simple_vector_on carrier events (s n)) /\
          (!x:num->real.
             x IN carrier
             ==> vector_tends zero add neg norm
                   (\n. s n x) (h x)) in
   let ae_strongly_measurable_vector_on =
      \(carrier:(num->real)->bool)
       (events:((num->real)->bool)->bool)
       (mu:((num->real)->bool)->bool#real)
       (zero:A) (add:A->A->A) (neg:A->A) (norm:A->real)
       (h:(num->real)->A).
        ?g:(num->real)->A.
          strongly_measurable_vector_on
            carrier events zero add neg norm g /\
          negligible events mu
            {x:num->real | x IN carrier /\ ~(h x = g x)} in
   let integrable_simple_scalar_on =
      \(carrier:(num->real)->bool)
       (events:((num->real)->bool)->bool)
       (mu:((num->real)->bool)->bool#real)
       (s:(num->real)->real).
        simple_scalar_on carrier events s /\
        (!c:real.
           c IN IMAGE s carrier /\ ~(c = &0)
           ==> measurable_finite events mu
                 {x:num->real | x IN carrier /\ s x = c}) in
   let integrable_simple_vector_on =
      \(carrier:(num->real)->bool)
       (events:((num->real)->bool)->bool)
       (mu:((num->real)->bool)->bool#real)
       (zero:A) (s:(num->real)->A).
        simple_vector_on carrier events s /\
        (!c:A.
           c IN IMAGE s carrier /\ ~(c = zero)
           ==> measurable_finite events mu
                 {x:num->real | x IN carrier /\ s x = c}) in
   let simple_scalar_integral_on =
      \(carrier:(num->real)->bool)
       (mu:((num->real)->bool)->bool#real)
       (s:(num->real)->real) (z:real).
        ?n enum partial.
          (!c:real.
             c IN IMAGE s carrier <=>
             ?i. i < n /\ enum i = c) /\
          (!i j. i < n /\ j < n /\ enum i = enum j ==> i = j) /\
          partial 0 = &0 /\
          (!i. i < n
               ==> partial (SUC i) =
                   SND
                     (mu {x:num->real |
                            x IN carrier /\ s x = enum i}) *
                   enum i + partial i) /\
          z = partial n in
   let simple_vector_integral_on =
      \(carrier:(num->real)->bool)
       (mu:((num->real)->bool)->bool#real)
       (zero:A) (add:A->A->A) (smul:real->A->A)
       (s:(num->real)->A) (z:A).
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
                       (SND
                         (mu {x:num->real |
                                x IN carrier /\ s x = enum i}))
                       (enum i))
                     (partial i)) /\
          z = partial n in
   let nonnegative_integral_upper_bound_on =
      \(carrier:(num->real)->bool)
       (events:((num->real)->bool)->bool)
       (mu:((num->real)->bool)->bool#real)
       (h:(num->real)->real) (u:real).
        !s:(num->real)->real z:real.
          integrable_simple_scalar_on carrier events mu s /\
          (!x:num->real.
             x IN carrier ==> &0 <= s x /\ s x <= h x) /\
          simple_scalar_integral_on carrier mu s z
          ==> z <= u in
   let has_nonnegative_integral_on =
      \(carrier:(num->real)->bool)
       (events:((num->real)->bool)->bool)
       (mu:((num->real)->bool)->bool#real)
       (h:(num->real)->real) (r:real).
        &0 <= r /\
        nonnegative_integral_upper_bound_on
          carrier events mu h r /\
        (!u:real.
           &0 <= u /\
           nonnegative_integral_upper_bound_on
             carrier events mu h u
           ==> r <= u) in
   let vector_integrable_on =
      \(carrier:(num->real)->bool)
       (events:((num->real)->bool)->bool)
       (mu:((num->real)->bool)->bool#real)
       (zero:A) (add:A->A->A) (neg:A->A) (norm:A->real)
       (h:(num->real)->A).
        ae_strongly_measurable_vector_on
          carrier events mu zero add neg norm h /\
        (?r:real.
           has_nonnegative_integral_on
             carrier events mu (\x:num->real. norm(h x)) r) in
   let has_bochner_integral_on =
      \(carrier:(num->real)->bool)
       (events:((num->real)->bool)->bool)
       (mu:((num->real)->bool)->bool#real)
       (zero:A) (add:A->A->A) (neg:A->A)
       (smul:real->A->A) (norm:A->real)
       (h:(num->real)->A) (z:A).
        ?s:num->(num->real)->A ints:num->A.
          (!n. integrable_simple_vector_on
                 carrier events mu zero (s n)) /\
          (!n. simple_vector_integral_on
                 carrier mu zero add smul (s n) (ints n)) /\
          (!e. &0 < e
               ==> ?N. !n. N <= n
                     ==> ?d:real.
                           has_nonnegative_integral_on
                             carrier events mu
                             (\x:num->real.
                                norm
                                  (add (s n x) (neg (h x)))) d /\
                           d < e) /\
          vector_tends zero add neg norm ints z in
   let bochner_integral_on =
      \(carrier:(num->real)->bool)
       (events:((num->real)->bool)->bool)
       (mu:((num->real)->bool)->bool#real)
       (zero:A) (add:A->A->A) (neg:A->A)
       (smul:real->A->A) (norm:A->real)
       (h:(num->real)->A).
        if complete_space zero add neg norm /\
           vector_integrable_on
             carrier events mu zero add neg norm h
        then @z:A.
               has_bochner_integral_on
                 carrier events mu zero add neg smul norm h z
        else zero in
   let finite_sum =
      \(zero:A) (add:A->A->A) (d:num) (h:num->A).
        @z:A.
          ?partial:num->A.
            partial 0 = zero /\
            (!i. i < d
                 ==> partial (SUC i) = add (partial i) (h i)) /\
            partial d = z in
   let divergence =
      \(zero:A) (add:A->A->A) (d:num)
       (f':(num->real)->(num->real)->num->A)
       (x:num->real).
        finite_sum zero add d
          (\i. f' x (basis_vector i) i) in
   let continuous_on =
      \(d:num) (add:A->A->A) (neg:A->A) (norm:A->real)
       (f:(num->real)->num->A)
       (carrier:(num->real)->bool).
        !x:num->real.
          x IN carrier
          ==> !e. &0 < e
                  ==> ?delta. &0 < delta /\
                      !y:num->real.
                        y IN carrier /\
                        rvector_norm d (\i. y i - x i) < delta
                        ==> avector_norm d norm
                              (\i. add (f y i) (neg (f x i))) < e in
   let bounded_linear =
      \(d:num) (zero:A) (add:A->A->A)
       (smul:real->A->A) (norm:A->real)
       (L:(num->real)->num->A).
        (!x:num->real.
           rvector d x ==> avector d zero (L x)) /\
        (!i. L (\j. &0) i = zero) /\
        (!x y:num->real.
           rvector d x /\ rvector d y
           ==> !i.
                 L (\j. x j + y j) i =
                 add (L x i) (L y i)) /\
        (!c:real x:num->real.
           rvector d x
           ==> !i.
                 L (\j. c * x j) i = smul c (L x i)) /\
        (?K:real.
           &0 <= K /\
           !x:num->real.
             rvector d x
             ==> avector_norm d norm (L x)
                 <= K * rvector_norm d x) in
   let has_frechet_derivative_at =
      \(d:num) (zero:A) (add:A->A->A) (neg:A->A)
       (smul:real->A->A) (norm:A->real)
       (f:(num->real)->num->A)
       (L:(num->real)->num->A) (x:num->real).
        bounded_linear d zero add smul norm L /\
        (!e. &0 < e
             ==> ?delta. &0 < delta /\
                 !y:num->real.
                   rvector d y /\
                   rvector_norm d (\i. y i - x i) < delta
                   ==> avector_norm d norm
                         (\i.
                            add
                              (add (f y i) (neg (f x i)))
                              (neg (L (\j. y j - x j) i)))
                       <= e * rvector_norm d (\j. y j - x j)) in
   !events:num->((num->real)->bool)->bool
    mu:num->((num->real)->bool)->bool#real
    zero:A
    add:A->A->A
    neg:A->A
    smul:real->A->A
    norm:A->real
    n:num
    a b:num->real
    f:(num->real)->num->A
    f':(num->real)->(num->real)->num->A
    exceptional:(num->real)->bool.
      (!d. lebesgue_measure_dimension d (events d) (mu d)) /\
      normed_real_vector_space zero add neg smul norm /\
      rvector (SUC n) a /\
      rvector (SUC n) b /\
      box_order (SUC n) a b /\
      exceptional SUBSET rvector (SUC n) /\
      COUNTABLE exceptional /\
      (!x:num->real.
         rvector (SUC n) x
         ==> avector (SUC n) zero (f x)) /\
      (!x:num->real.
         rvector (SUC n) x
         ==> bounded_linear
               (SUC n) zero add smul norm (f' x)) /\
      continuous_on
        (SUC n) add neg norm f (closed_box (SUC n) a b) /\
      (!x:num->real.
         x IN open_box (SUC n) a b /\ ~(x IN exceptional)
         ==> has_frechet_derivative_at
               (SUC n) zero add neg smul norm f (f' x) x) /\
      vector_integrable_on
        (closed_box (SUC n) a b)
        (events (SUC n)) (mu (SUC n))
        zero add neg norm
        (divergence zero add (SUC n) f')
      ==>
      bochner_integral_on
        (closed_box (SUC n) a b)
        (events (SUC n)) (mu (SUC n))
        zero add neg smul norm
        (divergence zero add (SUC n) f') =
      finite_sum zero add (SUC n)
        (\i.
           add
             (bochner_integral_on
               (closed_box n
                 (remove_coordinate i a)
                 (remove_coordinate i b))
               (events n) (mu n)
               zero add neg smul norm
               (\x:num->real.
                  f (insert_coordinate (SUC n) i (b i) x) i))
             (neg
               (bochner_integral_on
                 (closed_box n
                   (remove_coordinate i a)
                   (remove_coordinate i b))
                 (events n) (mu n)
                 zero add neg smul norm
                 (\x:num->real.
                    f (insert_coordinate (SUC n) i (a i) x) i))))`;;
