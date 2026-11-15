(*
  Statement-only formalization of Thousand Theorems corpus artifact Q5437947,
  "Fatou–Lebesgue theorem": the lower Lebesgue integral of the pointwise
  liminf of a sequence of measurable extended-nonnegative functions is at
  most the liminf of their lower Lebesgue integrals. This file contains no
  proof.
*)

let Q5437947_FATOU_LEBESGUE_THEOREM =
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
        then ezero
        else if FST x \/ FST y
        then (T,&0)
        else (F,SND x * SND y) in
   let esup_sequence =
      \(u:num->bool#real) (z:bool#real).
        enonnegative z /\
        (!n:num. enonnegative (u n) /\ ele (u n) z) /\
        (!w:bool#real.
           enonnegative w /\
           (!n:num. ele (u n) w)
           ==> ele z w) in
   let sigma_algebra =
      \(events:(A->bool)->bool).
        events {} /\
        events (:A) /\
        (!s:A->bool.
           events s ==> events ((:A) DIFF s)) /\
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
   let measurable_ennreal =
      \(events:(A->bool)->bool) (f:A->bool#real).
        (!x:A. enonnegative (f x)) /\
        (!c:real.
           &0 <= c ==> events {x:A | elt (F,c) (f x)}) in
   let simple_ennreal =
      \(events:(A->bool)->bool) (s:A->bool#real).
        (!x:A. enonnegative (s x)) /\
        FINITE (IMAGE s (:A)) /\
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
        finite_esum (IMAGE s (:A))
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
   let is_infimum =
      \(p:(bool#real)->bool) (z:bool#real).
        enonnegative z /\
        (!v:bool#real. p v ==> ele z v) /\
        (!w:bool#real.
           enonnegative w /\
           (!v:bool#real. p v ==> ele w v)
           ==> ele w z) in
   let lintegral =
      \(events:(A->bool)->bool)
       (mu:(A->bool)->bool#real)
       (f:A->bool#real).
        @z:bool#real.
          is_supremum
            (\v:bool#real.
               ?s:A->bool#real.
                 simple_ennreal events s /\
                 (!x:A. ele (s x) (f x)) /\
                 simple_lintegral mu s v)
            z in
   let eliminf =
      \(u:num->bool#real).
        @z:bool#real.
          is_supremum
            (\v:bool#real.
               ?n:num.
                 is_infimum
                   (\w:bool#real.
                      ?i:num. n <= i /\ w = u i)
                   v)
            z in
   !events:(A->bool)->bool
    mu:(A->bool)->bool#real
    f:num->A->bool#real.
      measure_space events mu /\
      (!n:num. measurable_ennreal events (f n))
      ==>
      ele
        (lintegral events mu
          (\x:A. eliminf (\n:num. f n x)))
        (eliminf
          (\n:num. lintegral events mu (f n)))`;;
