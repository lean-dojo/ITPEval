(*
  Statement-only formalization of Thousand Theorems corpus artifact Q220680,
  "Banach fixed-point theorem": a contraction on a complete extended metric
  space has a fixed point approached by its iterates with the standard
  geometric error bound. This file contains no proof.
*)

let Q220680_BANACH_FIXED_POINT_THEOREM =
 `let enonnegative =
      \(z:bool#real).
        (FST z /\ SND z = &0) \/
        (~(FST z) /\ &0 <= SND z) in
   let ezero = (F,&0) in
   let etop = (T,&0) in
   let ele =
      \(z:bool#real) (w:bool#real).
        FST w \/ (~(FST z) /\ SND z <= SND w) in
   let elt =
      \(z:bool#real) (w:bool#real).
        ~(FST z) /\ (FST w \/ SND z < SND w) in
   let eadd =
      \(z:bool#real) (w:bool#real).
        if FST z \/ FST w
        then etop
        else (F,SND z + SND w) in
   let escale =
      \(c:real) (z:bool#real).
        if c = &0
        then ezero
        else if FST z
        then etop
        else (F,c * SND z) in
   let emetric_space =
      \(edist:A->A->bool#real).
        (!x y:A. enonnegative (edist x y)) /\
        (!x y:A. edist x y = ezero <=> x = y) /\
        (!x y:A. edist x y = edist y x) /\
        (!x y z:A.
           ele (edist x z) (eadd (edist x y) (edist y z))) in
   let emetric_tends =
      \(edist:A->A->bool#real) (u:num->A) (y:A).
        !e:real.
          &0 < e
          ==> ?N:num. !n:num.
                N <= n ==> elt (edist (u n) y) (F,e) in
   let emetric_cauchy =
      \(edist:A->A->bool#real) (u:num->A).
        !e:real.
          &0 < e
          ==> ?N:num. !m n:num.
                N <= m /\ N <= n
                ==> elt (edist (u m) (u n)) (F,e) in
   let complete_emetric_space =
      \(edist:A->A->bool#real).
        !u:num->A.
          emetric_cauchy edist u
          ==> ?y:A. emetric_tends edist u y in
   let contracting_with =
      \(K:real) (edist:A->A->bool#real) (f:A->A).
        &0 <= K /\
        K < &1 /\
        !x y:A.
          ele (edist (f x) (f y)) (escale K (edist x y)) in
   let iterate_from =
      \(f:A->A) (x:A) (u:num->A).
        u 0 = x /\
        !n:num. u (SUC n) = f (u n) in
   !edist:A->A->bool#real.
   !f:A->A.
   !K:real.
   !x:A.
     emetric_space edist /\
     complete_emetric_space edist /\
     contracting_with K edist f /\
     ~(FST (edist x (f x)))
     ==> ?y:A. ?u:num->A.
           f y = y /\
           iterate_from f x u /\
           emetric_tends edist u y /\
           !n:num.
             ele (edist (u n) y)
               (F,SND (edist x (f x)) * K pow n / (&1 - K))`;;
