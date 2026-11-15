(*
  Statement-only formalization of Thousand Theorems corpus artifact Q468391,
  "Bolzano–Weierstrass theorem": in a proper pseudometric space, every sequence
  that is frequently contained in a bounded set has a strictly monotone
  convergent subsequence whose limit lies in the set's closure; in particular,
  this holds when every term lies in the bounded set. This file contains no
  proof.
*)

let Q468391_BOLZANO_WEIERSTRASS_THEOREM =
  `let is_pseudometric =
     \(d:A->A->real).
       (!x y:A. &0 <= d x y) /\
       (!x:A. d x x = &0) /\
       (!x y:A. d x y = d y x) /\
       (!x y z:A. d x z <= d x y + d y z) in
   let metric_open =
     \(d:A->A->real) (u:A->bool).
       !x:A.
         x IN u
         ==> ?epsilon:real.
               &0 < epsilon /\
               !y:A. d y x < epsilon ==> y IN u in
   let metric_compact =
     \(d:A->A->real) (s:A->bool).
       !cover:(A->bool)->bool.
         (!u:A->bool. u IN cover ==> metric_open d u) /\
         s SUBSET UNIONS cover
         ==> ?finite_cover:(A->bool)->bool.
               finite_cover SUBSET cover /\
               FINITE finite_cover /\
               s SUBSET UNIONS finite_cover in
   let proper_pseudometric_space =
     \(d:A->A->real).
       !center:A.
       !radius:real.
         metric_compact d {y:A | d y center <= radius} in
   let metric_bounded =
     \(d:A->A->real) (s:A->bool).
       ?bound:real.
         !x y:A.
           x IN s /\ y IN s
           ==> d x y <= bound in
   let metric_closure =
     \(d:A->A->real) (s:A->bool).
       {a:A |
          !u:A->bool.
            metric_open d u /\ a IN u
            ==> ?y:A. y IN s /\ y IN u} in
   let frequently_in =
     \(s:A->bool) (x:num->A).
       !N:num.
         ?n:num. N <= n /\ x n IN s in
   let strict_mono =
     \(phi:num->num).
       !m n:num. m < n ==> phi m < phi n in
   let sequence_tends_to =
     \(d:A->A->real) (u:num->A) (a:A).
       !epsilon:real.
         &0 < epsilon
         ==> ?N:num.
               !n:num.
                 N <= n
                 ==> d (u n) a < epsilon in
   (!d:A->A->real.
    !s:A->bool.
    !x:num->A.
      is_pseudometric d /\
      proper_pseudometric_space d /\
      metric_bounded d s /\
      frequently_in s x
      ==> ?a:A.
            a IN metric_closure d s /\
            ?phi:num->num.
              strict_mono phi /\
              sequence_tends_to d (\n:num. x (phi n)) a) /\
   (!d:A->A->real.
    !s:A->bool.
    !x:num->A.
      is_pseudometric d /\
      proper_pseudometric_space d /\
      metric_bounded d s /\
      (!n:num. x n IN s)
      ==> ?a:A.
            a IN metric_closure d s /\
            ?phi:num->num.
              strict_mono phi /\
              sequence_tends_to d (\n:num. x (phi n)) a)`;;
