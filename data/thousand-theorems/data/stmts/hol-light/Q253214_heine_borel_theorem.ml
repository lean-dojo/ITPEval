(*
  Statement-only formalization of Thousand Theorems corpus artifact Q253214,
  "Heine–Borel theorem": in a proper Hausdorff pseudometric space, a subset is
  compact if and only if it is closed and bounded. This file contains no proof.
*)

let Q253214_HEINE_BOREL_THEOREM =
 `let is_pseudometric =
    \(carrier:A->bool) (d:A->A->real).
      (!x y:A.
         x IN carrier /\ y IN carrier
         ==> &0 <= d x y) /\
      (!x:A.
         x IN carrier
         ==> d x x = &0) /\
      (!x y:A.
         x IN carrier /\ y IN carrier
         ==> d x y = d y x) /\
      (!x y z:A.
         x IN carrier /\ y IN carrier /\ z IN carrier
         ==> d x z <= d x y + d y z) in
   let metric_open =
    \(carrier:A->bool) (d:A->A->real) (u:A->bool).
      u SUBSET carrier /\
      !x:A.
        x IN u
        ==> ?epsilon:real.
              &0 < epsilon /\
              !y:A.
                y IN carrier /\ d x y < epsilon
                ==> y IN u in
   let metric_closed =
    \(carrier:A->bool) (d:A->A->real) (s:A->bool).
      s SUBSET carrier /\
      metric_open carrier d (carrier DIFF s) in
   let metric_compact =
    \(carrier:A->bool) (d:A->A->real) (s:A->bool).
      s SUBSET carrier /\
      !cover:(A->bool)->bool.
        (!u:A->bool.
           u IN cover
           ==> metric_open carrier d u) /\
        s SUBSET UNIONS cover
        ==> ?finite_cover:(A->bool)->bool.
              finite_cover SUBSET cover /\
              FINITE finite_cover /\
              s SUBSET UNIONS finite_cover in
   let metric_bounded =
    \(d:A->A->real) (s:A->bool).
      ?bound:real.
        !x y:A.
          x IN s /\ y IN s
          ==> d x y <= bound in
   let hausdorff_metric_space =
    \(carrier:A->bool) (d:A->A->real).
      !x y:A.
        x IN carrier /\ y IN carrier /\ ~(x = y)
        ==> ?u v:A->bool.
              metric_open carrier d u /\
              metric_open carrier d v /\
              x IN u /\
              y IN v /\
              u INTER v = {} in
   let proper_metric_space =
    \(carrier:A->bool) (d:A->A->real).
      !x:A.
        x IN carrier
        ==> !radius:real.
              metric_compact carrier d
                {y:A | y IN carrier /\ d y x <= radius} in
   !carrier:A->bool.
   !d:A->A->real.
   !s:A->bool.
     is_pseudometric carrier d /\
     hausdorff_metric_space carrier d /\
     proper_metric_space carrier d /\
     s SUBSET carrier
     ==> (metric_compact carrier d s <=>
          metric_closed carrier d s /\
          metric_bounded d s)`;;
