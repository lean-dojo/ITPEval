(*
  Statement-only formalization of Thousand Theorems corpus artifact Q1477053
  (thousand-theorems__hol-light__Q1477053), "Arzelà–Ascoli theorem": an
  equicontinuous family of bounded continuous functions from a compact
  topological space into a metric space, with values in a common compact set,
  has compact closure in the uniform-convergence topology. This file contains
  no proof.
*)

let Q1477053_ARZEL_ASCOLI_THEOREM =
  `let is_topology =
     \(domain:A->bool) (opens:(A->bool)->bool).
       opens {} /\
       opens domain /\
       (!u:A->bool. opens u ==> u SUBSET domain) /\
       (!family:(A->bool)->bool.
          (!u:A->bool. u IN family ==> opens u)
          ==> opens (UNIONS family)) /\
       (!u v:A->bool.
          opens u /\ opens v ==> opens (u INTER v)) in
   let compact_topological_space =
     \(domain:A->bool) (opens:(A->bool)->bool).
       !cover:(A->bool)->bool.
         (!u:A->bool. u IN cover ==> opens u) /\
         domain SUBSET UNIONS cover
         ==> ?finite_cover:(A->bool)->bool.
               finite_cover SUBSET cover /\
               FINITE finite_cover /\
               domain SUBSET UNIONS finite_cover in
   let is_metric =
     \(codomain:B->bool) (d:B->B->real).
       (!x y:B.
          x IN codomain /\ y IN codomain
          ==> &0 <= d x y) /\
       (!x y:B.
          x IN codomain /\ y IN codomain
          ==> (d x y = &0 <=> x = y)) /\
       (!x y:B.
          x IN codomain /\ y IN codomain
          ==> d x y = d y x) /\
       (!x y z:B.
          x IN codomain /\ y IN codomain /\ z IN codomain
          ==> d x z <= d x y + d y z) in
   let metric_open =
     \(codomain:B->bool) (d:B->B->real) (u:B->bool).
       u SUBSET codomain /\
       !x:B.
         x IN u
         ==> ?epsilon:real.
               &0 < epsilon /\
               !y:B.
                 y IN codomain /\ d y x < epsilon
                 ==> y IN u in
   let compact_metric_subset =
     \(codomain:B->bool) (d:B->B->real) (s:B->bool).
       s SUBSET codomain /\
       !cover:(B->bool)->bool.
         (!u:B->bool. u IN cover ==> metric_open codomain d u) /\
         s SUBSET UNIONS cover
         ==> ?finite_cover:(B->bool)->bool.
               finite_cover SUBSET cover /\
               FINITE finite_cover /\
               s SUBSET UNIONS finite_cover in
   let continuous_into_metric =
     \(domain:A->bool) (opens:(A->bool)->bool)
      (codomain:B->bool) (d:B->B->real) (f:A->B).
       (!x:A. x IN domain ==> f x IN codomain) /\
       !v:B->bool.
         metric_open codomain d v
         ==> opens {x:A | x IN domain /\ f x IN v} in
   let bounded_continuous =
     \(domain:A->bool) (opens:(A->bool)->bool)
      (codomain:B->bool) (d:B->B->real) (f:A->B).
       continuous_into_metric domain opens codomain d f /\
       ?bound:real.
         &0 <= bound /\
         !x y:A.
           x IN domain /\ y IN domain
           ==> d (f x) (f y) <= bound in
   let uniformly_close =
     \(domain:A->bool) (d:B->B->real)
      (epsilon:real) (f:A->B) (g:A->B).
       !x:A. x IN domain ==> d (f x) (g x) < epsilon in
   let uniform_open =
     \(domain:A->bool) (bcf:(A->B)->bool)
      (d:B->B->real) (u:(A->B)->bool).
       u SUBSET bcf /\
       !f:A->B.
         f IN u
         ==> ?epsilon:real.
               &0 < epsilon /\
               !g:A->B.
                 g IN bcf /\
                 uniformly_close domain d epsilon f g
                 ==> g IN u in
   let uniform_closure =
     \(domain:A->bool) (bcf:(A->B)->bool)
      (d:B->B->real) (family:(A->B)->bool).
       {f:A->B |
          f IN bcf /\
          !epsilon:real.
            &0 < epsilon
            ==> ?g:A->B.
                  g IN family /\
                  uniformly_close domain d epsilon f g} in
   let compact_uniform_subset =
     \(domain:A->bool) (bcf:(A->B)->bool)
      (d:B->B->real) (compact_set:(A->B)->bool).
       compact_set SUBSET bcf /\
       !cover:((A->B)->bool)->bool.
         (!u:(A->B)->bool.
            u IN cover ==> uniform_open domain bcf d u) /\
         compact_set SUBSET UNIONS cover
         ==> ?finite_cover:((A->B)->bool)->bool.
               finite_cover SUBSET cover /\
               FINITE finite_cover /\
               compact_set SUBSET UNIONS finite_cover in
   let equicontinuous =
     \(domain:A->bool) (opens:(A->bool)->bool)
      (d:B->B->real) (family:(A->B)->bool).
       !x:A.
         x IN domain
         ==> !epsilon:real.
               &0 < epsilon
               ==> ?u:A->bool.
                     opens u /\
                     x IN u /\
                     !f:A->B.
                       f IN family
                       ==> !y:A.
                             y IN u
                             ==> d (f y) (f x) < epsilon in
   !domain:A->bool.
   !codomain:B->bool.
   !opens:(A->bool)->bool.
   !d:B->B->real.
   !s:B->bool.
   !family:(A->B)->bool.
     let bcf =
       {f:A->B |
          bounded_continuous domain opens codomain d f} in
     is_topology domain opens /\
     compact_topological_space domain opens /\
     is_metric codomain d /\
     compact_metric_subset codomain d s /\
     family SUBSET bcf /\
     (!f:A->B.
        f IN family
        ==> !x:A. x IN domain ==> f x IN s) /\
     equicontinuous domain opens d family
     ==> compact_uniform_subset domain bcf d
           (uniform_closure domain bcf d family)`;;
