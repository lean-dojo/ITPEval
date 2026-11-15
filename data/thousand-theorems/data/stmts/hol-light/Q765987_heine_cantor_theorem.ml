(*
  Statement-only formalization of Thousand Theorems corpus artifact Q765987,
  "Heine–Cantor theorem": every continuous map from a compact uniform space
  to an arbitrary uniform space is uniformly continuous. This file contains
  no proof.
*)

let Q765987_HEINE_CANTOR_THEOREM =
  `let carrier_pairs_a =
     \(carrier:A->bool).
       {p:A#A | FST p IN carrier /\ SND p IN carrier} in
   let carrier_pairs_b =
     \(carrier:B->bool).
       {p:B#B | FST p IN carrier /\ SND p IN carrier} in
   let is_filter_a =
     \(carrier:A->bool) (u:((A#A)->bool)->bool).
       u (carrier_pairs_a carrier) /\
       (!r:(A#A)->bool.
          u r ==> r SUBSET carrier_pairs_a carrier) /\
       (!r s:(A#A)->bool.
          u r /\ r SUBSET s /\ s SUBSET carrier_pairs_a carrier
          ==> u s) /\
       (!r s:(A#A)->bool.
          u r /\ u s ==> u (r INTER s)) in
   let is_filter_b =
     \(carrier:B->bool) (u:((B#B)->bool)->bool).
       u (carrier_pairs_b carrier) /\
       (!r:(B#B)->bool.
          u r ==> r SUBSET carrier_pairs_b carrier) /\
       (!r s:(B#B)->bool.
          u r /\ r SUBSET s /\ s SUBSET carrier_pairs_b carrier
          ==> u s) /\
       (!r s:(B#B)->bool.
          u r /\ u s ==> u (r INTER s)) in
   let is_uniformity_a =
     \(carrier:A->bool) (u:((A#A)->bool)->bool).
       is_filter_a carrier u /\
       (!r:(A#A)->bool.
          u r ==> !x:A. x IN carrier ==> r (x,x)) /\
       (!r:(A#A)->bool.
          u r
          ==> u {p:A#A |
                   p IN carrier_pairs_a carrier /\
                   r (SND p,FST p)}) /\
       (!r:(A#A)->bool.
          u r
          ==> ?s:(A#A)->bool.
                u s /\
                !x y z:A.
                  x IN carrier /\ y IN carrier /\ z IN carrier /\
                  s (x,y) /\ s (y,z)
                  ==> r (x,z)) in
   let is_uniformity_b =
     \(carrier:B->bool) (u:((B#B)->bool)->bool).
       is_filter_b carrier u /\
       (!r:(B#B)->bool.
          u r ==> !x:B. x IN carrier ==> r (x,x)) /\
       (!r:(B#B)->bool.
          u r
          ==> u {p:B#B |
                   p IN carrier_pairs_b carrier /\
                   r (SND p,FST p)}) /\
       (!r:(B#B)->bool.
          u r
          ==> ?s:(B#B)->bool.
                u s /\
                !x y z:B.
                  x IN carrier /\ y IN carrier /\ z IN carrier /\
                  s (x,y) /\ s (y,z)
                  ==> r (x,z)) in
   let uniform_open_a =
     \(carrier:A->bool) (u:((A#A)->bool)->bool) (v:A->bool).
       v SUBSET carrier /\
       !x:A.
         x IN v
         ==> ?r:(A#A)->bool.
               u r /\
               !y:A.
                 y IN carrier /\ r (x,y)
                 ==> y IN v in
   let uniform_open_b =
     \(carrier:B->bool) (u:((B#B)->bool)->bool) (v:B->bool).
       v SUBSET carrier /\
       !x:B.
         x IN v
         ==> ?r:(B#B)->bool.
               u r /\
               !y:B.
                 y IN carrier /\ r (x,y)
                 ==> y IN v in
   let compact_uniform_space =
     \(carrier:A->bool) (u:((A#A)->bool)->bool).
       !cover:(A->bool)->bool.
         (!v:A->bool.
            v IN cover ==> uniform_open_a carrier u v) /\
         carrier SUBSET UNIONS cover
         ==> ?finite_cover:(A->bool)->bool.
               finite_cover SUBSET cover /\
               FINITE finite_cover /\
               carrier SUBSET UNIONS finite_cover in
   let continuous_between_uniform_spaces =
     \(carrier_a:A->bool) (carrier_b:B->bool)
      (u_a:((A#A)->bool)->bool)
      (u_b:((B#B)->bool)->bool) (f:A->B).
       (!x:A. x IN carrier_a ==> f x IN carrier_b) /\
       !v:B->bool.
         uniform_open_b carrier_b u_b v
         ==> uniform_open_a carrier_a u_a
               {x:A | x IN carrier_a /\ f x IN v} in
   let uniformly_continuous_between_uniform_spaces =
     \(carrier_a:A->bool) (carrier_b:B->bool)
      (u_a:((A#A)->bool)->bool)
      (u_b:((B#B)->bool)->bool) (f:A->B).
       (!x:A. x IN carrier_a ==> f x IN carrier_b) /\
       !r:(B#B)->bool.
         u_b r
         ==> u_a
               {p:A#A |
                  p IN carrier_pairs_a carrier_a /\
                  r (f (FST p),f (SND p))} in
   !carrier_a:A->bool.
   !carrier_b:B->bool.
   !u_a:((A#A)->bool)->bool.
   !u_b:((B#B)->bool)->bool.
   !f:A->B.
     is_uniformity_a carrier_a u_a /\
     is_uniformity_b carrier_b u_b /\
     compact_uniform_space carrier_a u_a /\
     continuous_between_uniform_spaces
       carrier_a carrier_b u_a u_b f
     ==> uniformly_continuous_between_uniform_spaces
           carrier_a carrier_b u_a u_b f`;;
