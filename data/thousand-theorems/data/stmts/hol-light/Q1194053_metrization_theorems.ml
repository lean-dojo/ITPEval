(*
  Statement-only formalization of Thousand Theorems corpus artifact Q1194053
  (thousand-theorems__hol-light__Q1194053), "Metrization theorems": every T3
  second-countable topological space admits a real-valued metric inducing
  exactly its given topology. This file contains no proof.
*)

let Q1194053_METRIZATION_THEOREMS =
  `let is_topology =
     \(carrier:A->bool) (open_sets:(A->bool)->bool).
       open_sets {} /\
       open_sets carrier /\
       (!U:A->bool. open_sets U ==> U SUBSET carrier) /\
       (!C:(A->bool)->bool.
          (!U:A->bool. U IN C ==> open_sets U)
          ==> open_sets (UNIONS C)) /\
       (!U V:A->bool.
          open_sets U /\ open_sets V
          ==> open_sets (U INTER V)) in
   let is_closed =
     \(carrier:A->bool) (open_sets:(A->bool)->bool) (C:A->bool).
       C SUBSET carrier /\ open_sets (carrier DIFF C) in
   let is_t0 =
     \(carrier:A->bool) (open_sets:(A->bool)->bool).
       !x y:A.
         x IN carrier /\ y IN carrier /\ ~(x = y)
         ==> ?U:A->bool.
               open_sets U /\
               ((x IN U /\ ~(y IN U)) \/
                (y IN U /\ ~(x IN U))) in
   let is_regular =
     \(carrier:A->bool) (open_sets:(A->bool)->bool).
       !C:A->bool.
       !x:A.
         is_closed carrier open_sets C /\
         x IN carrier /\
         ~(x IN C)
         ==> ?U V:A->bool.
               open_sets U /\
               open_sets V /\
               x IN U /\
               C SUBSET V /\
               U INTER V = {} in
   let is_second_countable =
     \(carrier:A->bool) (open_sets:(A->bool)->bool).
       ?basis:(A->bool)->bool.
         COUNTABLE basis /\
         (!V:A->bool. V IN basis ==> open_sets V) /\
         !U:A->bool.
           open_sets U
           ==> !x:A.
                 x IN U
                 ==> ?V:A->bool.
                       V IN basis /\
                       x IN V /\
                       V SUBSET U in
   let is_metric =
     \(carrier:A->bool) (d:A->A->real).
       (!x y:A.
          x IN carrier /\ y IN carrier
          ==> &0 <= d x y) /\
       (!x y:A.
          x IN carrier /\ y IN carrier
          ==> (d x y = &0 <=> x = y)) /\
       (!x y:A.
          x IN carrier /\ y IN carrier
          ==> d x y = d y x) /\
       (!x y z:A.
          x IN carrier /\ y IN carrier /\ z IN carrier
          ==> d x z <= d x y + d y z) in
   let induces_topology =
     \(carrier:A->bool) (open_sets:(A->bool)->bool)
      (d:A->A->real).
       !U:A->bool.
         open_sets U <=>
         U SUBSET carrier /\
         !x:A.
           x IN U
           ==> ?epsilon:real.
                 &0 < epsilon /\
                 !y:A.
                   y IN carrier /\ d x y < epsilon
                   ==> y IN U in
   let is_metrizable =
     \(carrier:A->bool) (open_sets:(A->bool)->bool).
       ?d:A->A->real.
         is_metric carrier d /\
         induces_topology carrier open_sets d in
   !carrier:A->bool.
   !open_sets:(A->bool)->bool.
     is_topology carrier open_sets /\
     is_t0 carrier open_sets /\
     is_regular carrier open_sets /\
     is_second_countable carrier open_sets
     ==> is_metrizable carrier open_sets`;;
