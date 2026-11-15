(*
  Statement-only formalization of Thousand Theorems corpus artifact Q1346677
  (thousand-theorems__hol-light__Q1346677), "Tietze extension theorem": every
  bounded continuous real-valued map on the domain of a closed embedding into
  a normal space has a bounded continuous extension with exactly the same
  supremum norm. This file contains no proof.
*)

let Q1346677_TIETZE_EXTENSION_THEOREM =
  `let is_topology_x =
     \(carrier:A->bool) (opens:(A->bool)->bool).
       opens {} /\
       opens carrier /\
       (!u:A->bool. opens u ==> u SUBSET carrier) /\
       (!c:(A->bool)->bool.
          (!u:A->bool. u IN c ==> opens u)
          ==> opens (UNIONS c)) /\
       (!u v:A->bool.
          opens u /\ opens v ==> opens (u INTER v)) in
   let is_topology_y =
     \(carrier:B->bool) (opens:(B->bool)->bool).
       opens {} /\
       opens carrier /\
       (!u:B->bool. opens u ==> u SUBSET carrier) /\
       (!c:(B->bool)->bool.
          (!u:B->bool. u IN c ==> opens u)
          ==> opens (UNIONS c)) /\
       (!u v:B->bool.
          opens u /\ opens v ==> opens (u INTER v)) in
   let closed_in_y =
     \(carrier:B->bool) (opens:(B->bool)->bool) (c:B->bool).
       c SUBSET carrier /\ opens (carrier DIFF c) in
   let normal_space =
     \(carrier:B->bool) (opens:(B->bool)->bool).
       !s t:B->bool.
         closed_in_y carrier opens s /\
         closed_in_y carrier opens t /\
         s INTER t = {}
         ==> ?u v:B->bool.
               opens u /\
               opens v /\
               s SUBSET u /\
               t SUBSET v /\
               u INTER v = {} in
   let real_open =
     \s:real->bool.
       !x:real.
         x IN s
         ==> ?epsilon:real.
               &0 < epsilon /\
               !y:real. abs(y - x) < epsilon ==> y IN s in
   let continuous_real_x =
     \(carrier:A->bool) (opens:(A->bool)->bool) (f:A->real).
       !u:real->bool.
         real_open u
         ==> opens {x:A | x IN carrier /\ f x IN u} in
   let continuous_real_y =
     \(carrier:B->bool) (opens:(B->bool)->bool) (f:B->real).
       !u:real->bool.
         real_open u
         ==> opens {y:B | y IN carrier /\ f y IN u} in
   let bounded_x =
     \(carrier:A->bool) (f:A->real).
       ?bound:real.
         !x:A. x IN carrier ==> abs(f x) <= bound in
   let bounded_y =
     \(carrier:B->bool) (f:B->real).
       ?bound:real.
         !y:B. y IN carrier ==> abs(f y) <= bound in
   let bounded_continuous_x =
     \(carrier:A->bool) (opens:(A->bool)->bool) (f:A->real).
       continuous_real_x carrier opens f /\ bounded_x carrier f in
   let bounded_continuous_y =
     \(carrier:B->bool) (opens:(B->bool)->bool) (f:B->real).
       continuous_real_y carrier opens f /\ bounded_y carrier f in
   let closed_embedding =
     \(carrier_x:A->bool) (opens_x:(A->bool)->bool)
      (carrier_y:B->bool) (opens_y:(B->bool)->bool) (e:A->B).
       (!x:A. x IN carrier_x ==> e x IN carrier_y) /\
       (!x y:A.
          x IN carrier_x /\ y IN carrier_x /\ e x = e y
          ==> x = y) /\
       (!u:A->bool.
          opens_x u <=>
          ?v:B->bool.
            opens_y v /\
            u = {x:A | x IN carrier_x /\ e x IN v}) /\
       closed_in_y carrier_y opens_y (IMAGE e carrier_x) in
   let is_sup_norm_x =
     \(carrier:A->bool) (f:A->real) (r:real).
       (carrier = {} /\ r = &0) \/
       (~(carrier = {}) /\
        (!x:A. x IN carrier ==> abs(f x) <= r) /\
        (!upper:real.
           (!x:A. x IN carrier ==> abs(f x) <= upper)
           ==> r <= upper)) in
   let is_sup_norm_y =
     \(carrier:B->bool) (f:B->real) (r:real).
       (carrier = {} /\ r = &0) \/
       (~(carrier = {}) /\
        (!y:B. y IN carrier ==> abs(f y) <= r) /\
        (!upper:real.
           (!y:B. y IN carrier ==> abs(f y) <= upper)
           ==> r <= upper)) in
   !carrier_x:A->bool.
   !carrier_y:B->bool.
   !opens_x:(A->bool)->bool.
   !opens_y:(B->bool)->bool.
   !f:A->real.
   !e:A->B.
     is_topology_x carrier_x opens_x /\
     is_topology_y carrier_y opens_y /\
     normal_space carrier_y opens_y /\
     bounded_continuous_x carrier_x opens_x f /\
     closed_embedding carrier_x opens_x carrier_y opens_y e
     ==> ?g:B->real.
           bounded_continuous_y carrier_y opens_y g /\
           (?r:real.
              is_sup_norm_x carrier_x f r /\
              is_sup_norm_y carrier_y g r) /\
           (!x:A. x IN carrier_x ==> g (e x) = f x)`;;
