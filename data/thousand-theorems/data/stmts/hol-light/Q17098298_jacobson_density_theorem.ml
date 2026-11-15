(*
  Statement-only formalization of Thousand Theorems corpus artifact Q17098298
  (thousand-theorems__hol-light__Q17098298), "Jacobson density theorem": on a
  semisimple left module, every endomorphism linear over the ring of
  module endomorphisms agrees on each finite set with multiplication by one
  scalar from the original ring. This file contains no proof.
*)

let Q17098298_JACOBSON_DENSITY_THEOREM =
  `let is_ring =
     \(zeroR:'r) (oneR:'r) (addR:'r->'r->'r)
      (mulR:'r->'r->'r) (negR:'r->'r).
       (!x:'r. addR zeroR x = x) /\
       (!x:'r. addR (negR x) x = zeroR) /\
       (!x y:'r. addR x y = addR y x) /\
       (!x y z:'r. addR (addR x y) z = addR x (addR y z)) /\
       (!x:'r. mulR oneR x = x /\ mulR x oneR = x) /\
       (!x y z:'r. mulR (mulR x y) z = mulR x (mulR y z)) /\
       (!x y z:'r.
          mulR x (addR y z) = addR (mulR x y) (mulR x z)) /\
       (!x y z:'r.
          mulR (addR x y) z = addR (mulR x z) (mulR y z)) in
   let is_add_comm_group =
     \(zeroM:'m) (addM:'m->'m->'m) (negM:'m->'m).
       (!x:'m. addM zeroM x = x) /\
       (!x:'m. addM (negM x) x = zeroM) /\
       (!x y:'m. addM x y = addM y x) /\
       (!x y z:'m. addM (addM x y) z = addM x (addM y z)) in
   let is_left_module =
     \(zeroR:'r) (oneR:'r) (addR:'r->'r->'r)
      (mulR:'r->'r->'r) (zeroM:'m) (addM:'m->'m->'m)
      (smul:'r->'m->'m).
       (!x:'m. smul oneR x = x) /\
       (!a b:'r. !x:'m. smul (mulR a b) x = smul a (smul b x)) /\
       (!a b:'r. !x:'m.
          smul (addR a b) x = addM (smul a x) (smul b x)) /\
       (!a:'r. !x y:'m.
          smul a (addM x y) = addM (smul a x) (smul a y)) /\
       (!x:'m. smul zeroR x = zeroM) /\
       (!a:'r. smul a zeroM = zeroM) in
   let is_submodule =
     \(zeroM:'m) (addM:'m->'m->'m) (negM:'m->'m)
      (smul:'r->'m->'m) (N:'m->bool).
       N zeroM /\
       (!x y:'m. N x /\ N y ==> N (addM x y)) /\
       (!x:'m. N x ==> N (negM x)) /\
       (!a:'r. !x:'m. N x ==> N (smul a x)) in
   let is_semisimple_module =
     \(zeroM:'m) (addM:'m->'m->'m) (negM:'m->'m)
      (smul:'r->'m->'m).
       !N:'m->bool.
         is_submodule zeroM addM negM smul N
         ==> ?K:'m->bool.
               is_submodule zeroM addM negM smul K /\
               (!x:'m. N x /\ K x <=> x = zeroM) /\
               (!x:'m.
                  ?n k:'m. N n /\ K k /\ x = addM n k) in
   let is_R_linear =
     \(zeroM:'m) (addM:'m->'m->'m) (smul:'r->'m->'m)
      (g:'m->'m).
       g zeroM = zeroM /\
       (!x y:'m. g (addM x y) = addM (g x) (g y)) /\
       (!a:'r. !x:'m. g (smul a x) = smul a (g x)) in
   let is_endomorphism_ring_linear =
     \(zeroM:'m) (addM:'m->'m->'m) (smul:'r->'m->'m)
      (f:'m->'m).
       f zeroM = zeroM /\
       (!x y:'m. f (addM x y) = addM (f x) (f y)) /\
       (!g:'m->'m.
          is_R_linear zeroM addM smul g
          ==> !x:'m. f (g x) = g (f x)) in
   !zeroR oneR:'r.
   !addR mulR:'r->'r->'r.
   !negR:'r->'r.
   !zeroM:'m.
   !addM:'m->'m->'m.
   !negM:'m->'m.
   !smul:'r->'m->'m.
   !f:'m->'m.
   !s:'m->bool.
     is_ring zeroR oneR addR mulR negR /\
     is_add_comm_group zeroM addM negM /\
     is_left_module zeroR oneR addR mulR zeroM addM smul /\
     is_semisimple_module zeroM addM negM smul /\
     is_endomorphism_ring_linear zeroM addM smul f /\
     FINITE s
     ==> ?r:'r.
           !m:'m. m IN s ==> f m = smul r m`;;
