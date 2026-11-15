(*
  Statement-only formalization of Thousand Theorems corpus artifact Q656198
  (thousand-theorems__hol-light__Q656198), "Maschke's theorem": for a finite
  group and a field in which the group order is nonzero, every submodule of a
  module over the group algebra has a complementary submodule. This file
  contains no proof.
*)

let Q656198_MASCHKES_THEOREM =
  `let is_field =
     \(zeroK:'k) (oneK:'k) (addK:'k->'k->'k)
      (mulK:'k->'k->'k) (negK:'k->'k) (invK:'k->'k).
       ~(zeroK = oneK) /\
       (!a:'k. addK zeroK a = a) /\
       (!a:'k. addK (negK a) a = zeroK) /\
       (!a b:'k. addK a b = addK b a) /\
       (!a b c:'k. addK (addK a b) c = addK a (addK b c)) /\
       (!a:'k. mulK oneK a = a) /\
       (!a b:'k. mulK a b = mulK b a) /\
       (!a b c:'k. mulK (mulK a b) c = mulK a (mulK b c)) /\
       (!a b c:'k.
          mulK a (addK b c) = addK (mulK a b) (mulK a c)) /\
       invK zeroK = zeroK /\
       (!a:'k. ~(a = zeroK) ==> mulK (invK a) a = oneK) in
   let is_group =
     \(idG:'g) (mulG:'g->'g->'g) (invG:'g->'g).
       (!g:'g. mulG idG g = g /\ mulG g idG = g) /\
       (!g:'g.
          mulG (invG g) g = idG /\ mulG g (invG g) = idG) /\
       (!g h j:'g.
          mulG (mulG g h) j = mulG g (mulG h j)) in
   let algebra_zero =
     \(zeroK:'k). \g:'g. zeroK in
   let algebra_one =
     \(zeroK:'k) (oneK:'k) (idG:'g).
       \g:'g. if g = idG then oneK else zeroK in
   let algebra_add =
     \(addK:'k->'k->'k) (a:'g->'k) (b:'g->'k).
       \g:'g. addK (a g) (b g) in
   let algebra_neg =
     \(negK:'k->'k) (a:'g->'k).
       \g:'g. negK (a g) in
   let algebra_mul =
     \(zeroK:'k) (addK:'k->'k->'k) (mulK:'k->'k->'k)
      (mulG:'g->'g->'g) (invG:'g->'g)
      (a:'g->'k) (b:'g->'k).
       \x:'g.
         iterate addK (UNIV:'g->bool)
           (\g:'g. mulK (a g) (b (mulG (invG g) x))) in
   let is_add_comm_group =
     \(zeroV:'v) (addV:'v->'v->'v) (negV:'v->'v).
       (!v:'v. addV zeroV v = v) /\
       (!v:'v. addV (negV v) v = zeroV) /\
       (!v w:'v. addV v w = addV w v) /\
       (!u v w:'v. addV (addV u v) w = addV u (addV v w)) in
   let is_group_algebra_module =
     \(zeroK:'k) (oneK:'k) (addK:'k->'k->'k)
      (mulK:'k->'k->'k) (negK:'k->'k)
      (idG:'g) (mulG:'g->'g->'g) (invG:'g->'g)
      (zeroV:'v) (addV:'v->'v->'v)
      (smul:('g->'k)->'v->'v).
       let zeroA = algebra_zero zeroK in
       let oneA = algebra_one zeroK oneK idG in
       let addA = algebra_add addK in
       let mulA = algebra_mul zeroK addK mulK mulG invG in
       (!v:'v. smul oneA v = v) /\
       (!a b:'g->'k. !v:'v.
          smul (mulA a b) v = smul a (smul b v)) /\
       (!a b:'g->'k. !v:'v.
          smul (addA a b) v = addV (smul a v) (smul b v)) /\
       (!a:'g->'k. !v w:'v.
          smul a (addV v w) = addV (smul a v) (smul a w)) /\
       (!v:'v. smul zeroA v = zeroV) /\
       (!a:'g->'k. smul a zeroV = zeroV) in
   let is_submodule =
     \(zeroV:'v) (addV:'v->'v->'v) (negV:'v->'v)
      (smul:('g->'k)->'v->'v) (p:'v->bool).
       p zeroV /\
       (!v w:'v. p v /\ p w ==> p (addV v w)) /\
       (!v:'v. p v ==> p (negV v)) /\
       (!a:'g->'k. !v:'v. p v ==> p (smul a v)) in
   let are_complements =
     \(zeroV:'v) (addV:'v->'v->'v)
      (p:'v->bool) (q:'v->bool).
       (!v:'v. (p v /\ q v) <=> v = zeroV) /\
       (!v:'v.
          ?vp vq:'v.
            p vp /\ q vq /\ v = addV vp vq) in
   !zeroK oneK:'k.
   !addK mulK:'k->'k->'k.
   !negK invK:'k->'k.
   !idG:'g.
   !mulG:'g->'g->'g.
   !invG:'g->'g.
   !zeroV:'v.
   !addV:'v->'v->'v.
   !negV:'v->'v.
   !smul:('g->'k)->'v->'v.
   !p:'v->bool.
     is_field zeroK oneK addK mulK negK invK /\
     FINITE (UNIV:'g->bool) /\
     is_group idG mulG invG /\
     ~(ITLIST addK
         (REPLICATE (CARD (UNIV:'g->bool)) oneK) zeroK = zeroK) /\
     is_add_comm_group zeroV addV negV /\
     is_group_algebra_module
       zeroK oneK addK mulK negK idG mulG invG zeroV addV smul /\
     is_submodule zeroV addV negV smul p
     ==> ?q:'v->bool.
           is_submodule zeroV addV negV smul q /\
           are_complements zeroV addV p q`;;
