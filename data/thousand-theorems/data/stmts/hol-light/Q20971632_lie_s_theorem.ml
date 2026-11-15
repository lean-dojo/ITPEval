(*
  Statement-only formalization of Thousand Theorems corpus artifact Q20971632
  (thousand-theorems__hol-light__Q20971632), "Lie's theorem": a nonzero
  finite-dimensional triangularizable module for a solvable Lie algebra over
  a characteristic-zero field has a nonzero common weight vector. This file
  contains no proof.
*)

let Q20971632_LIES_THEOREM =
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
   let has_characteristic_zero =
     \(zeroK:'k) (oneK:'k) (addK:'k->'k->'k).
       !m n:num.
         ITLIST addK (REPLICATE m oneK) zeroK =
         ITLIST addK (REPLICATE n oneK) zeroK
         ==> m = n in
   let is_vector_space_L =
     \(zeroK:'k) (oneK:'k) (addK:'k->'k->'k)
      (mulK:'k->'k->'k) (zeroL:'l) (addL:'l->'l->'l)
      (negL:'l->'l) (smulL:'k->'l->'l).
       (!x:'l. addL zeroL x = x) /\
       (!x:'l. addL (negL x) x = zeroL) /\
       (!x y:'l. addL x y = addL y x) /\
       (!x y z:'l. addL (addL x y) z = addL x (addL y z)) /\
       (!x:'l. smulL oneK x = x) /\
       (!a b:'k. !x:'l.
          smulL (mulK a b) x = smulL a (smulL b x)) /\
       (!a b:'k. !x:'l.
          smulL (addK a b) x = addL (smulL a x) (smulL b x)) /\
       (!a:'k. !x y:'l.
          smulL a (addL x y) = addL (smulL a x) (smulL a y)) /\
       (!x:'l. smulL zeroK x = zeroL) /\
       (!a:'k. smulL a zeroL = zeroL) in
   let is_vector_space_V =
     \(zeroK:'k) (oneK:'k) (addK:'k->'k->'k)
      (mulK:'k->'k->'k) (zeroV:'v) (addV:'v->'v->'v)
      (negV:'v->'v) (smulV:'k->'v->'v).
       (!v:'v. addV zeroV v = v) /\
       (!v:'v. addV (negV v) v = zeroV) /\
       (!v w:'v. addV v w = addV w v) /\
       (!u v w:'v. addV (addV u v) w = addV u (addV v w)) /\
       (!v:'v. smulV oneK v = v) /\
       (!a b:'k. !v:'v.
          smulV (mulK a b) v = smulV a (smulV b v)) /\
       (!a b:'k. !v:'v.
          smulV (addK a b) v = addV (smulV a v) (smulV b v)) /\
       (!a:'k. !v w:'v.
          smulV a (addV v w) = addV (smulV a v) (smulV a w)) /\
       (!v:'v. smulV zeroK v = zeroV) /\
       (!a:'k. smulV a zeroV = zeroV) in
   let is_lie_algebra =
     \(zeroL:'l) (addL:'l->'l->'l) (smulL:'k->'l->'l)
      (bracket:'l->'l->'l).
       (!x:'l. bracket x x = zeroL) /\
       (!x y z:'l.
          bracket (addL x y) z =
          addL (bracket x z) (bracket y z)) /\
       (!x y z:'l.
          bracket x (addL y z) =
          addL (bracket x y) (bracket x z)) /\
       (!a:'k. !x y:'l.
          bracket (smulL a x) y = smulL a (bracket x y)) /\
       (!a:'k. !x y:'l.
          bracket x (smulL a y) = smulL a (bracket x y)) /\
       (!x y z:'l.
          bracket x (bracket y z) =
          addL (bracket (bracket x y) z)
               (bracket y (bracket x z))) in
   let is_lie_module =
     \(addL:'l->'l->'l) (smulL:'k->'l->'l)
      (addV:'v->'v->'v) (negV:'v->'v)
      (smulV:'k->'v->'v) (bracket:'l->'l->'l)
      (act:'l->'v->'v).
       (!x y:'l. !v:'v.
          act (addL x y) v = addV (act x v) (act y v)) /\
       (!x:'l. !v w:'v.
          act x (addV v w) = addV (act x v) (act x w)) /\
       (!a:'k. !x:'l. !v:'v.
          act (smulL a x) v = smulV a (act x v)) /\
       (!a:'k. !x:'l. !v:'v.
          act x (smulV a v) = smulV a (act x v)) /\
       (!x y:'l. !v:'v.
          act (bracket x y) v =
          addV (act x (act y v)) (negV (act y (act x v)))) in
   let is_subspace_L =
     \(zeroL:'l) (addL:'l->'l->'l) (smulL:'k->'l->'l)
      (p:'l->bool).
       p zeroL /\
       (!x y:'l. p x /\ p y ==> p (addL x y)) /\
       (!a:'k. !x:'l. p x ==> p (smulL a x)) in
   let is_solvable =
     \(zeroL:'l) (addL:'l->'l->'l) (smulL:'k->'l->'l)
      (bracket:'l->'l->'l).
       ?n:num. ?series:num->'l->bool.
         (!x:'l. series 0 x) /\
         (!i:num.
            i <= n ==> is_subspace_L zeroL addL smulL (series i)) /\
         (!i:num.
            i < n
            ==> !x y:'l.
                  series i x /\ series i y
                  ==> series (SUC i) (bracket x y)) /\
         (!x:'l. series n x <=> x = zeroL) in
   let is_basis_V =
     \(zeroK:'k) (zeroV:'v) (addV:'v->'v->'v)
      (smulV:'k->'v->'v) (n:num) (b:num->'v).
       (!c:num->'k.
          iterate addV {i:num | i < n} (\i. smulV (c i) (b i)) =
          zeroV
          ==> !i:num. i < n ==> c i = zeroK) /\
       (!v:'v.
          ?c:num->'k.
            v = iterate addV {i:num | i < n}
                  (\i. smulV (c i) (b i))) in
   let is_finite_dimensional =
     \(zeroK:'k) (zeroV:'v) (addV:'v->'v->'v)
      (smulV:'k->'v->'v).
       ?n:num. ?b:num->'v.
         is_basis_V zeroK zeroV addV smulV n b in
   let is_triangularizable =
     \(zeroK:'k) (zeroV:'v) (addV:'v->'v->'v)
      (smulV:'k->'v->'v) (act:'l->'v->'v).
       !x:'l.
         ?n:num. ?b:num->'v.
           is_basis_V zeroK zeroV addV smulV n b /\
           !j:num.
             j < n
             ==> ?c:num->'k.
                   act x (b j) =
                   iterate addV {i:num | i <= j}
                     (\i. smulV (c i) (b i)) in
   !zeroK oneK:'k.
   !addK mulK:'k->'k->'k.
   !negK invK:'k->'k.
   !zeroL:'l.
   !addL:'l->'l->'l.
   !negL:'l->'l.
   !smulL:'k->'l->'l.
   !bracket:'l->'l->'l.
   !zeroV:'v.
   !addV:'v->'v->'v.
   !negV:'v->'v.
   !smulV:'k->'v->'v.
   !act:'l->'v->'v.
     is_field zeroK oneK addK mulK negK invK /\
     has_characteristic_zero zeroK oneK addK /\
     is_vector_space_L
       zeroK oneK addK mulK zeroL addL negL smulL /\
     is_vector_space_V
       zeroK oneK addK mulK zeroV addV negV smulV /\
     is_lie_algebra zeroL addL smulL bracket /\
     is_lie_module addL smulL addV negV smulV bracket act /\
     is_solvable zeroL addL smulL bracket /\
     is_finite_dimensional zeroK zeroV addV smulV /\
     is_triangularizable zeroK zeroV addV smulV act /\
     (?v:'v. ~(v = zeroV))
     ==> ?chi:'l->'k. ?v:'v.
           chi zeroL = zeroK /\
           (!x y:'l. chi (addL x y) = addK (chi x) (chi y)) /\
           (!a:'k. !x:'l. chi (smulL a x) = mulK a (chi x)) /\
           ~(v = zeroV) /\
           (!x:'l. act x v = smulV (chi x) v)`;;
