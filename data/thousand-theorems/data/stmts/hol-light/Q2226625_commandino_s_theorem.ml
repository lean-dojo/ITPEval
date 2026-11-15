(*
  Statement-only formalization of Thousand Theorems corpus artifact Q2226625
  (thousand-theorems__hol-light__Q2226625), "Commandino's theorem": in an
  n-simplex over a characteristic-zero division ring, the
  centroid-to-vertex vector is n times the opposite-face-centroid-to-centroid
  vector. This file contains no proof.
*)

let Q2226625_COMMANDINOS_THEOREM =
 `!zeroK oneK:K.
   !addK mulK:K->K->K.
   !negK invK:K->K.
   !zeroV:V.
   !addV:V->V->V.
   !negV:V->V.
   !smul:K->V->V.
   !vadd:V->P->P.
   !vsub:P->P->V.
   !nat_cast:num->K.
   !ksum:num->(num->K)->K.
   !vsum:num->(num->V)->V.
   !n:num.
   !points:num->P.
   !i:num.
     let is_nat_cast = (
       nat_cast 0 = zeroK /\
       (!m:num.
          nat_cast (SUC m) = addK (nat_cast m) oneK)) in
     let is_ksum = (
       (!f:num->K. ksum 0 f = zeroK) /\
       (!m:num. !f:num->K.
          ksum (SUC m) f = addK (ksum m f) (f m))) in
     let is_vsum = (
       (!f:num->V. vsum 0 f = zeroV) /\
       (!m:num. !f:num->V.
          vsum (SUC m) f = addV (vsum m f) (f m))) in
     let is_division_ring = (
       ~(zeroK = oneK) /\
       (!a:K. addK zeroK a = a /\ addK a zeroK = a) /\
       (!a b:K. addK a b = addK b a) /\
       (!a b c:K.
          addK (addK a b) c = addK a (addK b c)) /\
       (!a:K.
          addK (negK a) a = zeroK /\
          addK a (negK a) = zeroK) /\
       (!a:K. mulK oneK a = a /\ mulK a oneK = a) /\
       (!a b c:K.
          mulK (mulK a b) c = mulK a (mulK b c)) /\
       (!a b c:K.
          mulK a (addK b c) =
          addK (mulK a b) (mulK a c)) /\
       (!a b c:K.
          mulK (addK a b) c =
          addK (mulK a c) (mulK b c)) /\
       (!a:K.
          mulK zeroK a = zeroK /\ mulK a zeroK = zeroK) /\
       invK zeroK = zeroK /\
       (!a:K.
          ~(a = zeroK)
          ==> mulK a (invK a) = oneK /\
              mulK (invK a) a = oneK)) in
     let has_characteristic_zero = (
       !a b:num. nat_cast a = nat_cast b ==> a = b) in
     let is_add_comm_group = (
       (!x:V. addV zeroV x = x /\ addV x zeroV = x) /\
       (!x y:V. addV x y = addV y x) /\
       (!x y z:V.
          addV (addV x y) z = addV x (addV y z)) /\
       (!x:V.
          addV (negV x) x = zeroV /\
          addV x (negV x) = zeroV)) in
     let is_module = (
       (!x:V. smul oneK x = x) /\
       (!a b:K. !x:V.
          smul (mulK a b) x = smul a (smul b x)) /\
       (!a b:K. !x:V.
          smul (addK a b) x =
          addV (smul a x) (smul b x)) /\
       (!a:K. !x y:V.
          smul a (addV x y) =
          addV (smul a x) (smul a y)) /\
       (!x:V. smul zeroK x = zeroV) /\
       (!a:K. smul a zeroV = zeroV)) in
     let is_affine_space = (
       (!p:P. vadd zeroV p = p) /\
       (!x y:V. !p:P.
          vadd (addV x y) p = vadd x (vadd y p)) /\
       (!x:V. !p:P. vsub (vadd x p) p = x) /\
       (!p q:P. vadd (vsub p q) q = p)) in
     let affine_independent = (
       !coeff:num->K.
         ksum (n + 1) coeff = zeroK /\
         vsum (n + 1)
           (\j:num.
              smul (coeff j) (vsub (points j) (points 0))) =
           zeroV
         ==> !j:num. j < n + 1 ==> coeff j = zeroK) in
     let centroid =
       vadd
         (smul (invK (nat_cast (n + 1)))
           (vsum (n + 1)
             (\j:num. vsub (points j) (points 0))))
         (points 0) in
     let face_opposite_centroid =
       vadd
         (smul (invK (nat_cast n))
           (vsum (n + 1)
             (\j:num.
                if j = i
                then zeroV
                else vsub (points j) (points 0))))
         (points 0) in
     is_nat_cast /\
     is_ksum /\
     is_vsum /\
     is_division_ring /\
     has_characteristic_zero /\
     is_add_comm_group /\
     is_module /\
     is_affine_space /\
     affine_independent /\
     ~(n = 0) /\
     i < n + 1
     ==>
     vsub (points i) centroid =
     smul (nat_cast n)
       (vsub centroid face_opposite_centroid)`;;
