(*
  Statement-only formalization of Thousand Theorems corpus artifact Q776578,
  "Artin-Wedderburn theorem": every semisimple algebra is isomorphic, as an
  algebra over its commutative base semiring, to a finite product of matrix
  algebras over division algebras. This file contains no proof.
*)

let Q776578_ARTIN_WEDDERBURN_THEOREM =
  `let is_comm_semiring =
     \(zeroK:K) (oneK:K) (addK:K->K->K) (mulK:K->K->K).
       (!a:K. addK zeroK a = a /\ addK a zeroK = a) /\
       (!a b:K. addK a b = addK b a) /\
       (!a b c:K. addK (addK a b) c = addK a (addK b c)) /\
       (!a:K. mulK oneK a = a /\ mulK a oneK = a) /\
       (!a b:K. mulK a b = mulK b a) /\
       (!a b c:K. mulK (mulK a b) c = mulK a (mulK b c)) /\
       (!a b c:K.
          mulK a (addK b c) = addK (mulK a b) (mulK a c)) /\
       (!a b c:K.
          mulK (addK a b) c = addK (mulK a c) (mulK b c)) /\
       (!a:K. mulK zeroK a = zeroK /\ mulK a zeroK = zeroK) in
   let is_ring =
     \(zeroR:R) (oneR:R) (addR:R->R->R) (mulR:R->R->R)
      (negR:R->R).
       (!x:R. addR zeroR x = x /\ addR x zeroR = x) /\
       (!x y:R. addR x y = addR y x) /\
       (!x y z:R. addR (addR x y) z = addR x (addR y z)) /\
       (!x:R. addR (negR x) x = zeroR /\ addR x (negR x) = zeroR) /\
       (!x:R. mulR oneR x = x /\ mulR x oneR = x) /\
       (!x y z:R. mulR (mulR x y) z = mulR x (mulR y z)) /\
       (!x y z:R.
          mulR x (addR y z) = addR (mulR x y) (mulR x z)) /\
       (!x y z:R.
          mulR (addR x y) z = addR (mulR x z) (mulR y z)) /\
       (!x:R. mulR zeroR x = zeroR /\ mulR x zeroR = zeroR) in
   let is_algebra =
     \(zeroK:K) (oneK:K) (addK:K->K->K) (mulK:K->K->K)
      (zeroR:R) (oneR:R) (addR:R->R->R) (mulR:R->R->R)
      (scalar:K->R).
       scalar zeroK = zeroR /\
       scalar oneK = oneR /\
       (!a b:K. scalar (addK a b) = addR (scalar a) (scalar b)) /\
       (!a b:K. scalar (mulK a b) = mulR (scalar a) (scalar b)) /\
       (!a:K. !x:R. mulR (scalar a) x = mulR x (scalar a)) in
   let is_left_ideal =
     \(zeroR:R) (addR:R->R->R) (mulR:R->R->R) (negR:R->R)
      (ideal:R->bool).
       ideal zeroR /\
       (!x y:R. ideal x /\ ideal y ==> ideal (addR x y)) /\
       (!x:R. ideal x ==> ideal (negR x)) /\
       (!a x:R. ideal x ==> ideal (mulR a x)) in
   let is_semisimple_ring =
     \(zeroR:R) (addR:R->R->R) (mulR:R->R->R) (negR:R->R).
       !ideal:R->bool.
         is_left_ideal zeroR addR mulR negR ideal
         ==> ?complement:R->bool.
               is_left_ideal zeroR addR mulR negR complement /\
               (!x:R. ideal x /\ complement x ==> x = zeroR) /\
               (!x:R.
                  ?y z:R.
                    ideal y /\ complement z /\ x = addR y z) in
   let is_division_algebra =
     \(zeroK:K) (oneK:K) (addK:K->K->K) (mulK:K->K->K)
      (carrier:R->bool) (zeroD:R) (oneD:R)
      (addD:R->R->R) (mulD:R->R->R) (negD:R->R) (invD:R->R)
      (scalarD:K->R).
       carrier zeroD /\
       carrier oneD /\
       ~(oneD = zeroD) /\
       (!x y:R.
          carrier x /\ carrier y
          ==> carrier (addD x y) /\ carrier (mulD x y)) /\
       (!x:R. carrier x ==> carrier (negD x) /\ carrier (invD x)) /\
       (!x:R.
          carrier x
          ==> addD zeroD x = x /\ addD x zeroD = x) /\
       (!x y:R.
          carrier x /\ carrier y
          ==> addD x y = addD y x) /\
       (!x y z:R.
          carrier x /\ carrier y /\ carrier z
          ==> addD (addD x y) z = addD x (addD y z)) /\
       (!x:R.
          carrier x
          ==> addD (negD x) x = zeroD /\ addD x (negD x) = zeroD) /\
       (!x:R.
          carrier x
          ==> mulD oneD x = x /\ mulD x oneD = x) /\
       (!x y z:R.
          carrier x /\ carrier y /\ carrier z
          ==> mulD (mulD x y) z = mulD x (mulD y z)) /\
       (!x y z:R.
          carrier x /\ carrier y /\ carrier z
          ==> mulD x (addD y z) = addD (mulD x y) (mulD x z)) /\
       (!x y z:R.
          carrier x /\ carrier y /\ carrier z
          ==> mulD (addD x y) z = addD (mulD x z) (mulD y z)) /\
       (!x:R.
          carrier x
          ==> mulD zeroD x = zeroD /\ mulD x zeroD = zeroD) /\
       invD zeroD = zeroD /\
       (!x:R.
          carrier x /\ ~(x = zeroD)
          ==> mulD (invD x) x = oneD /\ mulD x (invD x) = oneD) /\
       (!a:K. carrier (scalarD a)) /\
       scalarD zeroK = zeroD /\
       scalarD oneK = oneD /\
       (!a b:K.
          scalarD (addK a b) = addD (scalarD a) (scalarD b)) /\
       (!a b:K.
          scalarD (mulK a b) = mulD (scalarD a) (scalarD b)) /\
       (!a:K. !x:R.
          carrier x
          ==> mulD (scalarD a) x = mulD x (scalarD a)) in
   let valid_entry =
     \(n:num) (d:num->num) (i:num) (r:num) (c:num).
       i < n /\ r < d i /\ c < d i in
   let matrix_product_carrier =
     \(zeroR:R) (n:num) (carrier:num->R->bool) (d:num->num)
      (x:num->num->num->R).
       !i r c:num.
         if valid_entry n d i r c
         then carrier i (x i r c)
         else x i r c = zeroR in
   let matrix_zero =
     \(zeroR:R) (n:num) (zeroD:num->R) (d:num->num).
       \i r c:num.
         if valid_entry n d i r c then zeroD i else zeroR in
  let matrix_one =
     \(zeroR:R) (n:num) (zeroD:num->R) (oneD:num->R) (d:num->num).
       \i r c:num.
         if valid_entry n d i r c
         then if r = c then oneD i else zeroD i
         else zeroR in
   let matrix_neg =
     \(zeroR:R) (negD:num->R->R) (n:num) (d:num->num)
      (x:num->num->num->R).
       \i r c:num.
         if valid_entry n d i r c then negD i (x i r c) else zeroR in
   let matrix_add =
     \(zeroR:R) (addD:num->R->R->R) (n:num) (d:num->num)
      (x:num->num->num->R) (y:num->num->num->R).
       \i r c:num.
         if valid_entry n d i r c
         then addD i (x i r c) (y i r c)
         else zeroR in
   let matrix_mul =
     \(zeroR:R) (zeroD:num->R)
      (addD:num->R->R->R) (mulD:num->R->R->R)
      (n:num) (d:num->num)
      (x:num->num->num->R) (y:num->num->num->R).
       \i r c:num.
         if valid_entry n d i r c
         then ITLIST (addD i)
                (list_of_seq
                  (\k:num. mulD i (x i r k) (y i k c))
                  (d i))
                (zeroD i)
         else zeroR in
  let matrix_scalar =
     \(zeroR:R) (zeroD:num->R) (scalarD:num->K->R)
      (n:num) (d:num->num) (a:K).
       \i r c:num.
         if valid_entry n d i r c
         then if r = c then scalarD i a else zeroD i
         else zeroR in
   let is_algebra_isomorphism =
     \(zeroR:R) (oneR:R) (addR:R->R->R) (mulR:R->R->R)
      (negR:R->R) (scalar:K->R)
      (n:num) (carrier:num->R->bool)
      (zeroD:num->R) (oneD:num->R)
      (addD:num->R->R->R) (mulD:num->R->R->R)
      (negD:num->R->R) (scalarD:num->K->R) (d:num->num)
      (phi:R->num->num->num->R).
       let target = matrix_product_carrier zeroR n carrier d in
       let target_zero = matrix_zero zeroR n zeroD d in
       let target_one = matrix_one zeroR n zeroD oneD d in
       let target_neg = matrix_neg zeroR negD n d in
       let target_add = matrix_add zeroR addD n d in
       let target_mul = matrix_mul zeroR zeroD addD mulD n d in
       let target_scalar = matrix_scalar zeroR zeroD scalarD n d in
       (!x:R. target (phi x)) /\
       (!x y:R. phi x = phi y ==> x = y) /\
       (!z:num->num->num->R. target z ==> ?x:R. phi x = z) /\
       phi zeroR = target_zero /\
       phi oneR = target_one /\
       (!x:R. phi (negR x) = target_neg (phi x)) /\
       (!x y:R. phi (addR x y) = target_add (phi x) (phi y)) /\
       (!x y:R. phi (mulR x y) = target_mul (phi x) (phi y)) /\
       (!a:K. phi (scalar a) = target_scalar a) in
   !zeroK oneK:K.
   !addK mulK:K->K->K.
   !zeroR oneR:R.
   !addR mulR:R->R->R.
   !negR:R->R.
   !scalar:K->R.
     is_comm_semiring zeroK oneK addK mulK /\
     is_ring zeroR oneR addR mulR negR /\
     is_algebra
       zeroK oneK addK mulK zeroR oneR addR mulR scalar /\
     is_semisimple_ring zeroR addR mulR negR
     ==> ?n:num.
         ?carrier:num->R->bool.
         ?zeroD:num->R.
         ?oneD:num->R.
         ?addD:num->R->R->R.
         ?mulD:num->R->R->R.
         ?negD:num->R->R.
         ?invD:num->R->R.
         ?scalarD:num->K->R.
         ?d:num->num.
         ?phi:R->num->num->num->R.
           (!i:num. i < n ==> 0 < d i) /\
           (!i:num.
              i < n
              ==> is_division_algebra
                    zeroK oneK addK mulK
                    (carrier i) (zeroD i) (oneD i)
                    (addD i) (mulD i) (negD i) (invD i)
                    (scalarD i)) /\
           is_algebra_isomorphism
             zeroR oneR addR mulR negR scalar
             n carrier zeroD oneD addD mulD negD scalarD d phi`;;
