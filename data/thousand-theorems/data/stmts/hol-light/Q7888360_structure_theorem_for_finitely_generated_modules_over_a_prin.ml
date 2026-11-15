(*
  Statement-only formalization of Thousand Theorems corpus artifact Q7888360,
  "Structure theorem for finitely generated modules over a principal ideal
  domain": every finitely generated module over a commutative principal ideal
  domain is linearly isomorphic to a finite free module times a finite direct
  sum of cyclic modules by powers of irreducibles. This file contains no proof.
*)

let Q7888360_STRUCTURE_THEOREM_FOR_FINITELY_GENERATED_MODULES_OVER_A_PID =
  `let is_commutative_ring =
     \(zeroR:R) (oneR:R) (addR:R->R->R) (mulR:R->R->R)
      (negR:R->R).
       (!a:R. addR zeroR a = a) /\
       (!a:R. addR (negR a) a = zeroR) /\
       (!a b:R. addR a b = addR b a) /\
       (!a b c:R. addR a (addR b c) = addR (addR a b) c) /\
       (!a:R. mulR oneR a = a) /\
       (!a b:R. mulR a b = mulR b a) /\
       (!a b c:R. mulR a (mulR b c) = mulR (mulR a b) c) /\
       (!a b c:R.
          mulR a (addR b c) = addR (mulR a b) (mulR a c)) in
   let is_integral_domain =
     \(zeroR:R) (oneR:R) (mulR:R->R->R).
       ~(zeroR = oneR) /\
       (!a b:R. mulR a b = zeroR ==> a = zeroR \/ b = zeroR) in
   let is_ideal =
     \(zeroR:R) (addR:R->R->R) (mulR:R->R->R) (negR:R->R)
      (ideal:R->bool).
       ideal zeroR /\
       (!a b:R. ideal a /\ ideal b ==> ideal (addR a b)) /\
       (!a:R. ideal a ==> ideal (negR a)) /\
       (!r a:R. ideal a ==> ideal (mulR r a)) in
   let is_principal_ideal_ring =
     \(zeroR:R) (addR:R->R->R) (mulR:R->R->R) (negR:R->R).
       !ideal:R->bool.
         is_ideal zeroR addR mulR negR ideal
         ==> ?generator:R.
               !x:R.
                 (ideal x <=>
                  ?coefficient:R. x = mulR coefficient generator) in
   let is_module =
     \(zeroR:R) (oneR:R) (addR:R->R->R) (mulR:R->R->R)
      (zeroM:M) (addM:M->M->M) (negM:M->M) (smul:R->M->M).
       (!x:M. addM zeroM x = x) /\
       (!x:M. addM (negM x) x = zeroM) /\
       (!x y:M. addM x y = addM y x) /\
       (!x y z:M. addM x (addM y z) = addM (addM x y) z) /\
       (!x:M. smul oneR x = x) /\
       (!a b:R. !x:M.
          smul (mulR a b) x = smul a (smul b x)) /\
       (!a b:R. !x:M.
          smul (addR a b) x = addM (smul a x) (smul b x)) /\
       (!a:R. !x y:M.
          smul a (addM x y) = addM (smul a x) (smul a y)) in
   let is_finitely_generated =
     \(zeroR:R) (addM:M->M->M) (smul:R->M->M).
       ?d:num. ?generators:num->M.
         !x:M.
           ?coefficients:num->R.
             (!i:num. d <= i ==> coefficients i = zeroR) /\
             x =
             iterate addM {i:num | i < d}
               (\i:num. smul (coefficients i) (generators i)) in
   let ring_power =
     \(oneR:R) (mulR:R->R->R) (a:R) (n:num).
       ITLIST mulR (REPLICATE n a) oneR in
   let is_unit =
     \(oneR:R) (mulR:R->R->R) (a:R).
       ?b:R. mulR a b = oneR in
   let is_irreducible =
     \(zeroR:R) (oneR:R) (mulR:R->R->R) (p:R).
       ~(p = zeroR) /\
       ~(is_unit oneR mulR p) /\
       (!a b:R.
          p = mulR a b
          ==> is_unit oneR mulR a \/ is_unit oneR mulR b) in
   let congruent_mod =
     \(addR:R->R->R) (mulR:R->R->R) (negR:R->R)
      (generator:R) (x:R) (y:R).
       ?coefficient:R.
         addR x (negR y) = mulR coefficient generator in
   let quotient_class =
     \(addR:R->R->R) (mulR:R->R->R) (negR:R->R)
      (generator:R) (representative:R).
       \x:R.
         congruent_mod addR mulR negR generator x representative in
   let is_quotient_element =
     \(addR:R->R->R) (mulR:R->R->R) (negR:R->R)
      (generator:R) (coset:R->bool).
       ?representative:R.
         coset =
         quotient_class addR mulR negR generator representative in
   let quotient_add =
     \(addR:R->R->R) (mulR:R->R->R) (negR:R->R)
      (generator:R) (left:R->bool) (right:R->bool).
       \x:R.
         ?a b:R.
           left a /\ right b /\
           congruent_mod addR mulR negR generator x (addR a b) in
   let quotient_smul =
     \(addR:R->R->R) (mulR:R->R->R) (negR:R->R)
      (generator:R) (scalar:R) (coset:R->bool).
       \x:R.
         ?a:R.
           coset a /\
           congruent_mod addR mulR negR generator x (mulR scalar a) in
   let finite_free_tuple =
     \(zeroR:R) (n:num) (coordinates:num->R).
       !i:num. n <= i ==> coordinates i = zeroR in
   let finite_quotient_tuple =
     \(oneR:R) (addR:R->R->R) (mulR:R->R->R) (negR:R->R)
      (k:num) (p:num->R) (e:num->num)
      (coordinates:num->(R->bool)).
       (!i:num.
          i < k
          ==> is_quotient_element addR mulR negR
                (ring_power oneR mulR (p i) (e i))
                (coordinates i)) /\
       (!i:num. k <= i ==> coordinates i = (\x:R. F)) in
   let decomposition_carrier =
     \(zeroR:R) (oneR:R) (addR:R->R->R) (mulR:R->R->R)
      (negR:R->R) (n:num) (k:num) (p:num->R) (e:num->num)
      (z:(num->R)#(num->(R->bool))).
       finite_free_tuple zeroR n (FST z) /\
       finite_quotient_tuple oneR addR mulR negR k p e (SND z) in
   let decomposition_add =
     \(addR:R->R->R) (mulR:R->R->R) (negR:R->R)
      (oneR:R) (k:num) (p:num->R) (e:num->num)
      (z:(num->R)#(num->(R->bool)))
      (w:(num->R)#(num->(R->bool))).
       ((\i:num. addR (FST z i) (FST w i)),
        (\i:num.
           if i < k then
             quotient_add addR mulR negR
               (ring_power oneR mulR (p i) (e i))
               (SND z i) (SND w i)
           else (\x:R. F))) in
   let decomposition_smul =
     \(addR:R->R->R) (mulR:R->R->R) (negR:R->R)
      (oneR:R) (k:num) (p:num->R) (e:num->num) (scalar:R)
      (z:(num->R)#(num->(R->bool))).
       ((\i:num. mulR scalar (FST z i)),
        (\i:num.
           if i < k then
             quotient_smul addR mulR negR
               (ring_power oneR mulR (p i) (e i))
               scalar (SND z i)
           else (\x:R. F))) in
   let is_linear_equivalence =
     \(zeroR:R) (oneR:R) (addR:R->R->R) (mulR:R->R->R)
      (negR:R->R) (addM:M->M->M) (smul:R->M->M)
      (n:num) (k:num) (p:num->R) (e:num->num)
      (equiv:M->((num->R)#(num->(R->bool)))).
       (!x:M.
          decomposition_carrier
            zeroR oneR addR mulR negR n k p e (equiv x)) /\
       (!x y:M.
          equiv (addM x y) =
          decomposition_add addR mulR negR oneR k p e
            (equiv x) (equiv y)) /\
       (!a:R. !x:M.
          equiv (smul a x) =
          decomposition_smul addR mulR negR oneR k p e a (equiv x)) /\
       (!z:(num->R)#(num->(R->bool)).
          decomposition_carrier zeroR oneR addR mulR negR n k p e z
          ==> ?!x:M. equiv x = z) in
   !zeroR oneR:R.
   !addR mulR:R->R->R.
   !negR:R->R.
   !zeroM:M.
   !addM:M->M->M.
   !negM:M->M.
   !smul:R->M->M.
     is_commutative_ring zeroR oneR addR mulR negR /\
     is_integral_domain zeroR oneR mulR /\
     is_principal_ideal_ring zeroR addR mulR negR /\
     is_module zeroR oneR addR mulR zeroM addM negM smul /\
     is_finitely_generated zeroR addM smul
     ==> ?n k:num. ?p:num->R. ?e:num->num.
           (!i:num.
              i < k ==> is_irreducible zeroR oneR mulR (p i)) /\
           ?equiv:M->((num->R)#(num->(R->bool))).
             is_linear_equivalence
               zeroR oneR addR mulR negR addM smul n k p e equiv`;;
