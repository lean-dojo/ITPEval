(*
  Statement-only formalization of Thousand Theorems corpus artifact Q193878,
  "Chinese remainder theorem": for a finite family of pairwise coprime ideals
  in a commutative ring, the canonical map from the quotient by their
  intersection to the product of the individual quotients is a ring
  isomorphism. This file contains no proof.
*)

let Q193878_CHINESE_REMAINDER_THEOREM =
  `let is_comm_ring =
     \(zero:R) (oneR:R) (add:R->R->R) (mul:R->R->R) (neg:R->R).
       (!x. add zero x = x) /\
       (!x y. add x y = add y x) /\
       (!x y z. add (add x y) z = add x (add y z)) /\
       (!x. add (neg x) x = zero) /\
       (!x. mul oneR x = x) /\
       (!x y. mul x y = mul y x) /\
       (!x y z. mul (mul x y) z = mul x (mul y z)) /\
       (!x y z. mul x (add y z) = add (mul x y) (mul x z)) in
   let is_ideal =
     \(zero:R) (add:R->R->R) (mul:R->R->R) (neg:R->R)
      (ideal:R->bool).
       ideal zero /\
       (!x y. ideal x /\ ideal y ==> ideal (add x y)) /\
       (!x. ideal x ==> ideal (neg x)) /\
       (!a x. ideal x ==> ideal (mul a x)) in
   let sub =
     \(add:R->R->R) (neg:R->R) (x:R) (y:R). add x (neg y) in
   let ideal_coset =
     \(sub:R->R->R) (ideal:R->bool) (x:R).
       \y:R. ideal (sub y x) in
   let ideal_inf =
     \(indices:K->bool) (ideals:K->R->bool).
       \x:R. !i:K. indices i ==> ideals i x in
   let quotient_carrier =
     \(coset_fn:(R->bool)->R->R->bool) (ideal:R->bool) (c:R->bool).
       ?x:R. c = coset_fn ideal x in
   let choose_representative =
     \(coset_fn:(R->bool)->R->R->bool) (ideal:R->bool) (c:R->bool).
       @x:R. c = coset_fn ideal x in
   let quotient_zero =
     \(coset_fn:(R->bool)->R->R->bool) (ideal:R->bool) (zero:R).
       coset_fn ideal zero in
   let quotient_one =
     \(coset_fn:(R->bool)->R->R->bool) (ideal:R->bool) (oneR:R).
       coset_fn ideal oneR in
   let quotient_neg =
     \(coset_fn:(R->bool)->R->R->bool)
      (repr_fn:(R->bool)->(R->bool)->R)
      (neg:R->R) (ideal:R->bool) (c:R->bool).
       coset_fn ideal (neg (repr_fn ideal c)) in
   let quotient_add =
     \(coset_fn:(R->bool)->R->R->bool)
      (repr_fn:(R->bool)->(R->bool)->R)
      (add:R->R->R) (ideal:R->bool) (c:R->bool) (d:R->bool).
       coset_fn ideal
         (add (repr_fn ideal c) (repr_fn ideal d)) in
   let quotient_mul =
     \(coset_fn:(R->bool)->R->R->bool)
      (repr_fn:(R->bool)->(R->bool)->R)
      (mul:R->R->R) (ideal:R->bool) (c:R->bool) (d:R->bool).
       coset_fn ideal
         (mul (repr_fn ideal c) (repr_fn ideal d)) in
   let product_carrier =
     \(quotient_carrier:(R->bool)->(R->bool)->bool)
      (indices:K->bool) (ideals:K->R->bool) (q:K->R->bool).
       !i:K.
         (indices i ==> quotient_carrier (ideals i) (q i)) /\
         (~indices i ==> q i = (\x:R. T)) in
   let product_zero =
     \(quotient_zero:(R->bool)->R->bool)
      (indices:K->bool) (ideals:K->R->bool).
       \i:K. if indices i then quotient_zero (ideals i) else (\x:R. T) in
   let product_one =
     \(quotient_one:(R->bool)->R->bool)
      (indices:K->bool) (ideals:K->R->bool).
       \i:K. if indices i then quotient_one (ideals i) else (\x:R. T) in
   let product_neg =
     \(quotient_neg:(R->bool)->(R->bool)->R->bool)
      (indices:K->bool) (ideals:K->R->bool) (q:K->R->bool).
       \i:K. if indices i then quotient_neg (ideals i) (q i)
             else (\x:R. T) in
   let product_add =
     \(quotient_add:(R->bool)->(R->bool)->(R->bool)->R->bool)
      (indices:K->bool) (ideals:K->R->bool)
      (q:K->R->bool) (r:K->R->bool).
       \i:K. if indices i then quotient_add (ideals i) (q i) (r i)
             else (\x:R. T) in
   let product_mul =
     \(quotient_mul:(R->bool)->(R->bool)->(R->bool)->R->bool)
      (indices:K->bool) (ideals:K->R->bool)
      (q:K->R->bool) (r:K->R->bool).
       \i:K. if indices i then quotient_mul (ideals i) (q i) (r i)
             else (\x:R. T) in
   let canonical_map =
     \(coset_fn:(R->bool)->R->R->bool)
      (repr_fn:(R->bool)->(R->bool)->R)
      (indices:K->bool) (ideals:K->R->bool) (inf_ideal:R->bool)
      (c:R->bool).
       \i:K.
         if indices i
         then coset_fn (ideals i) (repr_fn inf_ideal c)
         else (\x:R. T) in
   let is_ring_isomorphism =
     \(source:(R->bool)->bool) (target:(K->R->bool)->bool)
      (source_zero:R->bool) (source_one:R->bool)
      (source_add:(R->bool)->(R->bool)->R->bool)
      (source_mul:(R->bool)->(R->bool)->R->bool)
      (source_neg:(R->bool)->R->bool)
      (target_zero:K->R->bool) (target_one:K->R->bool)
      (target_add:(K->R->bool)->(K->R->bool)->K->R->bool)
      (target_mul:(K->R->bool)->(K->R->bool)->K->R->bool)
      (target_neg:(K->R->bool)->K->R->bool)
      (phi:(R->bool)->K->R->bool).
       (!c. source c ==> target (phi c)) /\
       (!c d. source c /\ source d /\ phi c = phi d ==> c = d) /\
       (!q. target q ==> ?c. source c /\ phi c = q) /\
       phi source_zero = target_zero /\
       phi source_one = target_one /\
       (!c. source c ==> phi (source_neg c) = target_neg (phi c)) /\
       (!c d.
          source c /\ source d
          ==> phi (source_add c d) = target_add (phi c) (phi d)) /\
       (!c d.
          source c /\ source d
          ==> phi (source_mul c d) = target_mul (phi c) (phi d)) in
   !zero:R. !oneR:R. !add:R->R->R. !mul:R->R->R. !neg:R->R.
   !indices:K->bool. !ideals:K->R->bool.
     is_comm_ring zero oneR add mul neg /\
     FINITE indices /\
     (!i. indices i ==> is_ideal zero add mul neg (ideals i)) /\
     (!i j.
        indices i /\ indices j /\ ~(i = j)
        ==> ?a b. ideals i a /\ ideals j b /\ add a b = oneR)
     ==> let sub0 = sub add neg in
         let coset0 = ideal_coset sub0 in
         let inf_ideal = ideal_inf indices ideals in
         let qcarrier = quotient_carrier coset0 in
         let repr = choose_representative coset0 in
         let qzero = \ideal. quotient_zero coset0 ideal zero in
         let qone = \ideal. quotient_one coset0 ideal oneR in
         let qneg = quotient_neg coset0 repr neg in
         let qadd = quotient_add coset0 repr add in
         let qmul = quotient_mul coset0 repr mul in
         let pcarrier = product_carrier qcarrier indices ideals in
         let pzero = product_zero qzero indices ideals in
         let pone = product_one qone indices ideals in
         let pneg = product_neg qneg indices ideals in
         let padd = product_add qadd indices ideals in
         let pmul = product_mul qmul indices ideals in
         let crt = canonical_map coset0 repr indices ideals inf_ideal in
         is_ring_isomorphism
           (qcarrier inf_ideal) pcarrier
           (qzero inf_ideal) (qone inf_ideal)
           (qadd inf_ideal) (qmul inf_ideal) (qneg inf_ideal)
           pzero pone padd pmul pneg crt`;;
