(*
  Statement-only formalization of Thousand Theorems corpus artifact Q282649
  (thousand-theorems__hol-light__Q282649), "Pentagonal number theorem": over
  an arbitrary commutative ring, the finite products of 1 - X^(n+1) converge
  coefficientwise in the induced product topology to the formal power series
  supported on generalized pentagonal numbers with alternating signs. This
  file contains no proof.
*)

let Q282649_PENTAGONAL_NUMBER_THEOREM =
  `let is_commutative_ring =
     \(zeroA:A) (oneA:A) (addA:A->A->A) (mulA:A->A->A) (negA:A->A).
       (!x:A. addA zeroA x = x /\ addA x zeroA = x) /\
       (!x y:A. addA x y = addA y x) /\
       (!x y z:A. addA (addA x y) z = addA x (addA y z)) /\
       (!x:A. addA (negA x) x = zeroA /\ addA x (negA x) = zeroA) /\
       (!x:A. mulA oneA x = x /\ mulA x oneA = x) /\
       (!x y:A. mulA x y = mulA y x) /\
       (!x y z:A. mulA (mulA x y) z = mulA x (mulA y z)) /\
       (!x y z:A.
          mulA x (addA y z) = addA (mulA x y) (mulA x z)) /\
       (!x y z:A.
          mulA (addA x y) z = addA (mulA x z) (mulA y z)) in
   let is_topology =
     \(open_sets:(A->bool)->bool).
       open_sets {} /\
       open_sets (UNIV:A->bool) /\
       (!family:(A->bool)->bool.
          (!U:A->bool. U IN family ==> open_sets U)
          ==> open_sets (UNIONS family)) /\
       (!U V:A->bool.
          open_sets U /\ open_sets V ==> open_sets (U INTER V)) in
   let cauchy_mul =
     \(addA:A->A->A) (mulA:A->A->A)
      (p:num->A) (q:num->A).
       \n:num.
         iterate addA {i:num | i <= n}
           (\i. mulA (p i) (q (n - i))) in
   let factor =
     \(zeroA:A) (oneA:A) (negA:A->A) (m:num).
       \d:num.
         if d = 0 then oneA
         else if d = m + 1 then negA oneA
         else zeroA in
   let finite_product =
     \(zeroA:A) (oneA:A) (addA:A->A->A) (mulA:A->A->A)
      (negA:A->A) (s:num->bool).
       iterate (cauchy_mul addA mulA) s (factor zeroA oneA negA) in
   let is_pentagonal_index =
     \(n:num) (k:int).
       (&2:int) * &n = k * ((&3:int) * k - &1) in
   let pentagonal_series =
     \(zeroA:A) (oneA:A) (negA:A->A).
       \n:num.
         if ?k:int. is_pentagonal_index n k then
           let k = @k:int. is_pentagonal_index n k in
           if EVEN (num_of_int (abs k)) then oneA else negA oneA
         else zeroA in
   let has_product_in_pi_topology =
     \(open_sets:(A->bool)->bool)
      (partial_product:(num->bool)->num->A)
      (target:num->A).
       !d:num. !U:A->bool.
         open_sets U /\ target d IN U
         ==> ?s0:num->bool.
               FINITE s0 /\
               !s:num->bool.
                 FINITE s /\ s0 SUBSET s
                 ==> partial_product s d IN U in
   !zeroA oneA:A.
   !addA mulA:A->A->A.
   !negA:A->A.
   !open_sets:(A->bool)->bool.
     is_commutative_ring zeroA oneA addA mulA negA /\
     is_topology open_sets
     ==>
     has_product_in_pi_topology
       open_sets
       (finite_product zeroA oneA addA mulA negA)
       (pentagonal_series zeroA oneA negA)`;;
