(*
  Statement-only formalization of Thousand Theorems corpus artifact Q303402,
  "Rank-nullity theorem": for a linear map between modules over a ring with
  the rank-nullity property, the cardinal ranks of its range and kernel add
  to the cardinal rank of its domain. This file contains no proof.
*)

let Q303402_RANK_NULLITY_THEOREM =
  `let is_ring =
     \(zeroR:R) (oneR:R) (addR:R->R->R) (mulR:R->R->R) (negR:R->R).
       (!a:R. addR zeroR a = a /\ addR a zeroR = a) /\
       (!a:R. addR (negR a) a = zeroR /\ addR a (negR a) = zeroR) /\
       (!a b:R. addR a b = addR b a) /\
       (!a b c:R. addR a (addR b c) = addR (addR a b) c) /\
       (!a:R. mulR oneR a = a /\ mulR a oneR = a) /\
       (!a:R. mulR zeroR a = zeroR /\ mulR a zeroR = zeroR) /\
       (!a b c:R. mulR a (mulR b c) = mulR (mulR a b) c) /\
       (!a b c:R.
          mulR a (addR b c) = addR (mulR a b) (mulR a c)) /\
       (!a b c:R.
          mulR (addR a b) c = addR (mulR a c) (mulR b c)) in
   let is_moduleV =
     \(zeroR:R) (oneR:R) (addR:R->R->R) (mulR:R->R->R)
      (zeroV:V) (addV:V->V->V) (negV:V->V) (smulV:R->V->V).
       (!x:V. addV zeroV x = x /\ addV x zeroV = x) /\
       (!x:V. addV (negV x) x = zeroV /\ addV x (negV x) = zeroV) /\
       (!x y:V. addV x y = addV y x) /\
       (!x y z:V. addV x (addV y z) = addV (addV x y) z) /\
       (!x:V. smulV zeroR x = zeroV) /\
       (!a:R. smulV a zeroV = zeroV) /\
       (!x:V. smulV oneR x = x) /\
       (!a b:R. !x:V. smulV (mulR a b) x = smulV a (smulV b x)) /\
       (!a b:R. !x:V.
          smulV (addR a b) x = addV (smulV a x) (smulV b x)) /\
       (!a:R. !x y:V.
          smulV a (addV x y) = addV (smulV a x) (smulV a y)) in
   let is_moduleW =
     \(zeroR:R) (oneR:R) (addR:R->R->R) (mulR:R->R->R)
      (zeroW:W) (addW:W->W->W) (negW:W->W) (smulW:R->W->W).
       (!x:W. addW zeroW x = x /\ addW x zeroW = x) /\
       (!x:W. addW (negW x) x = zeroW /\ addW x (negW x) = zeroW) /\
       (!x y:W. addW x y = addW y x) /\
       (!x y z:W. addW x (addW y z) = addW (addW x y) z) /\
       (!x:W. smulW zeroR x = zeroW) /\
       (!a:R. smulW a zeroW = zeroW) /\
       (!x:W. smulW oneR x = x) /\
       (!a b:R. !x:W. smulW (mulR a b) x = smulW a (smulW b x)) /\
       (!a b:R. !x:W.
          smulW (addR a b) x = addW (smulW a x) (smulW b x)) /\
       (!a:R. !x y:W.
          smulW a (addW x y) = addW (smulW a x) (smulW a y)) in
   let is_linear_map =
     \(addV:V->V->V) (smulV:R->V->V)
      (addW:W->W->W) (smulW:R->W->W) (f:V->W).
       (!x y:V. f (addV x y) = addW (f x) (f y)) /\
       (!a:R. !x:V. f (smulV a x) = smulW a (f x)) in
   let is_submoduleV =
     \(zeroV:V) (addV:V->V->V) (negV:V->V)
      (smulV:R->V->V) (P:V->bool).
       zeroV IN P /\
       (!x y:V. x IN P /\ y IN P ==> addV x y IN P) /\
       (!x:V. x IN P ==> negV x IN P) /\
       (!a:R. !x:V. x IN P ==> smulV a x IN P) in
   let is_submoduleW =
     \(zeroW:W) (addW:W->W->W) (negW:W->W)
      (smulW:R->W->W) (P:W->bool).
       zeroW IN P /\
       (!x y:W. x IN P /\ y IN P ==> addW x y IN P) /\
       (!x:W. x IN P ==> negW x IN P) /\
       (!a:R. !x:W. x IN P ==> smulW a x IN P) in
   let linear_independentV =
     \(zeroR:R) (zeroV:V) (addV:V->V->V) (smulV:R->V->V)
      (S:V->bool).
       !c:V->R.
         FINITE {x:V | ~(c x = zeroR)} /\
         {x:V | ~(c x = zeroR)} SUBSET S /\
         iterate addV {x:V | ~(c x = zeroR)} (\x:V. smulV (c x) x) =
           zeroV
         ==> !x:V. x IN S ==> c x = zeroR in
   let linear_independentW =
     \(zeroR:R) (zeroW:W) (addW:W->W->W) (smulW:R->W->W)
      (S:W->bool).
       !c:W->R.
         FINITE {x:W | ~(c x = zeroR)} /\
         {x:W | ~(c x = zeroR)} SUBSET S /\
         iterate addW {x:W | ~(c x = zeroR)} (\x:W. smulW (c x) x) =
           zeroW
         ==> !x:W. x IN S ==> c x = zeroR in
   let rank_witnessV =
     \(zeroR:R) (zeroV:V) (addV:V->V->V) (smulV:R->V->V)
      (P:V->bool) (B:V->bool).
       B SUBSET P /\
       linear_independentV zeroR zeroV addV smulV B /\
       (!C:V->bool.
          C SUBSET P /\
          linear_independentV zeroR zeroV addV smulV C
          ==> C <=_c B) in
   let rank_witnessW =
     \(zeroR:R) (zeroW:W) (addW:W->W->W) (smulW:R->W->W)
      (P:W->bool) (B:W->bool).
       B SUBSET P /\
       linear_independentW zeroR zeroW addW smulW B /\
       (!C:W->bool.
          C SUBSET P /\
          linear_independentW zeroR zeroW addW smulW C
          ==> C <=_c B) in
   let quotient_linear_independentV =
     \(zeroR:R) (addV:V->V->V) (smulV:R->V->V)
      (N:V->bool) (P:V->bool) (S:V->bool).
       S SUBSET P /\
       (!c:V->R.
          FINITE {x:V | ~(c x = zeroR)} /\
          {x:V | ~(c x = zeroR)} SUBSET S /\
          iterate addV {x:V | ~(c x = zeroR)} (\x:V. smulV (c x) x)
            IN N
          ==> !x:V. x IN S ==> c x = zeroR) in
   let quotient_linear_independentW =
     \(zeroR:R) (addW:W->W->W) (smulW:R->W->W)
      (N:W->bool) (P:W->bool) (S:W->bool).
       S SUBSET P /\
       (!c:W->R.
          FINITE {x:W | ~(c x = zeroR)} /\
          {x:W | ~(c x = zeroR)} SUBSET S /\
          iterate addW {x:W | ~(c x = zeroR)} (\x:W. smulW (c x) x)
            IN N
          ==> !x:W. x IN S ==> c x = zeroR) in
   let quotient_rank_witnessV =
     \(zeroR:R) (addV:V->V->V) (smulV:R->V->V)
      (N:V->bool) (P:V->bool) (B:V->bool).
       quotient_linear_independentV zeroR addV smulV N P B /\
       (!C:V->bool.
          quotient_linear_independentV zeroR addV smulV N P C
          ==> C <=_c B) in
   let quotient_rank_witnessW =
     \(zeroR:R) (addW:W->W->W) (smulW:R->W->W)
      (N:W->bool) (P:W->bool) (B:W->bool).
       quotient_linear_independentW zeroR addW smulW N P B /\
       (!C:W->bool.
          quotient_linear_independentW zeroR addW smulW N P C
          ==> C <=_c B) in
   let cardinal_sumVW =
     \(A:W->bool) (B:V->bool).
       {z:W+V |
          (?y:W. y IN A /\ z = INL y) \/
          (?x:V. x IN B /\ z = INR x)} in
   let cardinal_sumVV =
     \(A:V->bool) (B:V->bool).
       {z:V+V |
          (?x:V. x IN A /\ z = INL x) \/
          (?x:V. x IN B /\ z = INR x)} in
   let cardinal_sumWW =
     \(A:W->bool) (B:W->bool).
       {z:W+W |
          (?x:W. x IN A /\ z = INL x) \/
          (?x:W. x IN B /\ z = INR x)} in
   let has_rank_nullity =
     \(zeroR:R) (oneR:R)
      (zeroV:V) (addV:V->V->V) (negV:V->V) (smulV:R->V->V)
      (zeroW:W) (addW:W->W->W) (negW:W->W) (smulW:R->W->W).
       ~(zeroR = oneR) /\
       (!P:V->bool.
          is_submoduleV zeroV addV negV smulV P
          ==> ?B:V->bool.
                rank_witnessV zeroR zeroV addV smulV P B) /\
       (!P N:V->bool.
          is_submoduleV zeroV addV negV smulV P /\
          is_submoduleV zeroV addV negV smulV N /\
          N SUBSET P
          ==> ?BQ BN BP:V->bool.
                quotient_rank_witnessV zeroR addV smulV N P BQ /\
                rank_witnessV zeroR zeroV addV smulV N BN /\
                rank_witnessV zeroR zeroV addV smulV P BP /\
                cardinal_sumVV BQ BN =_c BP) /\
       (!P:W->bool.
          is_submoduleW zeroW addW negW smulW P
          ==> ?B:W->bool.
                rank_witnessW zeroR zeroW addW smulW P B) /\
       (!P N:W->bool.
          is_submoduleW zeroW addW negW smulW P /\
          is_submoduleW zeroW addW negW smulW N /\
          N SUBSET P
          ==> ?BQ BN BP:W->bool.
                quotient_rank_witnessW zeroR addW smulW N P BQ /\
                rank_witnessW zeroR zeroW addW smulW N BN /\
                rank_witnessW zeroR zeroW addW smulW P BP /\
                cardinal_sumWW BQ BN =_c BP) in
   !zeroR oneR:R.
   !addR mulR:R->R->R.
   !negR:R->R.
   !zeroV:V.
   !addV:V->V->V.
   !negV:V->V.
   !smulV:R->V->V.
   !zeroW:W.
   !addW:W->W->W.
   !negW:W->W.
   !smulW:R->W->W.
   !f:V->W.
     is_ring zeroR oneR addR mulR negR /\
     is_moduleV zeroR oneR addR mulR zeroV addV negV smulV /\
     is_moduleW zeroR oneR addR mulR zeroW addW negW smulW /\
     is_linear_map addV smulV addW smulW f /\
     has_rank_nullity
       zeroR oneR zeroV addV negV smulV zeroW addW negW smulW
     ==> ?BR:W->bool. ?BK BM:V->bool.
           rank_witnessW zeroR zeroW addW smulW
             {y:W | ?x:V. f x = y} BR /\
           rank_witnessV zeroR zeroV addV smulV
             {x:V | f x = zeroW} BK /\
           rank_witnessV zeroR zeroV addV smulV (UNIV:V->bool) BM /\
           cardinal_sumVW BR BK =_c BM`;;
