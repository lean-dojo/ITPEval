(*
  Statement-only formalization of Thousand Theorems corpus artifact Q172298,
  "Lasker–Noether theorem": a finite primary decomposition of a submodule over
  a commutative semiring can be replaced by one whose component annihilator
  ideals have pairwise distinct radicals. This file contains no proof.
*)

let Q172298_LASKER_NOETHER_THEOREM =
  `let is_comm_semiring =
     \(zeroR:R) (oneR:R) (addR:R->R->R) (mulR:R->R->R).
       (!a. addR zeroR a = a) /\
       (!a b. addR a b = addR b a) /\
       (!a b c. addR (addR a b) c = addR a (addR b c)) /\
       (!a. mulR oneR a = a) /\
       (!a. mulR zeroR a = zeroR) /\
       (!a b. mulR a b = mulR b a) /\
       (!a b c. mulR (mulR a b) c = mulR a (mulR b c)) /\
       (!a b c. mulR a (addR b c) =
                  addR (mulR a b) (mulR a c)) in
   let is_module =
     \(zeroR:R) (oneR:R) (addR:R->R->R) (mulR:R->R->R)
      (zeroM:M) (addM:M->M->M) (smul:R->M->M).
       (!x. addM zeroM x = x) /\
       (!x y. addM x y = addM y x) /\
       (!x y z. addM (addM x y) z = addM x (addM y z)) /\
       (!a. smul a zeroM = zeroM) /\
       (!a x y. smul a (addM x y) =
                  addM (smul a x) (smul a y)) /\
       (!x. smul zeroR x = zeroM) /\
       (!x. smul oneR x = x) /\
       (!a b x. smul (addR a b) x =
                   addM (smul a x) (smul b x)) /\
       (!a b x. smul (mulR a b) x = smul a (smul b x)) in
   let is_submodule =
     \(zeroM:M) (addM:M->M->M) (smul:R->M->M) (J:M->bool).
       J zeroM /\
       (!x y. J x /\ J y ==> J (addM x y)) /\
       (!a x. J x ==> J (smul a x)) in
   let submodule_inf =
     \(family:(M->bool)->bool). \x:M. !J. family J ==> J x in
   let powerR =
     \(oneR:R) (mulR:R->R->R) (a:R) (n:num).
       ITLIST mulR (REPLICATE n a) oneR in
   let radical_colon =
     \(oneR:R) (mulR:R->R->R) (smul:R->M->M)
      (J:M->bool) (a:R).
       ?n:num. !x:M. J (smul (powerR oneR mulR a n) x) in
   let is_primary =
     \(oneR:R) (mulR:R->R->R) (smul:R->M->M) (J:M->bool).
       ~(J = (\x:M. T)) /\
       (!a:R. !x:M.
          J (smul a x)
          ==> J x \/ radical_colon oneR mulR smul J a) in
   !zeroR:R. !oneR:R. !addR:R->R->R. !mulR:R->R->R.
   !zeroM:M. !addM:M->M->M. !smul:R->M->M.
   !N:M->bool. !s:(M->bool)->bool.
     is_comm_semiring zeroR oneR addR mulR /\
     is_module zeroR oneR addR mulR zeroM addM smul /\
     is_submodule zeroM addM smul N /\
     FINITE s /\
     (!J:M->bool. s J ==> is_submodule zeroM addM smul J) /\
     submodule_inf s = N /\
     (!J:M->bool.
        s J ==> is_primary oneR mulR smul J)
     ==> ?t:(M->bool)->bool.
           FINITE t /\
           (!J:M->bool. t J ==> is_submodule zeroM addM smul J) /\
           submodule_inf t = N /\
           (!J:M->bool.
              t J ==> is_primary oneR mulR smul J) /\
           (!I J:M->bool.
              t I /\ t J /\ ~(I = J)
              ==> ~(radical_colon oneR mulR smul I =
                    radical_colon oneR mulR smul J))`;;
