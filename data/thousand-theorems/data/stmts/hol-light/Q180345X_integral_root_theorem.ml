(*
  Statement-only formalization of Thousand Theorems corpus artifact Q180345X,
  "Integral root theorem": a root in a fraction field of a monic polynomial
  over a unique factorization domain lies in the embedded domain. This file
  contains no proof.
*)

let Q180345X_INTEGRAL_ROOT_THEOREM =
  `!zeroA:A. !oneA:A. !addA:A->A->A. !mulA:A->A->A. !negA:A->A.
   !zeroK:K. !oneK:K. !addK:K->K->K. !mulK:K->K->K.
   !negK:K->K. !invK:K->K. !embed:A->K.
   !p:num->A. !r:K.
     let powerK =
       \x:K. \n:num. ITLIST mulK (REPLICATE n x) oneK in
     let is_integral_domain_A =
       (~(zeroA = oneA) /\
       (!x. addA zeroA x = x) /\
       (!x. addA (negA x) x = zeroA) /\
       (!x y. addA x y = addA y x) /\
       (!x y z. addA x (addA y z) = addA (addA x y) z) /\
       (!x. mulA oneA x = x) /\
       (!x y. mulA x y = mulA y x) /\
       (!x y z. mulA x (mulA y z) = mulA (mulA x y) z) /\
       (!x y z. mulA x (addA y z) =
                  addA (mulA x y) (mulA x z)) /\
       (!x y. mulA x y = zeroA ==> x = zeroA \/ y = zeroA)) in
     let unitA =
       \u:A. ?v:A. mulA u v = oneA in
     let associatesA =
       \x:A. \y:A. ?u:A. unitA u /\ y = mulA u x in
     let irreducibleA =
       \q:A.
         ~(q = zeroA) /\ ~unitA q /\
         (!x y. mulA x y = q ==> unitA x \/ unitA y) in
     let factorizationA =
       \x:A. \fs:A list.
         (!q. MEM q fs ==> irreducibleA q) /\
         (?u:A. unitA u /\ x = mulA u (ITLIST mulA fs oneA)) in
     let associated_listsA =
       \fs:A list. \gs:A list.
         LENGTH fs = LENGTH gs /\
         (?perm:num->num.
            BIJ perm {i | i < LENGTH fs} {i | i < LENGTH gs} /\
            (!i. i < LENGTH fs
                 ==> associatesA (EL i fs) (EL (perm i) gs))) in
     let is_ufd_A =
       (is_integral_domain_A /\
       (!x:A. ~(x = zeroA) ==> ?fs:A list. factorizationA x fs) /\
       (!x:A. !fs:A list. !gs:A list.
          factorizationA x fs /\ factorizationA x gs
          ==> associated_listsA fs gs)) in
     let is_field_K =
       (~(zeroK = oneK) /\
       (!x. addK zeroK x = x) /\
       (!x. addK (negK x) x = zeroK) /\
       (!x y. addK x y = addK y x) /\
       (!x y z. addK x (addK y z) = addK (addK x y) z) /\
       (!x. mulK oneK x = x) /\
       (!x y. mulK x y = mulK y x) /\
       (!x y z. mulK x (mulK y z) = mulK (mulK x y) z) /\
       (!x y z. mulK x (addK y z) =
                  addK (mulK x y) (mulK x z)) /\
       (!x. ~(x = zeroK) ==> mulK (invK x) x = oneK)) in
     let is_fraction_field =
       (embed zeroA = zeroK /\
       embed oneA = oneK /\
       (!x y. embed (addA x y) = addK (embed x) (embed y)) /\
       (!x y. embed (mulA x y) = mulK (embed x) (embed y)) /\
       (!x y. embed x = embed y ==> x = y) /\
       (!x:K. ?a:A. ?b:A.
          ~(b = zeroA) /\ mulK x (embed b) = embed a)) in
     let polynomial =
       (FINITE {n | ~(p n = zeroA)}) in
     let monic =
       (?d:num.
         p d = oneA /\
         (!n. d < n ==> p n = zeroA)) in
     let is_root =
       (iterate addK {n | ~(p n = zeroA)}
         (\n. mulK (embed (p n)) (powerK r n)) = zeroK) in
     is_ufd_A /\ is_field_K /\ is_fraction_field /\
     polynomial /\ monic /\ is_root
     ==> ?a:A. r = embed a`;;
