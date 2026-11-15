(*
  Statement-only formalization of Thousand Theorems corpus artifact Q180345,
  "Rational root theorem": for a polynomial over a unique factorization
  domain, the reduced numerator of a fraction-field root divides the constant
  coefficient and its reduced denominator divides the leading coefficient.
  This file contains no proof.
*)

let Q180345_NUM_DVD_OF_IS_ROOT =
  `!zeroA oneA:A. !addA mulA:A->A->A. !negA:A->A.
   !zeroK oneK:K. !addK mulK:K->K->K. !negK invK:K->K.
   !embed:A->K. !numK denK:K->A. !p:num->A. !r:K.
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
     let dvdA =
       \d:A. \x:A. ?c:A. x = mulA d c in
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
       invK zeroK = zeroK /\
       (!x. ~(x = zeroK) ==> mulK (invK x) x = oneK)) in
     let is_fraction_field =
       (embed zeroA = zeroK /\
       embed oneA = oneK /\
       (!x y. embed (addA x y) = addK (embed x) (embed y)) /\
       (!x y. embed (mulA x y) = mulK (embed x) (embed y)) /\
       (!x y. embed x = embed y ==> x = y) /\
       (!x:K. ?a b:A.
          ~(b = zeroA) /\ mulK x (embed b) = embed a)) in
     let is_reduced_num_den =
       (!x:K.
          ~(denK x = zeroA) /\
          mulK x (embed (denK x)) = embed (numK x) /\
          (!d:A.
             dvdA d (numK x) /\ dvdA d (denK x) ==> unitA d)) in
     let polynomial =
       FINITE {n | ~(p n = zeroA)} in
     let is_root =
       iterate addK {n | ~(p n = zeroA)}
         (\n. mulK (embed (p n)) (powerK r n)) = zeroK in
     is_ufd_A /\ is_field_K /\ is_fraction_field /\
     is_reduced_num_den /\ polynomial /\ is_root
     ==> dvdA (numK r) (p 0)`;;

let Q180345_DEN_DVD_OF_IS_ROOT =
  `!zeroA oneA:A. !addA mulA:A->A->A. !negA:A->A.
   !zeroK oneK:K. !addK mulK:K->K->K. !negK invK:K->K.
   !embed:A->K. !numK denK:K->A. !p:num->A. !r:K.
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
     let dvdA =
       \d:A. \x:A. ?c:A. x = mulA d c in
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
       invK zeroK = zeroK /\
       (!x. ~(x = zeroK) ==> mulK (invK x) x = oneK)) in
     let is_fraction_field =
       (embed zeroA = zeroK /\
       embed oneA = oneK /\
       (!x y. embed (addA x y) = addK (embed x) (embed y)) /\
       (!x y. embed (mulA x y) = mulK (embed x) (embed y)) /\
       (!x y. embed x = embed y ==> x = y) /\
       (!x:K. ?a b:A.
          ~(b = zeroA) /\ mulK x (embed b) = embed a)) in
     let is_reduced_num_den =
       (!x:K.
          ~(denK x = zeroA) /\
          mulK x (embed (denK x)) = embed (numK x) /\
          (!d:A.
             dvdA d (numK x) /\ dvdA d (denK x) ==> unitA d)) in
     let polynomial =
       FINITE {n | ~(p n = zeroA)} in
     let degree =
       if (!n:num. p n = zeroA) then 0
       else @d:num.
              ~(p d = zeroA) /\
              (!n:num. d < n ==> p n = zeroA) in
     let is_root =
       iterate addK {n | ~(p n = zeroA)}
         (\n. mulK (embed (p n)) (powerK r n)) = zeroK in
     is_ufd_A /\ is_field_K /\ is_fraction_field /\
     is_reduced_num_den /\ polynomial /\ is_root
     ==> dvdA (denK r) (p degree)`;;
