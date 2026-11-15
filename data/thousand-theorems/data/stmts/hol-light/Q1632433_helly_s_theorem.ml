(*
  Statement-only formalization of Thousand Theorems corpus artifact Q1632433,
  "Helly's theorem": a finite indexed family of convex sets in a
  finite-dimensional module over a linearly ordered field, with at least
  dimension plus one members, has nonempty total intersection when every
  subfamily of exactly that size does. This file contains no proof.
*)

let Q1632433_HELLY_THEOREM =
 `let linear_ordered_field =
    \(zeroK:A) (oneK:A) (addK:A->A->A) (mulK:A->A->A)
     (negK:A->A) (invK:A->A) (le:A->A->bool).
       ~(zeroK = oneK) /\
       (!a b c:A. addK a (addK b c) = addK (addK a b) c) /\
       (!a b:A. addK a b = addK b a) /\
       (!a:A. addK zeroK a = a) /\
       (!a:A. addK (negK a) a = zeroK) /\
       (!a b c:A. mulK a (mulK b c) = mulK (mulK a b) c) /\
       (!a b:A. mulK a b = mulK b a) /\
       (!a:A. mulK oneK a = a) /\
       invK zeroK = zeroK /\
       (!a:A. ~(a = zeroK) ==> mulK (invK a) a = oneK) /\
       (!a b c:A.
          mulK a (addK b c) = addK (mulK a b) (mulK a c)) /\
       (!a:A. le a a) /\
       (!a b:A. le a b /\ le b a ==> a = b) /\
       (!a b c:A. le a b /\ le b c ==> le a c) /\
       (!a b:A. le a b \/ le b a) /\
       (!a b c:A. le a b ==> le (addK a c) (addK b c)) /\
       (!a b:A.
          le zeroK a /\ le zeroK b ==> le zeroK (mulK a b)) in
  let module_over =
    \(zeroK:A) (oneK:A) (addK:A->A->A) (mulK:A->A->A)
     (zeroE:B) (addE:B->B->B) (negE:B->B) (smul:A->B->B).
       (!x y z:B. addE x (addE y z) = addE (addE x y) z) /\
       (!x y:B. addE x y = addE y x) /\
       (!x:B. addE zeroE x = x) /\
       (!x:B. addE (negE x) x = zeroE) /\
       (!x:B. smul oneK x = x) /\
       (!a b:A. !x:B.
          smul (mulK a b) x = smul a (smul b x)) /\
       (!a b:A. !x:B.
          smul (addK a b) x = addE (smul a x) (smul b x)) /\
       (!a:A. !x y:B.
          smul a (addE x y) = addE (smul a x) (smul a y)) in
  let linear_combination =
    \(zeroE:B) (addE:B->B->B) (smul:A->B->B)
     (n:num) (basis:num->B) (coeff:num->A) (x:B).
       ?partial:num->B.
         partial 0 = zeroE /\
         (!i:num.
            i < n
            ==> partial (SUC i) =
                addE (partial i) (smul (coeff i) (basis i))) /\
         partial n = x in
  let has_dimension =
    \(zeroE:B) (addE:B->B->B) (smul:A->B->B)
     (n:num) (basis:num->B).
       (!x:B.
          ?coeff:num->A.
            linear_combination zeroE addE smul n basis coeff x) /\
       (!c d:num->A. !x:B.
          linear_combination zeroE addE smul n basis c x /\
          linear_combination zeroE addE smul n basis d x
          ==> !i:num. i < n ==> c i = d i) in
  let convex_set =
    \(zeroK:A) (oneK:A) (addK:A->A->A) (le:A->A->bool)
     (addE:B->B->B) (smul:A->B->B) (u:B->bool).
       !x y:B. !a b:A.
         x IN u /\ y IN u /\
         le zeroK a /\ le zeroK b /\ addK a b = oneK
         ==> addE (smul a x) (smul b y) IN u in
  !zeroK oneK:A.
  !addK mulK:A->A->A.
  !negK invK:A->A.
  !le:A->A->bool.
  !zeroE:B.
  !addE:B->B->B.
  !negE:B->B.
  !smul:A->B->B.
  !fam:I->B->bool.
  !s:I->bool.
    linear_ordered_field zeroK oneK addK mulK negK invK le /\
    module_over zeroK oneK addK mulK zeroE addE negE smul /\
    (?n:num. ?basis:num->B.
       has_dimension zeroE addE smul n basis /\
       FINITE s /\
       n + 1 <= CARD s /\
       (!i:I.
          i IN s
          ==> convex_set zeroK oneK addK le addE smul (fam i)) /\
       (!t:I->bool.
          t SUBSET s /\
          FINITE t /\
          CARD t = n + 1
          ==> ?x:B. !i:I. i IN t ==> x IN fam i))
    ==> ?x:B. !i:I. i IN s ==> x IN fam i`;;
