(*
  Statement-only formalization of Thousand Theorems corpus artifact Q2471737,
  "Carathéodory's theorem (convex hull)": over a linearly ordered field, the
  convex hull of a set in a module is the union of the convex hulls of its
  finite affinely independent subsets. This file contains no proof.
*)

let Q2471737_CARATHEODORY_CONVEX_HULL =
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
  let affine_independent =
    \(zeroK:A) (addK:A->A->A)
     (zeroE:B) (addE:B->B->B) (smul:A->B->B) (t:B->bool).
       !w:B->A.
         iterate addK t w = zeroK /\
         iterate addE t (\x:B. smul (w x) x) = zeroE
         ==> !x:B. x IN t ==> w x = zeroK in
  let convex_set =
    \(zeroK:A) (oneK:A) (addK:A->A->A) (le:A->A->bool)
     (addE:B->B->B) (smul:A->B->B) (s:B->bool).
       !x y:B. !a b:A.
         x IN s /\ y IN s /\
         le zeroK a /\ le zeroK b /\ addK a b = oneK
         ==> addE (smul a x) (smul b y) IN s in
  let convex_hull =
    \(zeroK:A) (oneK:A) (addK:A->A->A) (le:A->A->bool)
     (addE:B->B->B) (smul:A->B->B) (u:B->bool).
       {x:B |
          !s:B->bool.
            u SUBSET s /\
            convex_set zeroK oneK addK le addE smul s
            ==> x IN s} in
  !zeroK oneK:A.
  !addK mulK:A->A->A.
  !negK invK:A->A.
  !le:A->A->bool.
  !zeroE:B.
  !addE:B->B->B.
  !negE:B->B.
  !smul:A->B->B.
  !s:B->bool.
    linear_ordered_field zeroK oneK addK mulK negK invK le /\
    module_over zeroK oneK addK mulK zeroE addE negE smul
    ==>
    convex_hull zeroK oneK addK le addE smul s =
    {x:B |
       ?t:B->bool.
         FINITE t /\
         t SUBSET s /\
         affine_independent zeroK addK zeroE addE smul t /\
         x IN convex_hull zeroK oneK addK le addE smul t}`;;
