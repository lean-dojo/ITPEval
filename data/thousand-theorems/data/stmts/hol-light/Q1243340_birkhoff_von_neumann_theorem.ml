(*
  Statement-only formalization of Thousand Theorems corpus artifact Q1243340,
  "Birkhoff–Von Neumann theorem": over an arbitrary linearly ordered field,
  the doubly stochastic matrices on any finite index type, represented by a
  finite subset to include the empty case, are exactly the convex hull of the
  permutation matrices. This file contains no proof.
*)

let DOUBLY_STOCHASTIC_EQ_CONVEX_HULL_PERM_MATRIX =
 `let linear_ordered_field =
    \(zeroK:A) (oneK:A) (add:A->A->A) (mul:A->A->A)
     (neg:A->A) (invk:A->A) (le:A->A->bool).
       ~(zeroK = oneK) /\
       (!x y z:A. add x (add y z) = add (add x y) z) /\
       (!x y:A. add x y = add y x) /\
       (!x:A. add zeroK x = x) /\
       (!x:A. add (neg x) x = zeroK) /\
       (!x y z:A. mul x (mul y z) = mul (mul x y) z) /\
       (!x y:A. mul x y = mul y x) /\
       (!x:A. mul oneK x = x) /\
       invk zeroK = zeroK /\
       (!x:A. ~(x = zeroK) ==> mul (invk x) x = oneK) /\
       (!x y z:A.
          mul x (add y z) = add (mul x y) (mul x z)) /\
       (!x:A. le x x) /\
       (!x y:A. le x y /\ le y x ==> x = y) /\
       (!x y z:A. le x y /\ le y z ==> le x z) /\
       (!x y:A. le x y \/ le y x) /\
       (!x y z:A. le x y ==> le (add x z) (add y z)) /\
       (!x y:A. le zeroK x /\ le zeroK y ==> le zeroK (mul x y)) in
  let matrix_on =
    \(zeroK:A) (s:I->bool) (M:I->I->A).
       !i j:I. ~(i IN s /\ j IN s) ==> M i j = zeroK in
  let doubly_stochastic =
    \(zeroK:A) (oneK:A) (add:A->A->A) (le:A->A->bool)
     (s:I->bool).
       {M:I->I->A |
          matrix_on zeroK s M /\
          (!i j:I. i IN s /\ j IN s ==> le zeroK (M i j)) /\
          (!i:I.
             i IN s
             ==> iterate add s (\j:I. M i j) = oneK) /\
          (!j:I.
             j IN s
             ==> iterate add s (\i:I. M i j) = oneK)} in
  let permutation_matrix =
    \(zeroK:A) (oneK:A) (s:I->bool) (p:I->I) (M:I->I->A).
       matrix_on zeroK s M /\
       BIJ p s s /\
       (!i j:I.
          i IN s /\ j IN s
          ==> M i j = if p i = j then oneK else zeroK) in
  let permutation_matrices =
    \(zeroK:A) (oneK:A) (s:I->bool).
       {M:I->I->A |
          ?p:I->I. permutation_matrix zeroK oneK s p M} in
  let convex_set =
    \(zeroK:A) (oneK:A) (add:A->A->A) (mul:A->A->A)
     (le:A->A->bool) (c:(I->I->A)->bool).
       !M N:I->I->A. !a b:A.
         M IN c /\ N IN c /\
         le zeroK a /\ le zeroK b /\ add a b = oneK
         ==> (\i j:I.
                add (mul a (M i j)) (mul b (N i j))) IN c in
  let convex_hull =
    \(zeroK:A) (oneK:A) (add:A->A->A) (mul:A->A->A)
     (le:A->A->bool) (u:(I->I->A)->bool).
       {M:I->I->A |
          !c:(I->I->A)->bool.
            u SUBSET c /\
            convex_set zeroK oneK add mul le c
            ==> M IN c} in
  !zeroK oneK:A.
  !add mul:A->A->A.
  !neg invk:A->A.
  !le:A->A->bool.
  !s:I->bool.
    linear_ordered_field zeroK oneK add mul neg invk le /\
    FINITE s
    ==>
    doubly_stochastic zeroK oneK add le s =
    convex_hull zeroK oneK add mul le
      (permutation_matrices zeroK oneK s)`;;
