(*
  Statement-only formalization of Thousand Theorems corpus artifact Q7660749
  (thousand-theorems__hol-light__Q7660749), "Sylvester's determinant theorem":
  over any commutative ring, rectangular matrices on arbitrary finite index
  carriers satisfy det(I + A B) = det(I + B A). This file contains no proof.
*)

let q7660749_is_comm_ring = new_definition
  `q7660749_is_comm_ring (zeroR:R) (oneR:R)
      (addR:R->R->R) (mulR:R->R->R) (negR:R->R) <=>
     (!x:R. addR zeroR x = x) /\
     (!x:R. addR (negR x) x = zeroR) /\
     (!x y:R. addR x y = addR y x) /\
     (!x y z:R. addR x (addR y z) = addR (addR x y) z) /\
     (!x:R. mulR oneR x = x) /\
     (!x y:R. mulR x y = mulR y x) /\
     (!x y z:R. mulR x (mulR y z) = mulR (mulR x y) z) /\
     (!x y z:R.
        mulR x (addR y z) = addR (mulR x y) (mulR x z))`;;

let q7660749_apply_swaps = new_definition
  `q7660749_apply_swaps (swaps:(I#I)list) (x:I) =
     ITLIST
       (\ab y:I.
          if y = FST ab then SND ab
          else if y = SND ab then FST ab
          else y)
       swaps x`;;

let q7660749_even_permutation = new_definition
  `q7660749_even_permutation (s:I->bool) (p:I->I) <=>
     ?swaps:(I#I)list.
       EVEN (LENGTH swaps) /\
       ALL
         (\ab:I#I.
            FST ab IN s /\ SND ab IN s /\ ~(FST ab = SND ab))
         swaps /\
       (!i:I. i IN s ==> q7660749_apply_swaps swaps i = p i)`;;

let q7660749_sign = new_definition
  `q7660749_sign (oneR:R) (negR:R->R) (s:I->bool) (p:I->I) =
     if q7660749_even_permutation s p then oneR else negR oneR`;;

let q7660749_permutations = new_definition
  `q7660749_permutations (s:I->bool) =
     {p:I->I | BIJ p s s /\ (!i:I. ~(i IN s) ==> p i = i)}`;;

let q7660749_determinant = new_definition
  `q7660749_determinant (zeroR:R) (oneR:R)
      (addR:R->R->R) (mulR:R->R->R) (negR:R->R)
      (s:I->bool) (A:I->I->R) =
     iterate addR (q7660749_permutations s)
       (\p:I->I.
          mulR (q7660749_sign oneR negR s p)
            (iterate mulR s (\i:I. A i (p i))))`;;

let q7660749_matrix_identity = new_definition
  `q7660749_matrix_identity (zeroR:R) (oneR:R) (s:I->bool) =
     \i j:I. if i IN s /\ j = i then oneR else zeroR`;;

let q7660749_matrix_add = new_definition
  `q7660749_matrix_add (addR:R->R->R)
      (A:I->J->R) (B:I->J->R) =
     \i j. addR (A i j) (B i j)`;;

let q7660749_matrix_mul = new_definition
  `q7660749_matrix_mul (addR:R->R->R) (mulR:R->R->R)
      (middle:J->bool) (A:I->J->R) (B:J->K->R) =
     \i k. iterate addR middle (\j:J. mulR (A i j) (B j k))`;;

let Q7660749_SYLVESTERS_DETERMINANT_THEOREM =
  `!zeroR oneR:R.
   !addR mulR:R->R->R.
   !negR:R->R.
   !s:M->bool.
   !t:N->bool.
   !A:M->N->R.
   !B:N->M->R.
     q7660749_is_comm_ring zeroR oneR addR mulR negR /\
     FINITE s /\ FINITE t
     ==>
     q7660749_determinant zeroR oneR addR mulR negR s
       (q7660749_matrix_add addR
         (q7660749_matrix_identity zeroR oneR s)
         (q7660749_matrix_mul addR mulR t A B)) =
     q7660749_determinant zeroR oneR addR mulR negR t
       (q7660749_matrix_add addR
         (q7660749_matrix_identity zeroR oneR t)
         (q7660749_matrix_mul addR mulR s B A))`;;
