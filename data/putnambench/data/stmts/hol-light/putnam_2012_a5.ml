(*
  Statement-only formalization of PutnamBench corpus artifact putnam_2012_a5:
  classification of affine maps on finite vector spaces over prime fields
  whose first p^n iterates of zero are all distinct. This file contains no
  proof.
*)

needs "Library/iter.ml";;

let statement =
  `let affine =
     \p n:num.
       \(M:num->num->num) (v:num->num) (x:num->num) i.
         if i < n then
           (v i + nsum (0..n - 1) (\j. M i j * x j)) MOD p
         else 0 in
   !n p:num.
     0 < n /\ prime p
     ==>
     (((n = 1) \/ (n = 2 /\ p = 2)) <=>
      ?M:num->num->num. ?v:num->num.
        (!i:num. i < n ==> v i < p) /\
        (!i j:num. i < n /\ j < n ==> M i j < p) /\
        !k l:num.
          1 <= k /\ k <= p EXP n /\
          1 <= l /\ l <= p EXP n /\
          ~(k = l)
          ==>
          ~(ITER k (affine p n M v) (\i:num. 0) =
            ITER l (affine p n M v) (\i:num. 0)))`;;
