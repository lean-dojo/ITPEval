(*
  Statement-only formalization of PutnamBench corpus artifact putnam_2010_a5:
  a group embedded in three-dimensional real space whose products agree with
  cross products unless those cross products vanish. This file contains no
  proof.
*)

needs "Multivariate/vectors.ml";;

let statement =
  `let cross3 =
     \(x:real^3) (y:real^3).
       (lambda k.
          if k = 1 then x$2 * y$3 - x$3 * y$2
          else if k = 2 then x$3 * y$1 - x$1 * y$3
          else x$1 * y$2 - x$2 * y$1):real^3 in
   !mul:A->A->A. !identity:A. !ginv:A->A. !embed:A->real^3.
     (!a b c:A. mul a (mul b c) = mul (mul a b) c) /\
     (!a:A. mul identity a = a /\ mul a identity = a) /\
     (!a:A.
        mul (ginv a) a = identity /\ mul a (ginv a) = identity) /\
     (!a b:A. embed a = embed b ==> a = b) /\
     (!a b:A.
        cross3 (embed a) (embed b) = embed (mul a b) \/
        cross3 (embed a) (embed b) = vec 0)
     ==> !a b:A. cross3 (embed a) (embed b) = vec 0`;;
