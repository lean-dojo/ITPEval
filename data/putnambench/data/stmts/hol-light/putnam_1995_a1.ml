(*
  Statement-only formalization of PutnamBench corpus artifact putnam_1995_a1:
  a multiplicatively closed set of real numbers partitioned into two
  triple-product-closed subsets has a multiplicatively closed part. This file
  contains no proof.
*)

let statement =
  `!S T U:real->bool.
     (!a b:real.
        a IN S /\ b IN S
        ==> a * b IN S) /\
     T SUBSET S /\
     U SUBSET S /\
     T UNION U = S /\
     T INTER U = {} /\
     (!a b c:real.
        a IN T /\ b IN T /\ c IN T
        ==> a * b * c IN T) /\
     (!a b c:real.
        a IN U /\ b IN U /\ c IN U
        ==> a * b * c IN U)
     ==>
     (!a b:real.
        a IN T /\ b IN T
        ==> a * b IN T) \/
     (!a b:real.
        a IN U /\ b IN U
        ==> a * b IN U)`;;
