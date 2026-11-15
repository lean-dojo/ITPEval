(*
  Statement-only formalization of PutnamBench artifact putnam_1969_b2:
  a finite group is not the union of two proper subgroups, while the
  corresponding assertion for three proper subgroups is false. This file
  contains no proof.
*)

let statement =
  `let is_group =
     \(carrier:num->bool) (mul:num->num->num)
      (identity:num) (ginv:num->num).
       FINITE carrier /\
       identity IN carrier /\
       (!x y:num.
          x IN carrier /\ y IN carrier ==> mul x y IN carrier) /\
       (!x y z:num.
          x IN carrier /\ y IN carrier /\ z IN carrier
          ==> mul (mul x y) z = mul x (mul y z)) /\
       (!x:num.
          x IN carrier
          ==> mul identity x = x /\ mul x identity = x) /\
       (!x:num.
          x IN carrier
          ==> ginv x IN carrier /\
              mul (ginv x) x = identity /\
              mul x (ginv x) = identity) in
   let is_subgroup =
     \(carrier:num->bool) (mul:num->num->num)
      (identity:num) (ginv:num->num) (h:num->bool).
       h SUBSET carrier /\
       identity IN h /\
       (!x:num. x IN h ==> ginv x IN h) /\
       (!x y:num. x IN h /\ y IN h ==> mul x y IN h) in
   let P =
     \n:num.
       !carrier:num->bool. !mul:num->num->num.
       !identity:num. !ginv:num->num.
         is_group carrier mul identity ginv
         ==> !H:num->num->bool.
               (!i:num.
                  i < n
                  ==> is_subgroup carrier mul identity ginv (H i) /\
                      H i PSUBSET carrier)
               ==> ~(UNIONS (IMAGE H {i:num | i < n}) =
                     carrier) in
   P 2 /\ ~P 3`;;
