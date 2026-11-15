(*
  Statement-only formalization of VERINA corpus artifact verina_basic_90
  (verina__hol-light__verina_basic_90), catalog title "SlopeSearch": an
  executable fuel-bounded slope search in a nonempty rectangular integer
  matrix sorted by rows and columns returns a matching position or (-1,-1),
  together with its exact precondition and postcondition. This file contains
  no proof.
*)

let SlopeSearch_intToNat = new_definition
  `SlopeSearch_intToNat (z:int) =
     if z < (&0:int) then 0 else num_of_int z`;;

let SlopeSearch_getDefault = new_definition
  `SlopeSearch_getDefault (xs:int list) (i:num) =
     if i < LENGTH xs then EL i xs else (&0:int)`;;

let SlopeSearch_getRowDefault = new_definition
  `SlopeSearch_getRowDefault (a:(int list) list) (i:num) =
     if i < LENGTH a then EL i a else ([]:int list)`;;

let SlopeSearch_get2d = new_definition
  `SlopeSearch_get2d
      (a:(int list) list) (i:int) (j:int) =
     SlopeSearch_getDefault
       (SlopeSearch_getRowDefault a (SlopeSearch_intToNat i))
       (SlopeSearch_intToNat j)`;;

let SlopeSearch_precond = new_definition
  `SlopeSearch_precond (a:(int list) list) (key:int) <=>
     0 < LENGTH a /\
     0 < LENGTH (SlopeSearch_getRowDefault a 0) /\
     PAIRWISE
       (\x y:int list. LENGTH x = LENGTH y)
       a /\
     ALL
       (\row:int list.
          PAIRWISE (\x y:int. x <= y) row)
       a /\
     (!j:num.
        j < LENGTH (SlopeSearch_getRowDefault a 0)
        ==> PAIRWISE
              (\x y:int. x <= y)
              (MAP
                (\row:int list. SlopeSearch_getDefault row j)
                a))`;;

let SlopeSearch_aux =
  new_recursive_definition num_RECURSION
    `(!a:(int list) list. !key:int. !rows:num. !m:int. !n:int.
        SlopeSearch_aux 0 a key rows m n =
        ((-- &1:int),(-- &1:int))) /\
     (!fuel:num. !a:(int list) list. !key:int. !rows:num.
      !m:int. !n:int.
        SlopeSearch_aux (SUC fuel) a key rows m n =
        if m >= (&rows:int) \/ n < (&0:int) then
          ((-- &1:int),(-- &1:int))
        else if SlopeSearch_get2d a m n = key then
          (m,n)
        else if SlopeSearch_get2d a m n < key then
          SlopeSearch_aux
            fuel a key rows (m + (&1:int)) n
        else
          SlopeSearch_aux
            fuel a key rows m (n - (&1:int)))`;;

let SlopeSearch = new_definition
  `SlopeSearch (a:(int list) list) (key:int) =
     let rows = LENGTH a in
     let cols =
       if rows > 0 then
         LENGTH (SlopeSearch_getRowDefault a 0)
       else
         0 in
     SlopeSearch_aux
       (rows + cols) a key rows
       (&0:int) (&(cols - 1):int)`;;

let SlopeSearch_postcond = new_definition
  `SlopeSearch_postcond
      (a:(int list) list) (key:int) (result:int#int) <=>
     let m = FST result in
     let n = SND result in
     ((&0:int) <= m /\
      m < (&(LENGTH a):int) /\
      (&0:int) <= n /\
      n <
        (&(LENGTH (SlopeSearch_getRowDefault a 0)):int) /\
      SlopeSearch_get2d a m n = key) \/
     (m = (-- &1:int) /\
      n = (-- &1:int) /\
      ALL
        (\row:int list.
           ALL (\e:int. ~(e = key)) row)
        a)`;;

let SlopeSearch_spec_satisfied =
  `!a:(int list) list. !key:int.
     SlopeSearch_precond a key
     ==> SlopeSearch_postcond
           a key (SlopeSearch a key)`;;
