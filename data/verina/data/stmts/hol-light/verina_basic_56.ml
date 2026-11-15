(*
  Statement-only formalization of VERINA corpus artifact verina_basic_56
  (verina__hol-light__verina_basic_56), catalog title "copy": an executable
  segment copy replaces a bounded portion of a destination integer array with
  the corresponding source segment, together with its bounds precondition and
  complete pointwise correctness contract. This file contains no proof.
*)

let copy_precond = new_definition
  `copy_precond
      (src:int list) (sStart:num) (dest:int list)
      (dStart:num) (len:num) <=>
     LENGTH src >= sStart + len /\
     LENGTH dest >= dStart + len`;;

let copy_getDefault = new_definition
  `copy_getDefault (xs:int list) (i:num) =
     if i < LENGTH xs then EL i xs else (&0:int)`;;

let copy_setAt =
  new_recursive_definition list_RECURSION
    `(!i:num. !value:int.
        copy_setAt ([]:int list) i value = []) /\
     (!x:int. !xs:int list. !i:num. !value:int.
        copy_setAt (CONS x xs) i value =
        if i = 0 then CONS value xs
        else CONS x (copy_setAt xs (PRE i) value))`;;

let copy_updateSegment_rec =
  new_recursive_definition num_RECURSION
    `(!r:int list. !src:int list. !sStart:num. !dStart:num.
        copy_updateSegment_rec 0 r src sStart dStart = r) /\
     (!n:num. !r:int list. !src:int list. !sStart:num. !dStart:num.
        copy_updateSegment_rec (SUC n) r src sStart dStart =
        copy_updateSegment_rec n
          (copy_setAt r (dStart + n)
            (copy_getDefault src (sStart + n)))
          src sStart dStart)`;;

let updateSegment = new_definition
  `updateSegment
      (r:int list) (src:int list) (sStart:num)
      (dStart:num) (n:num) =
     copy_updateSegment_rec n r src sStart dStart`;;

let copy = new_definition
  `copy
      (src:int list) (sStart:num) (dest:int list)
      (dStart:num) (len:num) =
     if len = 0 then dest
     else updateSegment dest src sStart dStart len`;;

let copy_postcond = new_definition
  `copy_postcond
      (src:int list) (sStart:num) (dest:int list)
      (dStart:num) (len:num) (result:int list) <=>
     LENGTH result = LENGTH dest /\
     (!i:num.
        i < dStart
        ==> copy_getDefault result i = copy_getDefault dest i) /\
     (!i:num.
        dStart + len <= i
        ==> i < LENGTH result
        ==> copy_getDefault result i = copy_getDefault dest i) /\
     (!i:num.
        i < len
        ==> copy_getDefault result (dStart + i) =
            copy_getDefault src (sStart + i))`;;

let copy_spec_satisfied =
  `!src:int list. !sStart:num. !dest:int list.
   !dStart:num. !len:num.
     copy_precond src sStart dest dStart len
     ==> copy_postcond
           src sStart dest dStart len
           (copy src sStart dest dStart len)`;;
