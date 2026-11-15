(*
  Statement-only formalization of NTP4VC corpus artifact
  pearl/multiprecision/compare_Compare_wmpn_cmpqtvc: the loop verification
  condition for comparing two valid equal-length multiprecision unsigned
  integers by scanning their 64-bit limbs from most to least significant.
  This file contains no proof.
*)

needs "Library/words.ml";;
needs "Library/isum.ml";;

let mpcmp_radix = new_definition
  `mpcmp_radix = (&18446744073709551616:int)`;;

let mpcmp_int32_in_bounds = new_definition
  `mpcmp_int32_in_bounds (z:int) <=>
     --(&2147483648:int) <= z /\ z <= (&2147483647:int)`;;

let mpcmp_value = new_definition
  `mpcmp_value
     (pelts:'p->int->int64) (offset:'p->int) (p:'p) (n:int) =
     if n <= (&0:int) then (&0:int)
     else
       isum (0..num_of_int n - 1)
         (\k. mpcmp_radix pow k *
              (&(val (pelts p (offset p + &k))):int))`;;

let mpcmp_valid = new_definition
  `mpcmp_valid
     (data_length:'p->num)
     (offset:'p->int)
     (minimum:'p->int)
     (maximum:'p->int)
     (p:'p) (n:int) <=>
     mpcmp_int32_in_bounds n /\
     (&0:int) <= n /\
     ((&0:int) <= minimum p /\ minimum p <= offset p) /\
     offset p + n <= maximum p /\
     maximum p <= &(data_length p)`;;

let mpcmp_compare_int = new_definition
  `mpcmp_compare_int (x:int) (y:int) =
     if x < y then --(&1:int)
     else if x = y then (&0:int)
     else (&1:int)`;;

let mpcmp_range_equal = new_definition
  `mpcmp_range_equal
     (pelts:'p->int->int64)
     (offset:'p->int)
     (x:'p) (y:'p) (lower:int) (upper:int) <=>
     !j:int.
       lower <= j /\ j < upper
       ==> pelts x (offset x + j) = pelts y (offset y + j)`;;

let mpcmp_comparison = new_definition
  `mpcmp_comparison
     (pelts:'p->int->int64)
     (offset:'p->int)
     (x:'p) (y:'p) (size:int) =
     mpcmp_compare_int
       (mpcmp_value pelts offset x size)
       (mpcmp_value pelts offset y size)`;;

let mpcmp_loop_step = new_definition
  `mpcmp_loop_step
     (offset:'p->int)
     (minimum:'p->int)
     (maximum:'p->int)
     (pelts:'p->int->int64)
     (x:'p) (size:int32) (y:'p) (i:int32) <=>
     (((&0:int) <= ival i /\ ival i <= ival size) /\
      mpcmp_range_equal pelts offset x y (ival i) (ival size))
     ==>
     if (&1:int) <= ival i then
       mpcmp_int32_in_bounds (ival i - (&1:int)) /\
       (!previous:int32.
          ival previous = ival i - (&1:int)
          ==>
          (minimum x <= offset x + ival previous /\
           offset x + ival previous < maximum x) /\
          (let lx = pelts x (offset x + ival previous) in
           (minimum y <= offset y + ival previous /\
            offset y + ival previous < maximum y) /\
           (let ly = pelts y (offset y + ival previous) in
            !equal_flag:bool.
              ((val lx = val ly ==> equal_flag = T) /\
               (equal_flag = T ==> lx = ly))
              ==>
              if ~(equal_flag = T) then
                if val ly < val lx then
                  (&1:int) =
                    mpcmp_comparison
                      pelts offset x y (ival size)
                else
                  --(&1:int) =
                    mpcmp_comparison
                      pelts offset x y (ival size)
              else
                ival previous < ival i /\
                ((&0:int) <= ival previous /\
                 ival previous <= ival size) /\
                mpcmp_range_equal
                  pelts offset x y (ival previous) (ival size))))
     else
       (&0:int) =
         mpcmp_comparison pelts offset x y (ival size)`;;

let statement =
  `!data_length:'p->num.
   !offset minimum maximum:'p->int.
   !pelts:'p->int->int64.
   !x:'p. !size:int32. !y:'p.
     mpcmp_valid
       data_length offset minimum maximum x (ival size)
     ==>
     mpcmp_valid
       data_length offset minimum maximum y (ival size)
     ==>
     ((&0:int) <= ival size) /\
     ival size <= ival size /\
     mpcmp_range_equal pelts offset x y (ival size) (ival size) /\
     (!i:int32.
        mpcmp_loop_step offset minimum maximum pelts x size y i)`;;
