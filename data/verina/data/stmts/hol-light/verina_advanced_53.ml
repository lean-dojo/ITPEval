(*
  Statement-only formalization of VERINA corpus artifact verina_advanced_53,
  catalog title "minimumRightShifts": an executable bounded rotation scan
  returns the least number of right shifts that sorts a duplicate-free integer
  list, or -1 when no rotation sorts it. This file contains no proof.
*)

let minimumRightShifts_nodup =
  new_recursive_definition list_RECURSION
    `(minimumRightShifts_nodup ([]:int list) <=> T) /\
     (!x:int. !xs:int list.
        minimumRightShifts_nodup (CONS x xs) <=>
        ~(MEM x xs) /\ minimumRightShifts_nodup xs)`;;

let minimumRightShifts_precond = new_definition
  `minimumRightShifts_precond (nums:int list) <=>
     minimumRightShifts_nodup nums`;;

let minimumRightShifts_isSorted = new_definition
  `minimumRightShifts_isSorted (nums:int list) <=>
     PAIRWISE (\x y:int. x <= y) nums`;;

let minimumRightShifts_rightShiftOnce = new_definition
  `minimumRightShifts_rightShiftOnce (nums:int list) =
     let reversed = REVERSE nums in
     if reversed = [] then []
     else CONS (HD reversed) (REVERSE (TL reversed))`;;

let minimumRightShifts_check =
  new_recursive_definition num_RECURSION
    `(!count:num. !current:int list.
        minimumRightShifts_check 0 count current = (-- &1:int)) /\
     (!fuel:num. !count:num. !current:int list.
        minimumRightShifts_check (SUC fuel) count current =
        if minimumRightShifts_isSorted current then
          &count
        else
          minimumRightShifts_check fuel (SUC count)
            (minimumRightShifts_rightShiftOnce current))`;;

let minimumRightShifts = new_definition
  `minimumRightShifts (nums:int list) =
     let n = LENGTH nums in
     if n <= 1 then &0
     else if minimumRightShifts_isSorted nums then &0
     else
       minimumRightShifts_check (n - 1) 1
         (minimumRightShifts_rightShiftOnce nums)`;;

let minimumRightShifts_rotateRight =
  new_recursive_definition num_RECURSION
    `(!nums:int list.
        minimumRightShifts_rotateRight 0 nums = nums) /\
     (!k:num. !nums:int list.
        minimumRightShifts_rotateRight (SUC k) nums =
        minimumRightShifts_rotateRight k
          (minimumRightShifts_rightShiftOnce nums))`;;

let minimumRightShifts_postcond = new_definition
  `minimumRightShifts_postcond
      (nums:int list) (result:int) <=>
     let n = LENGTH nums in
     if n <= 1 then result = &0
     else
       (?k:num.
          result = &k /\
          k < n /\
          minimumRightShifts_isSorted
            (minimumRightShifts_rotateRight k nums) /\
          (!j:num.
             j < k
             ==> ~minimumRightShifts_isSorted
                   (minimumRightShifts_rotateRight j nums))) \/
       (result = -- &1 /\
        (!k:num.
           k < n
           ==> ~minimumRightShifts_isSorted
                 (minimumRightShifts_rotateRight k nums)))`;;

let minimumRightShifts_spec_satisfied =
  `!nums:int list.
     minimumRightShifts_precond nums
     ==> minimumRightShifts_postcond
           nums (minimumRightShifts nums)`;;
