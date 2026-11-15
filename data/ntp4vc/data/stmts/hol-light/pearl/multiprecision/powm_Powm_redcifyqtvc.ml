(*
  Statement-only formalization of NTP4VC corpus artifact
  pearl/multiprecision/powm_Powm_redcifyqtvc: the verification condition for
  converting a multiprecision integer to Montgomery form by zero-extension,
  copying, and quotient-remainder division. This file contains no proof.
*)

needs "Library/words.ml";;
needs "Library/isum.ml";;

new_type_abbrev
  ("redq_ptr",`:(int64 list)#(int#(int#(int#(bool#'z))))`);;

let redq_radix = new_definition
  `redq_radix = (&18446744073709551616:int)`;;

let redq_u64 = new_definition
  `redq_u64 (x:int64) = (&(val x):int)`;;

let redq_u32 = new_definition
  `redq_u32 (x:int32) = (&(val x):int)`;;

let redq_int32_in_bounds = new_definition
  `redq_int32_in_bounds (x:int) <=>
     --(&2147483648:int) <= x /\ x <= (&2147483647:int)`;;

let redq_ipow = new_definition
  `redq_ipow (base:int) (exponent:int) =
     base pow (if exponent < (&0:int) then 0 else num_of_int exponent)`;;

let redq_data = new_definition
  `redq_data (p:redq_ptr) = FST p`;;

let redq_offset = new_definition
  `redq_offset (p:redq_ptr) = FST (SND p)`;;

let redq_minimum = new_definition
  `redq_minimum (p:redq_ptr) = FST (SND (SND p))`;;

let redq_maximum = new_definition
  `redq_maximum (p:redq_ptr) = FST (SND (SND (SND p)))`;;

let redq_writable = new_definition
  `redq_writable (p:redq_ptr) =
     FST (SND (SND (SND (SND p))))`;;

let redq_zone = new_definition
  `redq_zone (p:redq_ptr) =
     SND (SND (SND (SND (SND p))))`;;

let redq_pelts = new_definition
  `redq_pelts p (i:int) =
     let k = if i < (&0:int) then 0 else num_of_int i in
     if k < LENGTH (redq_data p)
     then EL k (redq_data p)
     else (word 0:int64)`;;

let redq_plength = new_definition
  `redq_plength p = (&(LENGTH (redq_data p)):int)`;;

let redq_valid = new_definition
  `redq_valid p (size:int) <=>
     redq_int32_in_bounds size /\
     (&0:int) <= size /\
     (&0:int) <= redq_minimum p /\
     redq_minimum p <= redq_offset p /\
     redq_offset p + size <= redq_maximum p /\
     redq_maximum p <= redq_plength p`;;

let redq_value = new_definition
  `redq_value p (size:int) =
     if size <= (&0:int) then (&0:int)
     else
       isum (0..num_of_int size - 1)
         (\k. redq_radix pow k *
              redq_u64 (redq_pelts p (redq_offset p + &k)))`;;

let redq_redc = new_definition
  `redq_redc (ur:int) (u:int) (n:int) (m:int) <=>
     ur rem m = (redq_ipow redq_radix n * u) rem m`;;

let redq_allocation = new_definition
  `redq_allocation p (size:int) <=>
     redq_plength p = size /\
     redq_offset p = (&0:int) /\
     redq_minimum p = (&0:int) /\
     redq_maximum p = size /\
     redq_writable p = T`;;

let redq_same_metadata = new_definition
  `redq_same_metadata newer older <=>
     LENGTH (redq_data newer) = LENGTH (redq_data older) /\
     redq_offset newer = redq_offset older /\
     redq_minimum newer = redq_minimum older /\
     redq_maximum newer = redq_maximum older /\
     redq_writable newer = redq_writable older /\
     redq_zone newer = redq_zone older`;;

let redq_frame = new_definition
  `redq_frame newer older (size:int) <=>
     !j:int.
       j < redq_offset newer \/
       redq_offset newer + size <= j
       ==> redq_pelts newer j = redq_pelts older j`;;

let redq_shifted_pointer = new_definition
  `redq_shifted_pointer shifted base (displacement:int) <=>
     redq_offset shifted = redq_offset base + displacement /\
     redq_plength shifted = redq_plength base /\
     redq_pelts shifted = redq_pelts base /\
     redq_data shifted = redq_data base /\
     redq_minimum shifted = redq_minimum base /\
     redq_maximum shifted = redq_maximum base /\
     redq_zone shifted = redq_zone base /\
     redq_writable shifted = redq_writable base`;;

let redq_map_eq_sub_shift = new_definition
  `redq_map_eq_sub_shift newer older
      (new_offset:int) (old_offset:int) (size:int) <=>
     !i:int.
       (&0:int) <= i /\ i < size
       ==> newer (new_offset + i) = older (old_offset + i)`;;

let redq_copy_outputs = new_definition
  `redq_copy_outputs o6 tp2 o5 <=>
     redq_data o6 = redq_data tp2 /\
     LENGTH (redq_data tp2) = LENGTH (redq_data o5) /\
     redq_offset o6 = redq_offset o5 /\
     redq_minimum o6 = redq_minimum o5 /\
     redq_maximum o6 = redq_maximum o5 /\
     redq_writable o6 = redq_writable o5 /\
     redq_zone o6 = redq_zone o5`;;

let redq_division_result = new_definition
  `redq_division_result tp qp rp mp (total:int) (n:int) <=>
     redq_value tp total =
       redq_value qp (total - n + (&1:int)) *
       redq_value mp n +
       redq_value rp n /\
     redq_value rp n < redq_value mp n`;;

let redq_postcondition = new_definition
  `redq_postcondition rp up (un:int) mp (n:int) <=>
     redq_value rp n =
       (redq_ipow redq_radix n * redq_value up un) rem
       redq_value mp n /\
     redq_redc
       (redq_value rp n) (redq_value up un) n (redq_value mp n)`;;

let statement =
  `!rp:((int64 list)#(int#(int#(int#(bool#'z))))).
   !n:int32.
   !up:((int64 list)#(int#(int#(int#(bool#'z))))).
   !un:int32.
   !mp:((int64 list)#(int#(int#(int#(bool#'z))))).
     redq_valid rp (ival n) /\
     redq_valid up (ival un) /\
     redq_valid mp (ival n) /\
     (&1:int) <= ival n /\
     (&1:int) <= ival un /\
     ival un + ival n < (&2147483647:int) /\
     (&0:int) <
       redq_u64
         (redq_pelts mp
           (redq_offset mp + ival n - (&1:int))) /\
     redq_writable rp = T
     ==>
     redq_int32_in_bounds (ival un + ival n) /\
     (!o1:int32.
        ival o1 = ival un + ival n
        ==>
        (&0:int) <= ival o1 /\
        (!o2:int32.
           redq_u32 o2 = ival o1
           ==>
           (&0:int) <= redq_u32 o2 /\
           (!tp:((int64 list)#(int#(int#(int#(bool#'z))))).
              redq_allocation tp (redq_u32 o2)
              ==>
              redq_int32_in_bounds (ival un + (&1:int)) /\
              (!o3:int32.
                 ival o3 = ival un + (&1:int)
                 ==>
                 (&0:int) <= ival o3 /\
                 (!o4:int32.
                    redq_u32 o4 = ival o3
                    ==>
                    (&0:int) <= redq_u32 o4 /\
                    (!qp:((int64 list)#(int#(int#(int#(bool#'z))))).
                       redq_allocation qp (redq_u32 o4)
                       ==>
                       (redq_valid tp (ival n) /\
                        redq_writable tp = T) /\
                       (!tp1:((int64 list)#(int#(int#(int#(bool#'z))))).
                          redq_same_metadata tp1 tp
                          ==>
                          redq_value tp1 (ival n) = (&0:int) /\
                          redq_frame tp1 tp (ival n)
                          ==>
                          (redq_minimum tp1 <=
                             redq_offset tp1 + ival n /\
                           redq_offset tp1 + ival n <=
                             redq_maximum tp1) /\
                          (!o5:((int64 list)#(int#(int#(int#(bool#'z))))).
                             redq_shifted_pointer o5 tp1 (ival n)
                             ==>
                             (redq_valid up (ival un) /\
                              redq_valid o5 (ival un) /\
                              redq_writable o5 = T) /\
                             (!o6:((int64 list)#(int#(int#(int#(bool#'z))))).
                              !tp2:((int64 list)#(int#(int#(int#(bool#'z))))).
                                redq_copy_outputs o6 tp2 o5
                                ==>
                                redq_same_metadata tp2 tp1
                                ==>
                                redq_map_eq_sub_shift
                                  (redq_pelts o6) (redq_pelts up)
                                  (redq_offset o6) (redq_offset up)
                                  (ival un) /\
                                redq_frame o6 o5 (ival un)
                                ==>
                                redq_int32_in_bounds
                                  (ival un + ival n) /\
                                (!o7:int32.
                                   ival o7 = ival un + ival n
                                   ==>
                                   (((&1:int) <= ival n /\
                                     ival n <= ival o7 /\
                                     ival o7 <=
                                       (&2147483647:int) - (&1:int)) /\
                                    redq_valid tp2 (ival o7) /\
                                    redq_valid mp (ival n) /\
                                    redq_valid qp
                                      (ival o7 - ival n + (&1:int)) /\
                                    redq_valid rp (ival n) /\
                                    (redq_writable qp = T /\
                                     redq_writable rp = T) /\
                                    (&0:int) <
                                      redq_u64
                                        (redq_pelts mp
                                          (redq_offset mp + ival n -
                                           (&1:int)))) /\
                                   (!qp1:((int64 list)#(int#(int#(int#(bool#'z))))).
                                    !rp1:((int64 list)#(int#(int#(int#(bool#'z))))).
                                      redq_same_metadata qp1 qp
                                      ==>
                                      redq_same_metadata rp1 rp
                                      ==>
                                      redq_division_result
                                        tp2 qp1 rp1 mp (ival o7) (ival n)
                                      ==>
                                      redq_postcondition
                                        rp1 up (ival un) mp
                                        (ival n))))))))))))`;;
