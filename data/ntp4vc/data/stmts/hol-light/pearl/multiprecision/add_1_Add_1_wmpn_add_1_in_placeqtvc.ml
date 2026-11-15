(*
  Statement-only formalization of NTP4VC corpus artifact
  pearl/multiprecision/add_1_Add_1_wmpn_add_1_in_placeqtvc:
  the verification condition for in-place addition of one 64-bit limb,
  including pointer updates, carry invariants, framing, and loop
  continuations. This file contains no proof.
*)

needs "Library/words.ml";;
needs "Library/isum.ml";;

let mpadd1_radix = new_definition
  `mpadd1_radix = (&18446744073709551616:int)`;;

let mpadd1_int32_in_bounds = new_definition
  `mpadd1_int32_in_bounds (z:int) <=>
     --(&2147483648:int) <= z /\ z <= (&2147483647:int)`;;

let mpadd1_radix_power = new_definition
  `mpadd1_radix_power (n:int) =
     mpadd1_radix pow (if n < (&0:int) then 0 else num_of_int n)`;;

let mpadd1_value = new_definition
  `mpadd1_value
     (pelts:'p->int->int64) (offset:'p->int) (p:'p) (n:int) =
     if n <= (&0:int) then (&0:int)
     else
       isum (0..num_of_int n - 1)
         (\k. mpadd1_radix pow k *
              (&(val (pelts p (offset p + &k))):int))`;;

let mpadd1_valid = new_definition
  `mpadd1_valid
     (data_length:'p->num)
     (offset:'p->int)
     (minimum:'p->int)
     (maximum:'p->int)
     (p:'p) (n:int) <=>
     mpadd1_int32_in_bounds n /\
     (&0:int) <= n /\
     (&0:int) <= minimum p /\
     minimum p <= offset p /\
     offset p + n <= maximum p /\
     maximum p <= &(data_length p)`;;

let mpadd1_same_snapshot = new_definition
  `mpadd1_same_snapshot
     (data_length:'p->num)
     (offset:'p->int)
     (minimum:'p->int)
     (maximum:'p->int)
     (writable:'p->bool)
     (zone:'p->'z)
     (new:'p) (old:'p) <=>
     data_length new = data_length old /\
     offset new = offset old /\
     minimum new = minimum old /\
     maximum new = maximum old /\
     writable new = writable old /\
     zone new = zone old`;;

let mpadd1_single_update = new_definition
  `mpadd1_single_update
     (pelts:'p->int->int64)
     (new:'p) (old:'p) (index:int) (value:int64) <=>
     !j:int.
       pelts new j =
       if j = index then value else pelts old j`;;

let mpadd1_frame = new_definition
  `mpadd1_frame
     (offset:'p->int)
     (pelts:'p->int->int64)
     (new:'p) (old:'p) (count:int) <=>
     !j:int.
       j < offset new \/ offset new + count <= j
       ==> pelts new j = pelts old j`;;

let mpadd1_final_state = new_definition
  `mpadd1_final_state
     (offset:'p->int)
     (pelts:'p->int->int64)
     (state:'p) (old:'p) (size:int) (addend:int) (carry:int) <=>
     mpadd1_value pelts offset state size +
       mpadd1_radix_power size * carry =
       mpadd1_value pelts offset old size + addend /\
     (&0:int) <= carry /\ carry <= (&1:int) /\
     mpadd1_frame offset pelts state old size`;;

let mpadd1_loop_invariant = new_definition
  `mpadd1_loop_invariant
     (offset:'p->int)
     (pelts:'p->int->int64)
     (state:'p) (old:'p)
     (index:int32) (carry:int64) (size:int32) (addend:int64) <=>
     (&1:int) <= ival index /\ ival index <= ival size /\
     (&0:int) <= (&(val carry):int) /\
     (&(val carry):int) <= (&1:int) /\
     ((&(val carry):int) = (&1:int) \/ index = size) /\
     mpadd1_value pelts offset state (ival index) +
       mpadd1_radix_power (ival index) * (&(val carry):int) =
       mpadd1_value pelts offset old (ival index) +
       (&(val addend):int) /\
     mpadd1_frame offset pelts state old (ival index)`;;

let mpadd1_initial_carry_invariant = new_definition
  `mpadd1_initial_carry_invariant
     (offset:'p->int)
     (pelts:'p->int->int64)
     (state:'p) (old:'p) (size:int32) (addend:int64) <=>
     ((&1:int) <= (&1:int) /\ (&1:int) <= ival size) /\
     ((&0:int) <= (&(val (word 1:int64)):int) /\
      (&(val (word 1:int64)):int) <= (&1:int)) /\
     ((&(val (word 1:int64)):int) = (&1:int) \/
      (word 1:int32) = size) /\
     mpadd1_value pelts offset state (&1:int) +
       mpadd1_radix_power (&1:int) * (&(val (word 1:int64)):int) =
       mpadd1_value pelts offset old (&1:int) +
       (&(val addend):int) /\
     mpadd1_frame offset pelts state old (&1:int)`;;

let statement =
  `!data_length:'p->num.
   !offset minimum maximum:'p->int.
   !writable:'p->bool.
   !zone:'p->'z.
   !pelts:'p->int->int64.
   !x:'p. !sz:int32. !y:int64.
     mpadd1_valid data_length offset minimum maximum x (ival sz)
     ==> (&0:int) < ival sz
     ==> writable x = T
     ==> minimum x <= offset x /\
         offset x < maximum x /\
         (let o1:int64 = pelts x (offset x) in
          !res:int64.
            (&(val res):int) =
              ((&(val o1):int) + (&(val y):int)) rem mpadd1_radix
            ==>
            ((minimum x <= offset x /\ offset x < maximum x) /\
             writable x = T) /\
            (!x1:'p.
               mpadd1_same_snapshot
                 data_length offset minimum maximum writable zone x1 x
               ==>
               mpadd1_single_update
                 pelts x1 x (offset x1) res
               ==>
               if (&(val res):int) < (&(val o1):int) then
                 mpadd1_initial_carry_invariant
                   offset pelts x1 x sz y /\
                 (!i:int32. !c:int64. !x2:'p.
                    mpadd1_same_snapshot
                      data_length offset minimum maximum writable zone x2 x1
                    ==>
                    mpadd1_loop_invariant
                      offset pelts x2 x i c sz y
                    ==>
                    if ival i < ival sz then
                      (minimum x2 <= offset x2 + ival i /\
                       offset x2 + ival i < maximum x2) /\
                      (!res1:int64.
                         (&(val res1):int) =
                           ((&(val (pelts x2 (offset x2 + ival i))):int) +
                            (&1:int)) rem mpadd1_radix
                         ==>
                         ((minimum x2 <= offset x2 + ival i /\
                           offset x2 + ival i < maximum x2) /\
                          writable x2 = T) /\
                         (!x3:'p.
                            mpadd1_same_snapshot
                              data_length offset minimum maximum writable zone
                              x3 x2
                            ==>
                            (mpadd1_single_update
                               pelts x3 x2 (offset x3 + ival i) res1 /\
                             pelts x3 (offset x3 + ival i) = res1)
                            ==>
                            mpadd1_int32_in_bounds (ival i + (&1:int)) /\
                            (!o2:int32.
                               ival o2 = ival i + (&1:int)
                               ==>
                               (!o3:bool.
                                  (((&(val res1):int) =
                                      (&(val (word 0:int64)):int)
                                     ==> o3 = T) /\
                                   (o3 = T
                                    ==> res1 = (word 0:int64)))
                                  ==>
                                  if ~(o3 = T) then
                                    mpadd1_final_state
                                      offset pelts x3 x (ival sz)
                                      (&(val y):int)
                                      (&(val (word 0:int64)):int)
                                  else
                                    ((&0:int) <= ival sz - ival i /\
                                     ival sz - ival o2 <
                                       ival sz - ival i) /\
                                    mpadd1_loop_invariant
                                      offset pelts x3 x o2 c sz y))))
                    else
                      mpadd1_final_state
                        offset pelts x2 x (ival sz)
                        (&(val y):int) (&(val c):int))
               else
                 mpadd1_final_state
                   offset pelts x1 x (ival sz) (&(val y):int) (&0:int)))`;;
