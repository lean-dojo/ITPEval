(*
  Statement-only formalization of NTP4VC corpus artifact
  pearl/multiprecision/add_Add_add_n_rxyqtvc: the verification condition for
  in-place doubling of a multiprecision value, including the 64-bit carry,
  pointer validity, memory framing, and preservation of pointer bounds and
  length metadata. This file contains no proof.
*)

needs "Library/words.ml";;
needs "Library/isum.ml";;

let addnrxy_radix = new_definition
  `addnrxy_radix = (&18446744073709551616:int)`;;

let addnrxy_int32_in_bounds = new_definition
  `addnrxy_int32_in_bounds (z:int) <=>
     --(&2147483648:int) <= z /\ z <= (&2147483647:int)`;;

let addnrxy_radix_power = new_definition
  `addnrxy_radix_power (n:int) =
     addnrxy_radix pow (if n < (&0:int) then 0 else num_of_int n)`;;

let addnrxy_value = new_definition
  `addnrxy_value
     (pelts:'p->int->int64) (offset:'p->int) (p:'p) (n:int) =
     if n <= (&0:int) then (&0:int)
     else
       isum (0..num_of_int n - 1)
         (\k. addnrxy_radix pow k *
              (&(val (pelts p (offset p + &k))):int))`;;

let addnrxy_plength = new_definition
  `addnrxy_plength (data_length:'p->num) (p:'p) =
     (&(data_length p):int)`;;

let addnrxy_valid = new_definition
  `addnrxy_valid
     (data_length:'p->num)
     (offset:'p->int)
     (minimum:'p->int)
     (maximum:'p->int)
     (p:'p) (n:int) <=>
     addnrxy_int32_in_bounds n /\
     (&0:int) <= n /\
     (&0:int) <= minimum p /\
     minimum p <= offset p /\
     offset p + n <= maximum p /\
     maximum p <= addnrxy_plength data_length p`;;

let addnrxy_same_snapshot = new_definition
  `addnrxy_same_snapshot
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

let addnrxy_carry_range = new_definition
  `addnrxy_carry_range (carry:int64) <=>
     (&0:int) <= (&(val carry):int) /\
     (&(val carry):int) <= (&1:int)`;;

let addnrxy_value_equation = new_definition
  `addnrxy_value_equation
     (offset:'p->int)
     (pelts:'p->int->int64)
     (new:'p) (old:'p) (size:int32) (carry:int64) <=>
     addnrxy_value pelts offset new (ival size) +
       addnrxy_radix_power (ival size) * (&(val carry):int) =
     addnrxy_value pelts offset old (ival size) +
       addnrxy_value pelts offset old (ival size)`;;

let addnrxy_frame = new_definition
  `addnrxy_frame
     (offset:'p->int)
     (pelts:'p->int->int64)
     (new:'p) (old:'p) (size:int32) <=>
     !j:int.
       j < offset new \/ offset new + ival size <= j
       ==> pelts new j = pelts old j`;;

let statement =
  `!data_length:'p->num.
   !offset minimum maximum:'p->int.
   !writable:'p->bool.
   !zone:'p->'z.
   !pelts:'p->int->int64.
   !size:int32. !x:'p.
     (&0:int) <= ival size
     ==>
     writable x = T
     ==>
     addnrxy_valid
       data_length offset minimum maximum x (ival size)
     ==>
     ((&0:int) <= ival size) /\
     addnrxy_valid
       data_length offset minimum maximum x (ival size) /\
     writable x = T /\
     (!x1:'p.
        addnrxy_same_snapshot
          data_length offset minimum maximum writable zone x1 x
        ==>
        (!result:int64.
           addnrxy_value_equation offset pelts x1 x size result /\
           addnrxy_carry_range result /\
           addnrxy_frame offset pelts x1 x size
           ==>
           addnrxy_value_equation offset pelts x1 x size result /\
           addnrxy_carry_range result /\
           addnrxy_frame offset pelts x1 x size /\
           minimum x1 = minimum x /\
           maximum x1 = maximum x /\
           addnrxy_plength data_length x1 =
             addnrxy_plength data_length x))`;;
