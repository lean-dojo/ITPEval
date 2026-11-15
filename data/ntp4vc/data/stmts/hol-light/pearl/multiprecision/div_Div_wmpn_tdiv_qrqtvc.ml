(*
  Statement-only formalization of NTP4VC corpus artifact
  pearl/multiprecision/div_Div_wmpn_tdiv_qrqtvc: the verification condition
  for multiprecision division with allocated scratch pointers, pointer frame
  conditions, and the quotient-remainder value relation. This file contains
  no proof.
*)

let wtdqr_output = open_out "/dev/null";;
Format.pp_set_formatter_out_channel Format.std_formatter wtdqr_output;;

needs "Library/words.ml";;
needs "Library/isum.ml";;

let wtdqr_radix = new_definition
  `wtdqr_radix = (&18446744073709551616:int)`;;

let wtdqr_u32 = new_definition
  `wtdqr_u32 (x:int32) = (&(val x):int)`;;

let wtdqr_u64 = new_definition
  `wtdqr_u64 (x:int64) = (&(val x):int)`;;

let wtdqr_int32_in_bounds = new_definition
  `wtdqr_int32_in_bounds (z:int) <=>
     --(&2147483648:int) <= z /\ z <= (&2147483647:int)`;;

let wtdqr_uint32_in_bounds = new_definition
  `wtdqr_uint32_in_bounds (z:int) <=>
     (&0:int) <= z /\ z <= (&4294967295:int)`;;

let wtdqr_plength = new_definition
  `wtdqr_plength (data_length:'p->num) (p:'p) =
     (&(data_length p):int)`;;

let wtdqr_valid = new_definition
  `wtdqr_valid
     (data_length:'p->num)
     (offset:'p->int)
     (minimum:'p->int)
     (maximum:'p->int)
     (p:'p) (size:int) <=>
     wtdqr_int32_in_bounds size /\
     (&0:int) <= size /\
     (&0:int) <= minimum p /\
     minimum p <= offset p /\
     offset p + size <= maximum p /\
     maximum p <= wtdqr_plength data_length p`;;

let wtdqr_value = new_definition
  `wtdqr_value
     (pelts:'p->int->int64)
     (offset:'p->int)
     (p:'p) (size:int) =
     if size <= (&0:int) then (&0:int)
     else
       isum (0..num_of_int size - 1)
         (\k. wtdqr_radix pow k *
              wtdqr_u64 (pelts p (offset p + &k)))`;;

let wtdqr_allocation_description = new_definition
  `wtdqr_allocation_description
     (data_length:'p->num)
     (offset:'p->int)
     (minimum:'p->int)
     (maximum:'p->int)
     (writable:'p->bool)
     (zone:'p->'z)
     (null_zone:'z)
     (p:'p) (size:int) <=>
     (~(zone p = null_zone)
      ==> wtdqr_plength data_length p = size) /\
     offset p = (&0:int) /\
     minimum p = (&0:int) /\
     maximum p = wtdqr_plength data_length p /\
     writable p = T`;;

let wtdqr_same_metadata = new_definition
  `wtdqr_same_metadata
     (data_length:'p->num)
     (offset:'p->int)
     (minimum:'p->int)
     (maximum:'p->int)
     (writable:'p->bool)
     (zone:'p->'z)
     (newer:'p) (older:'p) <=>
     data_length newer = data_length older /\
     offset newer = offset older /\
     minimum newer = minimum older /\
     maximum newer = maximum older /\
     writable newer = writable older /\
     zone newer = zone older`;;

let wtdqr_canonical_freed_pointer = new_definition
  `wtdqr_canonical_freed_pointer
     (data_length:'p->num)
     (offset:'p->int)
     (minimum:'p->int)
     (maximum:'p->int)
     (writable:'p->bool)
     (p:'p) <=>
     offset p = (&0:int) /\
     minimum p = (&0:int) /\
     maximum p = wtdqr_plength data_length p /\
     writable p = T`;;

let wtdqr_division_result = new_definition
  `wtdqr_division_result
     (pelts:'p->int->int64)
     (offset:'p->int)
     (sy:int32) (sx:int32)
     (x:'p) (y:'p) (q1:'p) (r1:'p) <=>
     wtdqr_value pelts offset x (ival sx) =
       wtdqr_value pelts offset q1
         (ival sx - ival sy + (&1:int)) *
       wtdqr_value pelts offset y (ival sy) +
       wtdqr_value pelts offset r1 (ival sy) /\
     wtdqr_value pelts offset r1 (ival sy) <
       wtdqr_value pelts offset y (ival sy)`;;

let statement =
  `!data_length:'p->num.
   !offset:'p->int.
   !minimum:'p->int.
   !maximum:'p->int.
   !writable:'p->bool.
   !zone:'p->'z.
   !null_zone:'z.
   !pelts:'p->int->int64.
   !is_not_null:'p->bool.
   !sy:int32. !sx:int32.
   !x:'p. !y:'p. !q:'p. !r:'p. !qxn:int32.
     (&1:int) <= ival sy /\
     ival sy <= ival sx /\
     ival sx <= (&2147483647:int) - (&1:int) /\
     wtdqr_valid data_length offset minimum maximum x (ival sx) /\
     wtdqr_valid data_length offset minimum maximum y (ival sy) /\
     wtdqr_valid data_length offset minimum maximum q
       (ival sx - ival sy + (&1:int)) /\
     wtdqr_valid data_length offset minimum maximum r (ival sy) /\
     writable q = T /\
     writable r = T /\
     ival qxn = (&0:int) /\
     (&0:int) <
       wtdqr_u64 (pelts y (offset y + ival sy - (&1:int)))
     ==>
     (&0:int) <= ival sx /\
     (!o1:int32.
        wtdqr_u32 o1 = ival sx
        ==>
        wtdqr_uint32_in_bounds (wtdqr_u32 o1 + (&1:int)) /\
        (!o2:int32.
           wtdqr_u32 o2 = wtdqr_u32 o1 + (&1:int)
           ==>
           (&0:int) <= wtdqr_u32 o2 /\
           (!nx:'p.
              wtdqr_allocation_description
                data_length offset minimum maximum writable zone null_zone
                nx (wtdqr_u32 o2)
              ==>
              is_not_null nx = ~(zone nx = null_zone)
              ==>
              is_not_null nx
              ==>
              (&0:int) <= ival sy /\
              (!o3:int32.
                 wtdqr_u32 o3 = ival sy
                 ==>
                 (&0:int) <= wtdqr_u32 o3 /\
                 (!ny:'p.
                    wtdqr_allocation_description
                      data_length offset minimum maximum writable zone
                      null_zone ny (wtdqr_u32 o3)
                    ==>
                    is_not_null ny = ~(zone ny = null_zone)
                    ==>
                    is_not_null ny
                    ==>
                    (((&1:int) <= ival sy /\
                       ival sy <= ival sx /\
                       ival sx <= (&2147483647:int) - (&1:int)) /\
                      wtdqr_valid
                        data_length offset minimum maximum x (ival sx) /\
                      wtdqr_valid
                        data_length offset minimum maximum y (ival sy) /\
                      wtdqr_valid
                        data_length offset minimum maximum q
                        (ival sx - ival sy + (&1:int)) /\
                      wtdqr_valid
                        data_length offset minimum maximum r (ival sy) /\
                      wtdqr_valid
                        data_length offset minimum maximum nx
                        (ival sx + (&1:int)) /\
                      wtdqr_valid
                        data_length offset minimum maximum ny (ival sy) /\
                      (writable nx = T /\ writable ny = T) /\
                      (&0:int) <
                        wtdqr_u64
                          (pelts y
                            (offset y + ival sy - (&1:int))) /\
                      writable q = T /\
                      writable r = T) /\
                    (!ny1 nx1 r1 q1:'p.
                       wtdqr_same_metadata
                         data_length offset minimum maximum writable zone
                         ny1 ny
                       ==>
                       wtdqr_same_metadata
                         data_length offset minimum maximum writable zone
                         nx1 nx
                       ==>
                       wtdqr_same_metadata
                         data_length offset minimum maximum writable zone
                         r1 r
                       ==>
                       wtdqr_same_metadata
                         data_length offset minimum maximum writable zone
                         q1 q
                       ==>
                       wtdqr_division_result
                         pelts offset sy sx x y q1 r1
                       ==>
                       wtdqr_canonical_freed_pointer
                         data_length offset minimum maximum writable nx1 /\
                       wtdqr_canonical_freed_pointer
                         data_length offset minimum maximum writable ny1 /\
                       wtdqr_division_result
                         pelts offset sy sx x y q1 r1))))))`;;
