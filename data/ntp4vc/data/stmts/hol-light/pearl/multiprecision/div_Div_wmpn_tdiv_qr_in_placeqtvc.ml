(*
  Statement-only formalization of NTP4VC corpus artifact
  pearl/multiprecision/div_Div_wmpn_tdiv_qr_in_placeqtvc: the verification
  condition for in-place multiprecision division, including scratch-pointer
  allocation, pointer frame conditions, and the quotient-remainder value
  relation. This file contains no proof.
*)

let wtdqip_output = open_out "/dev/null";;
Format.pp_set_formatter_out_channel Format.std_formatter wtdqip_output;;

needs "Library/words.ml";;
needs "Library/isum.ml";;

let wtdqip_radix = new_definition
  `wtdqip_radix = (&18446744073709551616:int)`;;

let wtdqip_u32 = new_definition
  `wtdqip_u32 (x:int32) = (&(val x):int)`;;

let wtdqip_u64 = new_definition
  `wtdqip_u64 (x:int64) = (&(val x):int)`;;

let wtdqip_int32_in_bounds = new_definition
  `wtdqip_int32_in_bounds (z:int) <=>
     --(&2147483648:int) <= z /\ z <= (&2147483647:int)`;;

let wtdqip_uint32_in_bounds = new_definition
  `wtdqip_uint32_in_bounds (z:int) <=>
     (&0:int) <= z /\ z <= (&4294967295:int)`;;

let wtdqip_plength = new_definition
  `wtdqip_plength (data_length:'p->num) (p:'p) =
     (&(data_length p):int)`;;

let wtdqip_valid = new_definition
  `wtdqip_valid
     (data_length:'p->num)
     (offset:'p->int)
     (minimum:'p->int)
     (maximum:'p->int)
     (p:'p) (size:int) <=>
     wtdqip_int32_in_bounds size /\
     (&0:int) <= size /\
     (&0:int) <= minimum p /\
     minimum p <= offset p /\
     offset p + size <= maximum p /\
     maximum p <= wtdqip_plength data_length p`;;

let wtdqip_value = new_definition
  `wtdqip_value
     (pelts:'p->int->int64)
     (offset:'p->int)
     (p:'p) (size:int) =
     if size <= (&0:int) then (&0:int)
     else
       isum (0..num_of_int size - 1)
         (\k. wtdqip_radix pow k *
              wtdqip_u64 (pelts p (offset p + &k)))`;;

let wtdqip_allocation_description = new_definition
  `wtdqip_allocation_description
     (data_length:'p->num)
     (offset:'p->int)
     (minimum:'p->int)
     (maximum:'p->int)
     (writable:'p->bool)
     (zone:'p->'z)
     (null_zone:'z)
     (p:'p) (size:int) <=>
     (~(zone p = null_zone)
      ==> wtdqip_plength data_length p = size) /\
     offset p = (&0:int) /\
     minimum p = (&0:int) /\
     maximum p = wtdqip_plength data_length p /\
     writable p = T`;;

let wtdqip_same_metadata = new_definition
  `wtdqip_same_metadata
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

let wtdqip_canonical_freed_pointer = new_definition
  `wtdqip_canonical_freed_pointer
     (data_length:'p->num)
     (offset:'p->int)
     (minimum:'p->int)
     (maximum:'p->int)
     (writable:'p->bool)
     (p:'p) <=>
     offset p = (&0:int) /\
     minimum p = (&0:int) /\
     maximum p = wtdqip_plength data_length p /\
     writable p = T`;;

let wtdqip_division_result = new_definition
  `wtdqip_division_result
     (pelts:'p->int->int64)
     (offset:'p->int)
     (sy:int32) (sx:int32)
     (x:'p) (y:'p) (q1:'p) (x1:'p) <=>
     wtdqip_value pelts offset x (ival sx) =
       wtdqip_value pelts offset q1
         (ival sx - ival sy + (&1:int)) *
       wtdqip_value pelts offset y (ival sy) +
       wtdqip_value pelts offset x1 (ival sy) /\
     wtdqip_value pelts offset x1 (ival sy) <
       wtdqip_value pelts offset y (ival sy)`;;

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
   !x:'p. !y:'p. !q:'p. !qxn:int32.
     (&1:int) <= ival sy /\
     ival sy <= ival sx /\
     ival sx <= (&2147483647:int) - (&1:int) /\
     wtdqip_valid data_length offset minimum maximum x (ival sx) /\
     wtdqip_valid data_length offset minimum maximum y (ival sy) /\
     wtdqip_valid data_length offset minimum maximum q
       (ival sx - ival sy + (&1:int)) /\
     writable x = T /\
     writable q = T /\
     ival qxn = (&0:int) /\
     (&0:int) <
       wtdqip_u64 (pelts y (offset y + ival sy - (&1:int)))
     ==>
     (&0:int) <= ival sx /\
     (!o1:int32.
        wtdqip_u32 o1 = ival sx
        ==>
        wtdqip_uint32_in_bounds (wtdqip_u32 o1 + (&1:int)) /\
        (!o2:int32.
           wtdqip_u32 o2 = wtdqip_u32 o1 + (&1:int)
           ==>
           (&0:int) <= wtdqip_u32 o2 /\
           (!nx:'p.
              wtdqip_allocation_description
                data_length offset minimum maximum writable zone null_zone
                nx (wtdqip_u32 o2)
              ==>
              is_not_null nx = ~(zone nx = null_zone)
              ==>
              is_not_null nx
              ==>
              (&0:int) <= ival sy /\
              (!o3:int32.
                 wtdqip_u32 o3 = ival sy
                 ==>
                 (&0:int) <= wtdqip_u32 o3 /\
                 (!ny:'p.
                    wtdqip_allocation_description
                      data_length offset minimum maximum writable zone
                      null_zone ny (wtdqip_u32 o3)
                    ==>
                    is_not_null ny = ~(zone ny = null_zone)
                    ==>
                    is_not_null ny
                    ==>
                    (((&1:int) <= ival sy /\
                       ival sy <= ival sx /\
                       ival sx <= (&2147483647:int) - (&1:int)) /\
                      wtdqip_valid
                        data_length offset minimum maximum x (ival sx) /\
                      wtdqip_valid
                        data_length offset minimum maximum y (ival sy) /\
                      wtdqip_valid
                        data_length offset minimum maximum q
                        (ival sx - ival sy + (&1:int)) /\
                      wtdqip_valid
                        data_length offset minimum maximum nx
                        (ival sx + (&1:int)) /\
                      wtdqip_valid
                        data_length offset minimum maximum ny (ival sy) /\
                      (writable q = T /\ writable x = T) /\
                      (writable nx = T /\ writable ny = T) /\
                      (&0:int) <
                        wtdqip_u64
                          (pelts y
                            (offset y + ival sy - (&1:int)))) /\
                    (!ny1 nx1 x1 q1:'p.
                       wtdqip_same_metadata
                         data_length offset minimum maximum writable zone
                         ny1 ny
                       ==>
                       wtdqip_same_metadata
                         data_length offset minimum maximum writable zone
                         nx1 nx
                       ==>
                       wtdqip_same_metadata
                         data_length offset minimum maximum writable zone
                         x1 x
                       ==>
                       wtdqip_same_metadata
                         data_length offset minimum maximum writable zone
                         q1 q
                       ==>
                       wtdqip_division_result
                         pelts offset sy sx x y q1 x1
                       ==>
                       wtdqip_canonical_freed_pointer
                         data_length offset minimum maximum writable nx1 /\
                       wtdqip_canonical_freed_pointer
                         data_length offset minimum maximum writable ny1 /\
                       wtdqip_division_result
                         pelts offset sy sx x y q1 x1))))))`;;
