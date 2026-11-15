(*
  Statement-only formalization of NTP4VC corpus artifact
  pearl/multiprecision/add_Add_add_ryqtvc: the verification condition for
  adding two multiprecision values of possibly different lengths into the
  second operand, including carry, pointer validity, alias separation,
  memory framing, and preservation of pointer metadata. This file contains
  no proof.
*)

needs "Library/words.ml";;
needs "Library/isum.ml";;

let addry_radix = new_definition
  `addry_radix = (&18446744073709551616:int)`;;

let addry_int32_in_bounds = new_definition
  `addry_int32_in_bounds (z:int) <=>
     --(&2147483648:int) <= z /\ z <= (&2147483647:int)`;;

let addry_plength = new_definition
  `addry_plength (data_length:'p->num) (p:'p) =
     (&(data_length p):int)`;;

let addry_valid = new_definition
  `addry_valid
     (data_length:'p->num)
     (offset:'p->int)
     (minimum:'p->int)
     (maximum:'p->int)
     (p:'p) (size:int) <=>
     addry_int32_in_bounds size /\
     (&0:int) <= size /\
     (&0:int) <= minimum p /\
     minimum p <= offset p /\
     offset p + size <= maximum p /\
     maximum p <= addry_plength data_length p`;;

let addry_radix_power = new_definition
  `addry_radix_power (n:int) =
     addry_radix pow (if n < (&0:int) then 0 else num_of_int n)`;;

let addry_value = new_definition
  `addry_value
     (pelts:'p->int->int64) (offset:'p->int) (p:'p) (size:int) =
     if size <= (&0:int) then (&0:int)
     else
       isum (0..num_of_int size - 1)
         (\k. addry_radix pow k *
              (&(val (pelts p (offset p + &k))):int))`;;

let addry_map_eq_sub = new_definition
  `addry_map_eq_sub
     (pelts:'p->int->int64)
     (left:'p) (right:'p) (lower:int) (upper:int) <=>
     !i:int.
       lower <= i /\ i < upper
       ==> pelts left i = pelts right i`;;

let addry_map_eq_sub_shift = new_definition
  `addry_map_eq_sub_shift
     (pelts:'p->int->int64)
     (left:'p) (right:'p)
     (left_offset:int) (right_offset:int) (size:int) <=>
     !i:int.
       (&0:int) <= i /\ i < size
       ==> pelts left (left_offset + i) =
           pelts right (right_offset + i)`;;

let addry_same_pelts = new_definition
  `addry_same_pelts
     (pelts:'p->int->int64) (left:'p) (right:'p) <=>
     !i:int. pelts left i = pelts right i`;;

let addry_same_data = new_definition
  `addry_same_data
     (data_length:'p->num)
     (pelts:'p->int->int64)
     (left:'p) (right:'p) <=>
     data_length left = data_length right /\
     pelts left = pelts right`;;

let addry_identical = new_definition
  `addry_identical
     (data_length:'p->num)
     (pelts:'p->int->int64)
     (offset:'p->int)
     (minimum:'p->int)
     (maximum:'p->int)
     (zone:'p->'z)
     (left:'p) (right:'p) <=>
     addry_same_data data_length pelts left right /\
     offset left = offset right /\
     minimum left = minimum right /\
     maximum left = maximum right /\
     zone left = zone right`;;

let addry_same_offset_writable_zone = new_definition
  `addry_same_offset_writable_zone
     (offset:'p->int) (writable:'p->bool) (zone:'p->'z)
     (left:'p) (right:'p) <=>
     offset left = offset right /\
     writable left = writable right /\
     zone left = zone right`;;

let addry_same_offset_minimum_writable_zone = new_definition
  `addry_same_offset_minimum_writable_zone
     (offset:'p->int) (minimum:'p->int)
     (writable:'p->bool) (zone:'p->'z)
     (left:'p) (right:'p) <=>
     offset left = offset right /\
     minimum left = minimum right /\
     writable left = writable right /\
     zone left = zone right`;;

let addry_disjoint = new_definition
  `addry_disjoint
     (offset:'p->int) (left:'p) (left_size:int)
     (right:'p) (right_size:int) <=>
     offset left = offset right \/
     offset left + left_size <= offset right \/
     offset right + right_size <= offset left`;;

let addry_nonoverlap = new_definition
  `addry_nonoverlap
     (offset:'p->int) (left:'p) (right:'p) (size:int) <=>
     ((&0:int) <= offset left /\ offset left + size <= offset right) \/
     ((&0:int) <= offset right /\ offset right + size <= offset left)`;;

let addry_open_precondition = new_definition
  `addry_open_precondition
     (data_length:'p->num)
     (pelts:'p->int->int64)
     (offset:'p->int)
     (minimum:'p->int)
     (maximum:'p->int)
     (writable:'p->bool)
     (zone:'p->'z)
     (zx:'m->'z) (zy:'m->'z)
     (mx:'m->int32) (my:'m->int32)
     (lx:'m->int32) (ly:'m->int32)
     (ok:'m->bool)
     (sx:int32) (x:'p) (y:'p) (y1:'p) (x1:'p)
     (nr:'p) (ny:'p) (nx:'p) (m:'m) <=>
     writable nr = T /\
     addry_value pelts offset ny (ival sx) =
       addry_value pelts offset y (ival sx) /\
     addry_value pelts offset nx (ival sx) =
       addry_value pelts offset x (ival sx) /\
     addry_valid data_length offset minimum maximum ny (ival sx) /\
     addry_valid data_length offset minimum maximum nx (ival sx) /\
     addry_identical
       data_length pelts offset minimum maximum zone nr ny /\
     addry_nonoverlap offset ny nx (ival sx) /\
     zx m = zone y1 /\
     zy m = zone x1 /\
     ival (mx m) = maximum y /\
     ival (my m) = maximum x /\
     lx m = sx /\
     ly m = sx /\
     ok m = T /\
     addry_map_eq_sub_shift
       pelts ny y1 (offset ny) (offset y1) (ival sx) /\
     addry_map_eq_sub_shift
       pelts nx x1 (offset nx) (offset x1) (ival sx) /\
     addry_same_pelts pelts y1 y /\
     addry_same_pelts pelts x1 x /\
     addry_plength data_length y1 = addry_plength data_length y /\
     addry_plength data_length x1 = addry_plength data_length x /\
     minimum y1 = minimum y /\
     minimum x1 = minimum x /\
     addry_same_data data_length pelts nr ny /\
     addry_same_data data_length pelts ny nx`;;

let addry_call_precondition = new_definition
  `addry_call_precondition
     (data_length:'p->num)
     (pelts:'p->int->int64)
     (offset:'p->int)
     (minimum:'p->int)
     (maximum:'p->int)
     (writable:'p->bool)
     (sy:int32) (sx:int32)
     (nr:'p) (ny:'p) (nx:'p) <=>
     (&0:int) <= ival sy /\
     ival sy <= ival sx /\
     addry_valid data_length offset minimum maximum nr (ival sx) /\
     addry_valid data_length offset minimum maximum nx (ival sx) /\
     addry_valid data_length offset minimum maximum ny (ival sy) /\
     addry_disjoint offset nr (ival sx) nx (ival sx) /\
     addry_disjoint offset nr (ival sx) ny (ival sy) /\
     addry_same_data data_length pelts nr nx /\
     addry_same_data data_length pelts nx ny /\
     writable nr = T`;;

let addry_rebased_snapshot = new_definition
  `addry_rebased_snapshot
     (data_length:'p->num)
     (pelts:'p->int->int64)
     (offset:'p->int)
     (minimum:'p->int)
     (maximum:'p->int)
     (writable:'p->bool)
     (zone:'p->'z)
     (fresh:'p) (shared:'p) (old:'p) <=>
     addry_same_data data_length pelts fresh shared /\
     data_length shared = data_length old /\
     offset fresh = offset old /\
     minimum fresh = minimum old /\
     maximum fresh = maximum old /\
     writable fresh = writable old /\
     zone fresh = zone old`;;

let addry_snapshot_metadata = new_definition
  `addry_snapshot_metadata
     (data_length:'p->num)
     (offset:'p->int)
     (minimum:'p->int)
     (maximum:'p->int)
     (writable:'p->bool)
     (zone:'p->'z)
     (fresh:'p) (old:'p) <=>
     data_length fresh = data_length old /\
     offset fresh = offset old /\
     minimum fresh = minimum old /\
     maximum fresh = maximum old /\
     writable fresh = writable old /\
     zone fresh = zone old`;;

let addry_wmpn_postcondition = new_definition
  `addry_wmpn_postcondition
     (pelts:'p->int->int64) (offset:'p->int)
     (sy:int32) (sx:int32)
     (nr:'p) (ny:'p) (nx:'p)
     (nr1:'p) (ny1:'p) (nx1:'p) (res:int64) <=>
     addry_value pelts offset nr1 (ival sx) +
       addry_radix_power (ival sx) * (&(val res):int) =
       addry_value pelts offset nx (ival sx) +
       addry_value pelts offset ny (ival sy) /\
     (&0:int) <= (&(val res):int) /\
     (&(val res):int) <= (&1:int) /\
     (!j:int.
        j < offset nr1 \/ offset nr1 + ival sx <= j
        ==> pelts nr1 j = pelts nr j) /\
     (offset nr1 = offset nx1 \/
      addry_map_eq_sub
        pelts nx1 nx (offset nx1) (offset nx1 + ival sx)) /\
     (offset nr1 = offset ny1 \/
      addry_map_eq_sub
        pelts ny1 ny (offset ny1) (offset ny1 + ival sy))`;;

let addry_close_precondition = new_definition
  `addry_close_precondition
     (data_length:'p->num)
     (pelts:'p->int->int64)
     (offset:'p->int)
     (minimum:'p->int)
     (maximum:'p->int)
     (writable:'p->bool)
     (zone:'p->'z)
     (zx:'m->'z) (zy:'m->'z)
     (lx:'m->int32) (ly:'m->int32)
     (ok:'m->bool)
     (sx:int32) (y1:'p) (x1:'p)
     (nr1:'p) (ny1:'p) (nx1:'p) (m:'m) <=>
     writable y1 = T /\
     writable nr1 = T /\
     ok m = T /\
     (&0:int) <= ival sx /\
     ival sx <= ival sx /\
     addry_identical
       data_length pelts offset minimum maximum zone nr1 ny1 /\
     addry_nonoverlap offset ny1 nx1 (ival sx) /\
     zx m = zone y1 /\
     zy m = zone x1 /\
     lx m = sx /\
     ly m = sx`;;

let addry_same_alias_memory = new_definition
  `addry_same_alias_memory
     (zr:'m->'z) (zx:'m->'z) (zy:'m->'z)
     (mr:'m->int32) (mx:'m->int32) (my:'m->int32)
     (lr:'m->int32) (lx:'m->int32) (ly:'m->int32)
     (left:'m) (right:'m) <=>
     zr left = zr right /\
     zx left = zx right /\
     zy left = zy right /\
     mr left = mr right /\
     mx left = mx right /\
     my left = my right /\
     lr left = lr right /\
     lx left = lx right /\
     ly left = ly right`;;

let addry_close_intermediate = new_definition
  `addry_close_intermediate
     (data_length:'p->num)
     (pelts:'p->int->int64)
     (offset:'p->int)
     (minimum:'p->int)
     (maximum:'p->int)
     (mx:'m->int32) (my:'m->int32)
     (sx:int32) (m1:'m)
     (nx1:'p) (ny1:'p) (nx2:'p) (ny2:'p)
     (y1:'p) (x1:'p) (y2:'p) (x2:'p) <=>
     maximum y2 = ival (mx m1) /\
     maximum x2 = ival (my m1) /\
     addry_map_eq_sub_shift
       pelts ny1 y2 (offset ny2) (offset y2) (ival sx) /\
     addry_map_eq_sub_shift
       pelts nx1 x2 (offset nx2) (offset x2) (ival sx) /\
     (!j:int.
        j < offset y2 \/ offset y2 + ival sx <= j
        ==> pelts y2 j = pelts y1 j) /\
     (!j:int.
        j < offset x2 \/ offset x2 + ival sx <= j
        ==> pelts x2 j = pelts x1 j) /\
     addry_plength data_length y2 = addry_plength data_length y1 /\
     addry_plength data_length x2 = addry_plength data_length x1 /\
     minimum y2 = minimum y1 /\
     minimum x2 = minimum x1`;;

let addry_final_postcondition = new_definition
  `addry_final_postcondition
     (data_length:'p->num)
     (pelts:'p->int->int64)
     (offset:'p->int)
     (minimum:'p->int)
     (maximum:'p->int)
     (sy:int32) (sx:int32)
     (x:'p) (y:'p) (x2:'p) (y2:'p) (res:int64) <=>
     addry_value pelts offset y2 (ival sx) +
       addry_radix_power (ival sx) * (&(val res):int) =
       addry_value pelts offset x (ival sx) +
       addry_value pelts offset y (ival sy) /\
     (&0:int) <= (&(val res):int) /\
     (&(val res):int) <= (&1:int) /\
     (!j:int.
        j < offset y2 \/ offset y2 + ival sx <= j
        ==> pelts y2 j = pelts y j) /\
     (!j:int. pelts x2 j = pelts x j) /\
     addry_value pelts offset x2 (ival sx) =
       addry_value pelts offset x (ival sx) /\
     minimum x2 = minimum x /\
     maximum x2 = maximum x /\
     addry_plength data_length x2 = addry_plength data_length x /\
     minimum y2 = minimum y /\
     maximum y2 = maximum y /\
     addry_plength data_length y2 = addry_plength data_length y`;;

let statement =
  `!data_length:'p->num.
   !pelts:'p->int->int64.
   !offset minimum maximum:'p->int.
   !writable:'p->bool.
   !zone:'p->'z.
   !zr zx zy:'m->'z.
   !mr mx my lr lx ly:'m->int32.
   !ok:'m->bool.
   !sy sx:int32. !x y:'p.
     (&0:int) <= ival sy
     ==>
     ival sy <= ival sx
     ==>
     addry_valid data_length offset minimum maximum x (ival sx)
     ==>
     addry_valid data_length offset minimum maximum y (ival sx)
     ==>
     writable y = T
     ==>
     addry_valid data_length offset minimum maximum y (ival sx) /\
     addry_valid data_length offset minimum maximum x (ival sx) /\
     (&0:int) <= ival sx /\
     ival sx <= ival sx /\
     writable y = T /\
     (!y1 x1:'p.
        addry_same_offset_writable_zone offset writable zone y1 y
        ==>
        addry_same_offset_writable_zone offset writable zone x1 x
        ==>
        (!nr ny nx:'p. !m:'m.
           addry_open_precondition
             data_length pelts offset minimum maximum writable zone
             zx zy mx my lx ly ok sx x y y1 x1 nr ny nx m
           ==>
           addry_call_precondition
             data_length pelts offset minimum maximum writable
             sy sx nr ny nx /\
           (!nx1 ny1 nr1:'p.
              addry_rebased_snapshot
                data_length pelts offset minimum maximum writable zone
                nx1 nr1 nx
              ==>
              addry_rebased_snapshot
                data_length pelts offset minimum maximum writable zone
                ny1 nr1 ny
              ==>
              addry_snapshot_metadata
                data_length offset minimum maximum writable zone nr1 nr
              ==>
              (!res:int64.
                 addry_wmpn_postcondition
                   pelts offset sy sx nr ny nx nr1 ny1 nx1 res
                 ==>
                 addry_close_precondition
                   data_length pelts offset minimum maximum writable zone
                   zx zy lx ly ok sx y1 x1 nr1 ny1 nx1 m /\
                 (!m1:'m. !nx2 ny2 y2 x2:'p.
                    addry_same_alias_memory
                      zr zx zy mr mx my lr lx ly m1 m
                    ==>
                    addry_same_offset_writable_zone
                      offset writable zone nx2 nx1
                    ==>
                    addry_same_offset_writable_zone
                      offset writable zone ny2 ny1
                    ==>
                    addry_same_offset_minimum_writable_zone
                      offset minimum writable zone y2 y1
                    ==>
                    addry_same_offset_minimum_writable_zone
                      offset minimum writable zone x2 x1
                    ==>
                    addry_close_intermediate
                      data_length pelts offset minimum maximum mx my sx m1
                      nx1 ny1 nx2 ny2 y1 x1 y2 x2
                    ==>
                    addry_final_postcondition
                      data_length pelts offset minimum maximum
                      sy sx x y x2 y2 res)))))`;;
