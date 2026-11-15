(*
  Statement-only formalization of NTP4VC corpus artifact
  pearl/multiprecision/sub_Sub_sub_nqtvc: the verification condition for
  equal-length multiprecision subtraction into a separate result pointer,
  including borrow arithmetic, pointer aliasing, memory framing, and
  preservation of pointer metadata. This file contains no proof.
*)

let mpsubn_statement_output = open_out "/dev/null";;
Format.set_formatter_out_channel mpsubn_statement_output;;

needs "Library/words.ml";;
needs "Library/isum.ml";;

let mpsubn_radix = new_definition
  `mpsubn_radix = (&18446744073709551616:int)`;;

let mpsubn_u64 = new_definition
  `mpsubn_u64 (x:int64) = (&(val x):int)`;;

let mpsubn_int32_in_bounds = new_definition
  `mpsubn_int32_in_bounds (z:int) <=>
     --(&2147483648:int) <= z /\ z <= (&2147483647:int)`;;

let mpsubn_radix_power = new_definition
  `mpsubn_radix_power (n:int) =
     mpsubn_radix pow (if n < (&0:int) then 0 else num_of_int n)`;;

let mpsubn_value = new_definition
  `mpsubn_value
     (pelts:'p->int->int64) (offset:'p->int) (p:'p) (n:int) =
     if n <= (&0:int) then (&0:int)
     else
       isum (0..num_of_int n - 1)
         (\k. mpsubn_radix pow k *
              mpsubn_u64 (pelts p (offset p + &k)))`;;

let mpsubn_plength = new_definition
  `mpsubn_plength (data_length:'p->num) (p:'p) =
     (&(data_length p):int)`;;

let mpsubn_valid = new_definition
  `mpsubn_valid
     (data_length:'p->num)
     (offset:'p->int)
     (minimum:'p->int)
     (maximum:'p->int)
     (p:'p) (n:int) <=>
     mpsubn_int32_in_bounds n /\
     (&0:int) <= n /\
     (&0:int) <= minimum p /\
     minimum p <= offset p /\
     offset p + n <= maximum p /\
     maximum p <= mpsubn_plength data_length p`;;

let mpsubn_same_pelts = new_definition
  `mpsubn_same_pelts
     (pelts:'p->int->int64) (left:'p) (right:'p) <=>
     !j:int. pelts left j = pelts right j`;;

let mpsubn_same_data = new_definition
  `mpsubn_same_data
     (data_length:'p->num)
     (pelts:'p->int->int64)
     (left:'p) (right:'p) <=>
     data_length left = data_length right /\
     mpsubn_same_pelts pelts left right`;;

let mpsubn_map_eq_sub_shift = new_definition
  `mpsubn_map_eq_sub_shift
     (pelts:'p->int->int64)
     (left:'p) (right:'p)
     (left_start:int) (right_start:int) (size:int) <=>
     !i:int.
       (&0:int) <= i /\ i < size
       ==> pelts left (left_start + i) =
           pelts right (right_start + i)`;;

let mpsubn_map_eq_sub = new_definition
  `mpsubn_map_eq_sub
     (pelts:'p->int->int64)
     (left:'p) (right:'p)
     (lower:int) (upper:int) <=>
     !i:int.
       lower <= i /\ i < upper
       ==> pelts left i = pelts right i`;;

let mpsubn_outside_equal = new_definition
  `mpsubn_outside_equal
     (offset:'p->int)
     (pelts:'p->int->int64)
     (newp:'p) (oldp:'p) (size:int) <=>
     !j:int.
       j < offset newp \/ offset newp + size <= j
       ==> pelts newp j = pelts oldp j`;;

let mpsubn_result_alias_safe = new_definition
  `mpsubn_result_alias_safe
     (offset:'p->int) (result:'p) (operand:'p) (size:int) <=>
     offset result = offset operand \/
     offset result + size <= offset operand \/
     offset operand + size <= offset result`;;

let mpsubn_view = new_definition
  `mpsubn_view
     (offset:'p->int)
     (writable:'p->bool)
     (zone:'p->'z)
     (current:'p) (oldp:'p) <=>
     offset current = offset oldp /\
     writable current = writable oldp /\
     zone current = zone oldp`;;

let mpsubn_view_with_minimum = new_definition
  `mpsubn_view_with_minimum
     (offset:'p->int)
     (minimum:'p->int)
     (writable:'p->bool)
     (zone:'p->'z)
     (current:'p) (oldp:'p) <=>
     offset current = offset oldp /\
     minimum current = minimum oldp /\
     writable current = writable oldp /\
     zone current = zone oldp`;;

let mpsubn_memory_view = new_definition
  `mpsubn_memory_view
     (zr:'m->'z) (zx:'m->'z) (zy:'m->'z)
     (mr:'m->int32) (mx:'m->int32) (my:'m->int32)
     (lr:'m->int32) (lx:'m->int32) (ly:'m->int32)
     (current:'m) (oldm:'m) <=>
     zr current = zr oldm /\
     zx current = zx oldm /\
     zy current = zy oldm /\
     mr current = mr oldm /\
     mx current = mx oldm /\
     my current = my oldm /\
     lr current = lr oldm /\
     lx current = lx oldm /\
     ly current = ly oldm`;;

let mpsubn_open_hypothesis = new_definition
  `mpsubn_open_hypothesis
     (data_length:'p->num)
     (offset:'p->int)
     (minimum:'p->int)
     (maximum:'p->int)
     (writable:'p->bool)
     (zone:'p->'z)
     (pelts:'p->int->int64)
     (zr:'m->'z) (zx:'m->'z) (zy:'m->'z)
     (mr:'m->int32) (mx:'m->int32) (my:'m->int32)
     (lr:'m->int32) (lx:'m->int32) (ly:'m->int32)
     (ok:'m->bool)
     (size:int32)
     (r:'p) (x:'p) (y:'p)
     (r1:'p) (x1:'p) (y1:'p)
     (nr:'p) (nx:'p) (ny:'p)
     (m:'m) <=>
     writable nr = T /\
     (mpsubn_value pelts offset nx (ival size) =
        mpsubn_value pelts offset x (ival size) /\
      mpsubn_value pelts offset ny (ival size) =
        mpsubn_value pelts offset y (ival size)) /\
     (mpsubn_valid
        data_length offset minimum maximum nr (ival size) /\
      mpsubn_valid
        data_length offset minimum maximum nx (ival size) /\
      mpsubn_valid
        data_length offset minimum maximum ny (ival size)) /\
     ((&0:int) <= offset nr /\
      offset nr + ival size <= offset nx /\
      offset nx + ival size <= offset ny) /\
     (zr m = zone r1 /\ zx m = zone x1 /\ zy m = zone y1) /\
     (ival (mr m) = maximum r /\
      ival (mx m) = maximum x /\
      ival (my m) = maximum y) /\
     (lr m = size /\ lx m = size /\ ly m = size) /\
     ok m = T /\
     mpsubn_map_eq_sub_shift
       pelts nr r1 (offset nr) (offset r1) (ival size) /\
     mpsubn_map_eq_sub_shift
       pelts nx x1 (offset nx) (offset x1) (ival size) /\
     mpsubn_map_eq_sub_shift
       pelts ny y1 (offset ny) (offset y1) (ival size) /\
     (mpsubn_same_pelts pelts r1 r /\
      mpsubn_same_pelts pelts x1 x /\
      mpsubn_same_pelts pelts y1 y) /\
     (mpsubn_plength data_length r1 =
        mpsubn_plength data_length r /\
      mpsubn_plength data_length x1 =
        mpsubn_plength data_length x /\
      mpsubn_plength data_length y1 =
        mpsubn_plength data_length y) /\
     (minimum r1 = minimum r /\
      minimum x1 = minimum x /\
      minimum y1 = minimum y) /\
     mpsubn_same_data data_length pelts nr nx /\
     mpsubn_same_data data_length pelts nx ny`;;

let mpsubn_wmpn_precondition = new_definition
  `mpsubn_wmpn_precondition
     (data_length:'p->num)
     (offset:'p->int)
     (minimum:'p->int)
     (maximum:'p->int)
     (writable:'p->bool)
     (pelts:'p->int->int64)
     (size:int32)
     (nr:'p) (nx:'p) (ny:'p) <=>
     (&0:int) <= ival size /\
     (mpsubn_valid
        data_length offset minimum maximum nr (ival size) /\
      mpsubn_valid
        data_length offset minimum maximum nx (ival size) /\
      mpsubn_valid
        data_length offset minimum maximum ny (ival size)) /\
     mpsubn_result_alias_safe offset nr nx (ival size) /\
     mpsubn_result_alias_safe offset nr ny (ival size) /\
     (mpsubn_same_data data_length pelts nr nx /\
      mpsubn_same_data data_length pelts nx ny) /\
     writable nr = T`;;

let mpsubn_ny_snapshot = new_definition
  `mpsubn_ny_snapshot
     (data_length:'p->num)
     (offset:'p->int)
     (minimum:'p->int)
     (maximum:'p->int)
     (writable:'p->bool)
     (zone:'p->'z)
     (pelts:'p->int->int64)
     (ny1:'p) (nr1:'p) (ny:'p) <=>
     mpsubn_same_data data_length pelts ny1 nr1 /\
     data_length nr1 = data_length ny /\
     offset ny1 = offset ny /\
     minimum ny1 = minimum ny /\
     maximum ny1 = maximum ny /\
     writable ny1 = writable ny /\
     zone ny1 = zone ny`;;

let mpsubn_nx_snapshot = new_definition
  `mpsubn_nx_snapshot
     (data_length:'p->num)
     (offset:'p->int)
     (minimum:'p->int)
     (maximum:'p->int)
     (writable:'p->bool)
     (zone:'p->'z)
     (pelts:'p->int->int64)
     (nx1:'p) (nr1:'p) (nx:'p) <=>
     mpsubn_same_data data_length pelts nx1 nr1 /\
     data_length nr1 = data_length nx /\
     offset nx1 = offset nx /\
     minimum nx1 = minimum nx /\
     maximum nx1 = maximum nx /\
     writable nx1 = writable nx /\
     zone nx1 = zone nx`;;

let mpsubn_nr_snapshot = new_definition
  `mpsubn_nr_snapshot
     (data_length:'p->num)
     (offset:'p->int)
     (minimum:'p->int)
     (maximum:'p->int)
     (writable:'p->bool)
     (zone:'p->'z)
     (nr1:'p) (nr:'p) <=>
     data_length nr1 = data_length nr /\
     offset nr1 = offset nr /\
     minimum nr1 = minimum nr /\
     maximum nr1 = maximum nr /\
     writable nr1 = writable nr /\
     zone nr1 = zone nr`;;

let mpsubn_call_postcondition = new_definition
  `mpsubn_call_postcondition
     (offset:'p->int)
     (pelts:'p->int->int64)
     (size:int32)
     (nr:'p) (nx:'p) (ny:'p)
     (nr1:'p) (nx1:'p) (ny1:'p)
     (res:int64) <=>
     mpsubn_value pelts offset nr1 (ival size) -
       mpsubn_radix_power (ival size) * mpsubn_u64 res =
       mpsubn_value pelts offset nx (ival size) -
       mpsubn_value pelts offset ny (ival size) /\
     ((&0:int) <= mpsubn_u64 res /\ mpsubn_u64 res <= (&1:int)) /\
     mpsubn_outside_equal offset pelts nr1 nr (ival size) /\
     (offset nr1 = offset nx1 \/
      mpsubn_map_eq_sub
        pelts nx1 nx (offset nx1) (offset nx1 + ival size)) /\
     (offset nr1 = offset ny1 \/
      mpsubn_map_eq_sub
        pelts ny1 ny (offset ny1) (offset ny1 + ival size))`;;

let mpsubn_close_precondition = new_definition
  `mpsubn_close_precondition
     (offset:'p->int)
     (writable:'p->bool)
     (zone:'p->'z)
     (zr:'m->'z) (zx:'m->'z) (zy:'m->'z)
     (lr:'m->int32) (lx:'m->int32) (ly:'m->int32)
     (ok:'m->bool)
     (size:int32)
     (r1:'p) (x1:'p) (y1:'p)
     (nr1:'p) (nx1:'p) (ny1:'p)
     (m:'m) <=>
     ok m = T /\
     ((&0:int) <= ival size /\ ival size <= ival size) /\
     (zr m = zone r1 /\ zx m = zone x1 /\ zy m = zone y1) /\
     (lr m = size /\ lx m = size /\ ly m = size) /\
     ((&0:int) <= offset nr1 /\
      offset nr1 + ival size <= offset nx1 /\
      offset nx1 + ival size <= offset ny1) /\
     writable r1 = T /\
     writable nr1 = T`;;

let mpsubn_final_transition = new_definition
  `mpsubn_final_transition
     (data_length:'p->num)
     (offset:'p->int)
     (minimum:'p->int)
     (maximum:'p->int)
     (pelts:'p->int->int64)
     (mr:'m->int32) (mx:'m->int32) (my:'m->int32)
     (size:int32) (m1:'m)
     (r1:'p) (x1:'p) (y1:'p)
     (nr1:'p) (nx1:'p) (ny1:'p)
     (nr2:'p) (nx2:'p) (ny2:'p)
     (r2:'p) (x2:'p) (y2:'p) <=>
     (maximum r2 = ival (mr m1) /\
      maximum x2 = ival (mx m1) /\
      maximum y2 = ival (my m1)) /\
     mpsubn_map_eq_sub_shift
       pelts nr1 r2 (offset nr2) (offset r2) (ival size) /\
     mpsubn_map_eq_sub_shift
       pelts nx1 x2 (offset nx2) (offset x2) (ival size) /\
     mpsubn_map_eq_sub_shift
       pelts ny1 y2 (offset ny2) (offset y2) (ival size) /\
     mpsubn_outside_equal offset pelts r2 r1 (ival size) /\
     mpsubn_outside_equal offset pelts x2 x1 (ival size) /\
     mpsubn_outside_equal offset pelts y2 y1 (ival size) /\
     (mpsubn_plength data_length r2 =
        mpsubn_plength data_length r1 /\
      mpsubn_plength data_length x2 =
        mpsubn_plength data_length x1 /\
      mpsubn_plength data_length y2 =
        mpsubn_plength data_length y1) /\
     minimum r2 = minimum r1 /\
     minimum x2 = minimum x1 /\
     minimum y2 = minimum y1`;;

let mpsubn_final_postcondition = new_definition
  `mpsubn_final_postcondition
     (data_length:'p->num)
     (offset:'p->int)
     (minimum:'p->int)
     (maximum:'p->int)
     (pelts:'p->int->int64)
     (size:int32)
     (r:'p) (x:'p) (y:'p)
     (res:int64)
     (r2:'p) (x2:'p) (y2:'p) <=>
     mpsubn_value pelts offset r2 (ival size) -
       mpsubn_radix_power (ival size) * mpsubn_u64 res =
       mpsubn_value pelts offset x (ival size) -
       mpsubn_value pelts offset y (ival size) /\
     ((&0:int) <= mpsubn_u64 res /\ mpsubn_u64 res <= (&1:int)) /\
     mpsubn_outside_equal offset pelts r2 r (ival size) /\
     mpsubn_same_pelts pelts x2 x /\
     mpsubn_same_pelts pelts y2 y /\
     mpsubn_value pelts offset x2 (ival size) =
       mpsubn_value pelts offset x (ival size) /\
     mpsubn_value pelts offset y2 (ival size) =
       mpsubn_value pelts offset y (ival size) /\
     (minimum x2 = minimum x /\
      maximum x2 = maximum x /\
      mpsubn_plength data_length x2 =
        mpsubn_plength data_length x) /\
     (minimum y2 = minimum y /\
      maximum y2 = maximum y /\
      mpsubn_plength data_length y2 =
        mpsubn_plength data_length y) /\
     minimum r2 = minimum r /\
     maximum r2 = maximum r /\
     mpsubn_plength data_length r2 = mpsubn_plength data_length r`;;

let mpsubn_continuation = new_definition
  `mpsubn_continuation
     (data_length:'p->num)
     (offset:'p->int)
     (minimum:'p->int)
     (maximum:'p->int)
     (writable:'p->bool)
     (zone:'p->'z)
     (pelts:'p->int->int64)
     (zr:'m->'z) (zx:'m->'z) (zy:'m->'z)
     (mr:'m->int32) (mx:'m->int32) (my:'m->int32)
     (lr:'m->int32) (lx:'m->int32) (ly:'m->int32)
     (ok:'m->bool)
     (size:int32)
     (r:'p) (x:'p) (y:'p) <=>
     !y1:'p. !x1:'p. !r1:'p.
       mpsubn_view offset writable zone y1 y
       ==>
       mpsubn_view offset writable zone x1 x
       ==>
       mpsubn_view offset writable zone r1 r
       ==>
       (!nr:'p. !nx:'p. !ny:'p. !m:'m.
          mpsubn_open_hypothesis
            data_length offset minimum maximum writable zone pelts
            zr zx zy mr mx my lr lx ly ok
            size r x y r1 x1 y1 nr nx ny m
          ==>
          mpsubn_wmpn_precondition
            data_length offset minimum maximum writable pelts
            size nr nx ny /\
          (!ny1:'p. !nx1:'p. !nr1:'p.
             mpsubn_ny_snapshot
               data_length offset minimum maximum writable zone pelts
               ny1 nr1 ny
             ==>
             mpsubn_nx_snapshot
               data_length offset minimum maximum writable zone pelts
               nx1 nr1 nx
             ==>
             mpsubn_nr_snapshot
               data_length offset minimum maximum writable zone
               nr1 nr
             ==>
             (!res:int64.
                mpsubn_call_postcondition
                  offset pelts size nr nx ny nr1 nx1 ny1 res
                ==>
                mpsubn_close_precondition
                  offset writable zone zr zx zy lr lx ly ok
                  size r1 x1 y1 nr1 nx1 ny1 m /\
                (!m1:'m.
                 !ny2:'p. !nx2:'p. !nr2:'p.
                 !y2:'p. !x2:'p. !r2:'p.
                   mpsubn_memory_view
                     zr zx zy mr mx my lr lx ly m1 m
                   ==>
                   mpsubn_view offset writable zone ny2 ny1
                   ==>
                   mpsubn_view offset writable zone nx2 nx1
                   ==>
                   mpsubn_view offset writable zone nr2 nr1
                   ==>
                   mpsubn_view_with_minimum
                     offset minimum writable zone y2 y1
                   ==>
                   mpsubn_view_with_minimum
                     offset minimum writable zone x2 x1
                   ==>
                   mpsubn_view_with_minimum
                     offset minimum writable zone r2 r1
                   ==>
                   mpsubn_final_transition
                     data_length offset minimum maximum pelts
                     mr mx my size m1
                     r1 x1 y1 nr1 nx1 ny1
                     nr2 nx2 ny2 r2 x2 y2
                   ==>
                   mpsubn_final_postcondition
                     data_length offset minimum maximum pelts
                     size r x y res r2 x2 y2))))`;;

let statement =
  `!data_length:'p->num.
   !offset:'p->int.
   !minimum:'p->int.
   !maximum:'p->int.
   !writable:'p->bool.
   !zone:'p->'z.
   !pelts:'p->int->int64.
   !zr:'m->'z. !zx:'m->'z. !zy:'m->'z.
   !mr:'m->int32. !mx:'m->int32. !my:'m->int32.
   !lr:'m->int32. !lx:'m->int32. !ly:'m->int32.
   !ok:'m->bool.
   !size:int32.
   !r:'p. !x:'p. !y:'p.
     (&0:int) <= ival size
     ==>
     mpsubn_valid
       data_length offset minimum maximum r (ival size)
     ==>
     mpsubn_valid
       data_length offset minimum maximum x (ival size)
     ==>
     mpsubn_valid
       data_length offset minimum maximum y (ival size)
     ==>
     writable r = T
     ==>
     mpsubn_valid
       data_length offset minimum maximum r (ival size) /\
     mpsubn_valid
       data_length offset minimum maximum x (ival size) /\
     mpsubn_valid
       data_length offset minimum maximum y (ival size) /\
     writable r = T /\
     (&0:int) <= ival size /\
     ival size <= ival size /\
     mpsubn_continuation
       data_length offset minimum maximum writable zone pelts
       zr zx zy mr mx my lr lx ly ok size r x y`;;
