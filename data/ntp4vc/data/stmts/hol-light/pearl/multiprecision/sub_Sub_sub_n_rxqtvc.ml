(*
  Statement-only formalization of NTP4VC corpus artifact
  pearl/multiprecision/sub_Sub_sub_n_rxqtvc: the verification condition for
  in-place equal-length multiprecision subtraction, including borrow
  arithmetic, pointer aliasing, memory framing, and preservation of pointer
  metadata. This file contains no proof.
*)

let mpsubrx_statement_output = open_out "/dev/null";;
Format.set_formatter_out_channel mpsubrx_statement_output;;

needs "Library/words.ml";;
needs "Library/isum.ml";;

let mpsubrx_radix = new_definition
  `mpsubrx_radix = (&18446744073709551616:int)`;;

let mpsubrx_u64 = new_definition
  `mpsubrx_u64 (x:int64) = (&(val x):int)`;;

let mpsubrx_int32_in_bounds = new_definition
  `mpsubrx_int32_in_bounds (z:int) <=>
     --(&2147483648:int) <= z /\ z <= (&2147483647:int)`;;

let mpsubrx_radix_power = new_definition
  `mpsubrx_radix_power (n:int) =
     mpsubrx_radix pow (if n < (&0:int) then 0 else num_of_int n)`;;

let mpsubrx_value = new_definition
  `mpsubrx_value
     (pelts:'p->int->int64) (offset:'p->int) (p:'p) (n:int) =
     if n <= (&0:int) then (&0:int)
     else
       isum (0..num_of_int n - 1)
         (\k. mpsubrx_radix pow k *
              mpsubrx_u64 (pelts p (offset p + &k)))`;;

let mpsubrx_plength = new_definition
  `mpsubrx_plength (data_length:'p->num) (p:'p) =
     (&(data_length p):int)`;;

let mpsubrx_valid = new_definition
  `mpsubrx_valid
     (data_length:'p->num)
     (offset:'p->int)
     (minimum:'p->int)
     (maximum:'p->int)
     (p:'p) (n:int) <=>
     mpsubrx_int32_in_bounds n /\
     (&0:int) <= n /\
     (&0:int) <= minimum p /\
     minimum p <= offset p /\
     offset p + n <= maximum p /\
     maximum p <= mpsubrx_plength data_length p`;;

let mpsubrx_same_pelts = new_definition
  `mpsubrx_same_pelts
     (pelts:'p->int->int64) (left:'p) (right:'p) <=>
     !j:int. pelts left j = pelts right j`;;

let mpsubrx_same_data = new_definition
  `mpsubrx_same_data
     (data_length:'p->num)
     (pelts:'p->int->int64)
     (left:'p) (right:'p) <=>
     data_length left = data_length right /\
     mpsubrx_same_pelts pelts left right`;;

let mpsubrx_identical = new_definition
  `mpsubrx_identical
     (data_length:'p->num)
     (offset:'p->int)
     (minimum:'p->int)
     (maximum:'p->int)
     (zone:'p->'z)
     (pelts:'p->int->int64)
     (left:'p) (right:'p) <=>
     mpsubrx_same_data data_length pelts left right /\
     offset left = offset right /\
     minimum left = minimum right /\
     maximum left = maximum right /\
     zone left = zone right`;;

let mpsubrx_map_eq_sub_shift = new_definition
  `mpsubrx_map_eq_sub_shift
     (pelts:'p->int->int64)
     (left:'p) (right:'p)
     (left_start:int) (right_start:int) (size:int) <=>
     !i:int.
       (&0:int) <= i /\ i < size
       ==> pelts left (left_start + i) =
           pelts right (right_start + i)`;;

let mpsubrx_map_eq_sub = new_definition
  `mpsubrx_map_eq_sub
     (pelts:'p->int->int64)
     (left:'p) (right:'p) (lower:int) (upper:int) <=>
     !i:int.
       lower <= i /\ i < upper
       ==> pelts left i = pelts right i`;;

let mpsubrx_outside_equal = new_definition
  `mpsubrx_outside_equal
     (offset:'p->int)
     (pelts:'p->int->int64)
     (new:'p) (old:'p) (size:int) <=>
     !j:int.
       j < offset new \/ offset new + size <= j
       ==> pelts new j = pelts old j`;;

let mpsubrx_separated = new_definition
  `mpsubrx_separated
     (offset:'p->int) (left:'p) (right:'p) (size:int) <=>
     ((&0:int) <= offset left /\
      offset left + size <= offset right) \/
     ((&0:int) <= offset right /\
      offset right + size <= offset left)`;;

let mpsubrx_result_alias_safe = new_definition
  `mpsubrx_result_alias_safe
     (offset:'p->int) (result:'p) (operand:'p) (size:int) <=>
     offset result = offset operand \/
     offset result + size <= offset operand \/
     offset operand + size <= offset result`;;

let mpsubrx_continuation = new_definition
  `mpsubrx_continuation
     (data_length:'p->num)
     (offset:'p->int)
     (minimum:'p->int)
     (maximum:'p->int)
     (writable:'p->bool)
     (zone:'p->'z)
     (pelts:'p->int->int64)
     (zr:'m->'z)
     (zx:'m->'z)
     (zy:'m->'z)
     (mr:'m->int32)
     (mx:'m->int32)
     (my:'m->int32)
     (lr:'m->int32)
     (lx:'m->int32)
     (ly:'m->int32)
     (ok:'m->bool)
     (size:int32) (x:'p) (y:'p) <=>
     !y1:'p. !x1:'p.
       offset y1 = offset y /\
       writable y1 = writable y /\
       zone y1 = zone y
       ==>
       offset x1 = offset x /\
       writable x1 = writable x /\
       zone x1 = zone x
       ==>
       (!nr:'p. !nx:'p. !ny:'p. !m:'m.
          writable nr = T /\
          (mpsubrx_value pelts offset nx (ival size) =
             mpsubrx_value pelts offset x (ival size) /\
           mpsubrx_value pelts offset ny (ival size) =
             mpsubrx_value pelts offset y (ival size)) /\
          (mpsubrx_valid
             data_length offset minimum maximum nx (ival size) /\
           mpsubrx_valid
             data_length offset minimum maximum ny (ival size)) /\
          mpsubrx_identical
            data_length offset minimum maximum zone pelts nr nx /\
          mpsubrx_separated offset nx ny (ival size) /\
          (zx m = zone x1 /\ zy m = zone y1) /\
          (ival (mx m) = maximum x /\ ival (my m) = maximum y) /\
          (lx m = size /\ ly m = size) /\
          ok m = T /\
          mpsubrx_map_eq_sub_shift
            pelts nx x1 (offset nx) (offset x1) (ival size) /\
          mpsubrx_map_eq_sub_shift
            pelts ny y1 (offset ny) (offset y1) (ival size) /\
          (mpsubrx_same_pelts pelts x1 x /\
           mpsubrx_same_pelts pelts y1 y) /\
          (mpsubrx_plength data_length x1 =
             mpsubrx_plength data_length x /\
           mpsubrx_plength data_length y1 =
             mpsubrx_plength data_length y) /\
          (minimum x1 = minimum x /\ minimum y1 = minimum y) /\
          mpsubrx_same_data data_length pelts nr nx /\
          mpsubrx_same_data data_length pelts nx ny
          ==>
          (((&0:int) <= ival size /\
            (mpsubrx_valid
               data_length offset minimum maximum nr (ival size) /\
             mpsubrx_valid
               data_length offset minimum maximum nx (ival size) /\
             mpsubrx_valid
               data_length offset minimum maximum ny (ival size)) /\
            mpsubrx_result_alias_safe offset nr nx (ival size) /\
            mpsubrx_result_alias_safe offset nr ny (ival size) /\
            (mpsubrx_same_data data_length pelts nr nx /\
             mpsubrx_same_data data_length pelts nx ny) /\
            writable nr = T) /\
           (!ny1:'p. !nx1:'p. !nr1:'p.
              mpsubrx_same_data data_length pelts ny1 nr1 /\
              data_length nr1 = data_length ny /\
              offset ny1 = offset ny /\
              minimum ny1 = minimum ny /\
              maximum ny1 = maximum ny /\
              writable ny1 = writable ny /\
              zone ny1 = zone ny
              ==>
              mpsubrx_same_data data_length pelts nx1 nr1 /\
              data_length nr1 = data_length nx /\
              offset nx1 = offset nx /\
              minimum nx1 = minimum nx /\
              maximum nx1 = maximum nx /\
              writable nx1 = writable nx /\
              zone nx1 = zone nx
              ==>
              data_length nr1 = data_length nr /\
              offset nr1 = offset nr /\
              minimum nr1 = minimum nr /\
              maximum nr1 = maximum nr /\
              writable nr1 = writable nr /\
              zone nr1 = zone nr
              ==>
              (!res:int64.
                 mpsubrx_value pelts offset nr1 (ival size) -
                   mpsubrx_radix_power (ival size) * mpsubrx_u64 res =
                   mpsubrx_value pelts offset nx (ival size) -
                   mpsubrx_value pelts offset ny (ival size) /\
                 ((&0:int) <= mpsubrx_u64 res /\
                  mpsubrx_u64 res <= (&1:int)) /\
                 mpsubrx_outside_equal
                   offset pelts nr1 nr (ival size) /\
                 (offset nr1 = offset nx1 \/
                  mpsubrx_map_eq_sub
                    pelts nx1 nx (offset nx1)
                    (offset nx1 + ival size)) /\
                 (offset nr1 = offset ny1 \/
                  mpsubrx_map_eq_sub
                    pelts ny1 ny (offset ny1)
                    (offset ny1 + ival size))
                 ==>
                 (((writable x1 = T /\ writable nr1 = T) /\
                   ok m = T /\
                   ((&0:int) <= ival size /\
                    ival size <= ival size) /\
                   mpsubrx_identical
                     data_length offset minimum maximum zone pelts nr1 nx1 /\
                   mpsubrx_separated offset nx1 ny1 (ival size) /\
                   (zx m = zone x1 /\ zy m = zone y1) /\
                   lx m = size /\
                   ly m = size) /\
                  (!m1:'m.
                   !ny2:'p. !nx2:'p. !y2:'p. !x2:'p.
                     zr m1 = zr m /\
                     zx m1 = zx m /\
                     zy m1 = zy m /\
                     mr m1 = mr m /\
                     mx m1 = mx m /\
                     my m1 = my m /\
                     lr m1 = lr m /\
                     lx m1 = lx m /\
                     ly m1 = ly m
                     ==>
                     offset ny2 = offset ny1 /\
                     writable ny2 = writable ny1 /\
                     zone ny2 = zone ny1
                     ==>
                     offset nx2 = offset nx1 /\
                     writable nx2 = writable nx1 /\
                     zone nx2 = zone nx1
                     ==>
                     offset y2 = offset y1 /\
                     minimum y2 = minimum y1 /\
                     writable y2 = writable y1 /\
                     zone y2 = zone y1
                     ==>
                     offset x2 = offset x1 /\
                     minimum x2 = minimum x1 /\
                     writable x2 = writable x1 /\
                     zone x2 = zone x1
                     ==>
                     (maximum x2 = ival (mx m1) /\
                      maximum y2 = ival (my m1)) /\
                     mpsubrx_map_eq_sub_shift
                       pelts nx1 x2
                       (offset nx2) (offset x2) (ival size) /\
                     mpsubrx_map_eq_sub_shift
                       pelts ny1 y2
                       (offset ny2) (offset y2) (ival size) /\
                     mpsubrx_outside_equal
                       offset pelts x2 x1 (ival size) /\
                     mpsubrx_outside_equal
                       offset pelts y2 y1 (ival size) /\
                     (mpsubrx_plength data_length x2 =
                        mpsubrx_plength data_length x1 /\
                      mpsubrx_plength data_length y2 =
                        mpsubrx_plength data_length y1) /\
                     minimum x2 = minimum x1 /\
                     minimum y2 = minimum y1
                     ==>
                     mpsubrx_value pelts offset x2 (ival size) -
                       mpsubrx_radix_power (ival size) * mpsubrx_u64 res =
                       mpsubrx_value pelts offset x (ival size) -
                       mpsubrx_value pelts offset y (ival size) /\
                     ((&0:int) <= mpsubrx_u64 res /\
                      mpsubrx_u64 res <= (&1:int)) /\
                     mpsubrx_outside_equal
                       offset pelts x2 x (ival size) /\
                     mpsubrx_same_pelts pelts y2 y /\
                     mpsubrx_value pelts offset y2 (ival size) =
                       mpsubrx_value pelts offset y (ival size) /\
                     (minimum x2 = minimum x /\
                      maximum x2 = maximum x /\
                      mpsubrx_plength data_length x2 =
                        mpsubrx_plength data_length x) /\
                     minimum y2 = minimum y /\
                     maximum y2 = maximum y /\
                     mpsubrx_plength data_length y2 =
                       mpsubrx_plength data_length y))))))`;;

let statement =
  `!data_length:'p->num.
   !offset:'p->int.
   !minimum:'p->int.
   !maximum:'p->int.
   !writable:'p->bool.
   !zone:'p->'z.
   !pelts:'p->int->int64.
   !zr:'m->'z.
   !zx:'m->'z.
   !zy:'m->'z.
   !mr:'m->int32.
   !mx:'m->int32.
   !my:'m->int32.
   !lr:'m->int32.
   !lx:'m->int32.
   !ly:'m->int32.
   !ok:'m->bool.
   !size:int32. !x:'p. !y:'p.
     (&0:int) <= ival size
     ==>
     mpsubrx_valid
       data_length offset minimum maximum x (ival size)
     ==>
     mpsubrx_valid
       data_length offset minimum maximum y (ival size)
     ==>
     writable x = T
     ==>
     mpsubrx_valid
       data_length offset minimum maximum x (ival size) /\
     mpsubrx_valid
       data_length offset minimum maximum y (ival size) /\
     (&0:int) <= ival size /\
     ival size <= ival size /\
     writable x = T /\
     mpsubrx_continuation
       data_length offset minimum maximum writable zone pelts
       zr zx zy mr mx my lr lx ly ok size x y`;;
