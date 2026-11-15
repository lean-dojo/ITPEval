(*
  Statement-only formalization of NTP4VC corpus artifact
  pearl/multiprecision/sub_Sub_sub_rxqtvc: the verification condition for
  alias-aware unequal-length multiprecision subtraction into the first
  operand, including borrow arithmetic, memory framing, validity, and
  preservation of the second operand and pointer metadata. This file
  contains no proof.
*)

let mpsubrxu_statement_output = open_out "/dev/null";;
Format.set_formatter_out_channel mpsubrxu_statement_output;;

let mpsubrxu_radix = new_definition
  `mpsubrxu_radix = (&18446744073709551616:int)`;;

let mpsubrxu_u64 = new_definition
  `mpsubrxu_u64 (x:int) = x`;;

let mpsubrxu_u64_in_bounds = new_definition
  `mpsubrxu_u64_in_bounds (z:int) <=>
     (&0:int) <= z /\ z < mpsubrxu_radix`;;

let mpsubrxu_int32_in_bounds = new_definition
  `mpsubrxu_int32_in_bounds (z:int) <=>
     --(&2147483648:int) <= z /\ z <= (&2147483647:int)`;;

let mpsubrxu_pelts_in_bounds = new_definition
  `mpsubrxu_pelts_in_bounds (pelts:'p->int->int) <=>
     !p:'p. !j:int. mpsubrxu_u64_in_bounds (pelts p j)`;;

let mpsubrxu_int32_function_in_bounds = new_definition
  `mpsubrxu_int32_function_in_bounds (field:'m->int) <=>
     !m:'m. mpsubrxu_int32_in_bounds (field m)`;;

let mpsubrxu_radix_power = new_definition
  `mpsubrxu_radix_power (n:int) =
     mpsubrxu_radix pow (if n < (&0:int) then 0 else num_of_int n)`;;

let mpsubrxu_value = new_definition
  `mpsubrxu_value
     (pelts:'p->int->int) (offset:'p->int) (p:'p) (n:int) =
     if n <= (&0:int) then (&0:int)
     else
       isum (0..num_of_int n - 1)
         (\k. mpsubrxu_radix pow k *
              mpsubrxu_u64 (pelts p (offset p + &k)))`;;

let mpsubrxu_plength = new_definition
  `mpsubrxu_plength (data_length:'p->num) (p:'p) =
     (&(data_length p):int)`;;

let mpsubrxu_valid = new_definition
  `mpsubrxu_valid
     (data_length:'p->num)
     (offset:'p->int)
     (minimum:'p->int)
     (maximum:'p->int)
     (p:'p) (n:int) <=>
     mpsubrxu_int32_in_bounds n /\
     (&0:int) <= n /\
     (&0:int) <= minimum p /\
     minimum p <= offset p /\
     offset p + n <= maximum p /\
     maximum p <= mpsubrxu_plength data_length p`;;

let mpsubrxu_same_pelts = new_definition
  `mpsubrxu_same_pelts
     (pelts:'p->int->int) (left:'p) (right:'p) <=>
     !j:int. pelts left j = pelts right j`;;

let mpsubrxu_same_data = new_definition
  `mpsubrxu_same_data
     (data_length:'p->num)
     (pelts:'p->int->int)
     (left:'p) (right:'p) <=>
     data_length left = data_length right /\
     mpsubrxu_same_pelts pelts left right`;;

let mpsubrxu_identical = new_definition
  `mpsubrxu_identical
     (data_length:'p->num)
     (offset:'p->int)
     (minimum:'p->int)
     (maximum:'p->int)
     (zone:'p->'z)
     (pelts:'p->int->int)
     (left:'p) (right:'p) <=>
     mpsubrxu_same_data data_length pelts left right /\
     offset left = offset right /\
     minimum left = minimum right /\
     maximum left = maximum right /\
     zone left = zone right`;;

let mpsubrxu_map_eq_sub_shift = new_definition
  `mpsubrxu_map_eq_sub_shift
     (pelts:'p->int->int)
     (left:'p) (right:'p)
     (left_start:int) (right_start:int) (size:int) <=>
     !i:int.
       (&0:int) <= i /\ i < size
       ==> pelts left (left_start + i) =
           pelts right (right_start + i)`;;

let mpsubrxu_map_eq_sub = new_definition
  `mpsubrxu_map_eq_sub
     (pelts:'p->int->int)
     (left:'p) (right:'p) (lower:int) (upper:int) <=>
     !i:int.
       lower <= i /\ i < upper
       ==> pelts left i = pelts right i`;;

let mpsubrxu_outside_equal = new_definition
  `mpsubrxu_outside_equal
     (offset:'p->int)
     (pelts:'p->int->int)
     (new:'p) (old:'p) (size:int) <=>
     !j:int.
       j < offset new \/ offset new + size <= j
       ==> pelts new j = pelts old j`;;

let mpsubrxu_separated = new_definition
  `mpsubrxu_separated
     (offset:'p->int)
     (left:'p) (right:'p)
     (left_size:int) (right_size:int) <=>
     ((&0:int) <= offset left /\
      offset left + left_size <= offset right) \/
     ((&0:int) <= offset right /\
      offset right + right_size <= offset left)`;;

let mpsubrxu_result_alias_safe = new_definition
  `mpsubrxu_result_alias_safe
     (offset:'p->int)
     (result:'p) (operand:'p)
     (result_size:int) (operand_size:int) <=>
     offset result = offset operand \/
     offset result + result_size <= offset operand \/
     offset operand + operand_size <= offset result`;;

let mpsubrxu_continuation = new_definition
  `mpsubrxu_continuation
     (data_length:'p->num)
     (offset:'p->int)
     (minimum:'p->int)
     (maximum:'p->int)
     (writable:'p->bool)
     (zone:'p->'z)
     (pelts:'p->int->int)
     (zr:'m->'z)
     (zx:'m->'z)
     (zy:'m->'z)
     (mr:'m->int)
     (mx:'m->int)
     (my:'m->int)
     (lr:'m->int)
     (lx:'m->int)
     (ly:'m->int)
     (ok:'m->bool)
     (sx:int) (sy:int) (x:'p) (y:'p) <=>
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
          (mpsubrxu_value pelts offset nx sx =
             mpsubrxu_value pelts offset x sx /\
           mpsubrxu_value pelts offset ny sy =
             mpsubrxu_value pelts offset y sy) /\
          (mpsubrxu_valid
             data_length offset minimum maximum nx sx /\
           mpsubrxu_valid
             data_length offset minimum maximum ny sy) /\
          mpsubrxu_identical
            data_length offset minimum maximum zone pelts nr nx /\
          mpsubrxu_separated offset nx ny sx sy /\
          (zx m = zone x1 /\ zy m = zone y1) /\
          (mx m = maximum x /\ my m = maximum y) /\
          (lx m = sx /\ ly m = sy) /\
          ok m = T /\
          mpsubrxu_map_eq_sub_shift
            pelts nx x1 (offset nx) (offset x1) sx /\
          mpsubrxu_map_eq_sub_shift
            pelts ny y1 (offset ny) (offset y1) sy /\
          (mpsubrxu_same_pelts pelts x1 x /\
           mpsubrxu_same_pelts pelts y1 y) /\
          (mpsubrxu_plength data_length x1 =
             mpsubrxu_plength data_length x /\
           mpsubrxu_plength data_length y1 =
             mpsubrxu_plength data_length y) /\
          (minimum x1 = minimum x /\ minimum y1 = minimum y) /\
          mpsubrxu_same_data data_length pelts nr nx /\
          mpsubrxu_same_data data_length pelts nx ny
          ==>
          (((&0:int) <= sy /\
            sy <= sx) /\
           (mpsubrxu_valid
              data_length offset minimum maximum nr sx /\
            mpsubrxu_valid
              data_length offset minimum maximum nx sx /\
            mpsubrxu_valid
              data_length offset minimum maximum ny sy) /\
           mpsubrxu_result_alias_safe
             offset nr nx sx sx /\
           mpsubrxu_result_alias_safe
             offset nr ny sx sy /\
           (mpsubrxu_same_data data_length pelts nr nx /\
            mpsubrxu_same_data data_length pelts nx ny) /\
           writable nr = T) /\
          (!ny1:'p. !nx1:'p. !nr1:'p.
             mpsubrxu_same_data data_length pelts ny1 nr1 /\
             data_length nr1 = data_length ny /\
             offset ny1 = offset ny /\
             minimum ny1 = minimum ny /\
             maximum ny1 = maximum ny /\
             writable ny1 = writable ny /\
             zone ny1 = zone ny
             ==>
             mpsubrxu_same_data data_length pelts nx1 nr1 /\
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
             (!res:int.
                mpsubrxu_u64_in_bounds res
                ==>
                mpsubrxu_value pelts offset nr1 sx -
                  mpsubrxu_radix_power sx * mpsubrxu_u64 res =
                  mpsubrxu_value pelts offset nx sx -
                  mpsubrxu_value pelts offset ny sy /\
                ((&0:int) <= mpsubrxu_u64 res /\
                 mpsubrxu_u64 res <= (&1:int)) /\
                mpsubrxu_outside_equal
                  offset pelts nr1 nr sx /\
                (offset nr1 = offset nx1 \/
                 mpsubrxu_map_eq_sub
                   pelts nx1 nx (offset nx1)
                   (offset nx1 + sx)) /\
                (offset nr1 = offset ny1 \/
                 mpsubrxu_map_eq_sub
                   pelts ny1 ny (offset ny1)
                   (offset ny1 + sy))
                ==>
                (((writable x1 = T /\ writable nr1 = T) /\
                  ok m = T /\
                  ((&0:int) <= sy /\
                   sy <= sx) /\
                  mpsubrxu_identical
                    data_length offset minimum maximum zone pelts nr1 nx1 /\
                  mpsubrxu_separated
                    offset nx1 ny1 sx sy /\
                  (zx m = zone x1 /\ zy m = zone y1) /\
                  lx m = sx /\
                  ly m = sy) /\
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
                    (maximum x2 = mx m1 /\
                     maximum y2 = my m1) /\
                    mpsubrxu_map_eq_sub_shift
                      pelts nx1 x2
                      (offset nx2) (offset x2) sx /\
                    mpsubrxu_map_eq_sub_shift
                      pelts ny1 y2
                      (offset ny2) (offset y2) sy /\
                    mpsubrxu_outside_equal
                      offset pelts x2 x1 sx /\
                    mpsubrxu_outside_equal
                      offset pelts y2 y1 sy /\
                    (mpsubrxu_plength data_length x2 =
                       mpsubrxu_plength data_length x1 /\
                     mpsubrxu_plength data_length y2 =
                       mpsubrxu_plength data_length y1) /\
                    minimum x2 = minimum x1 /\
                    minimum y2 = minimum y1
                    ==>
                    mpsubrxu_value pelts offset x2 sx -
                      mpsubrxu_radix_power sx * mpsubrxu_u64 res =
                      mpsubrxu_value pelts offset x sx -
                      mpsubrxu_value pelts offset y sy /\
                    ((&0:int) <= mpsubrxu_u64 res /\
                     mpsubrxu_u64 res <= (&1:int)) /\
                    mpsubrxu_outside_equal
                      offset pelts x2 x sx /\
                    mpsubrxu_same_pelts pelts y2 y /\
                    mpsubrxu_value pelts offset y2 sy =
                      mpsubrxu_value pelts offset y sy /\
                    (minimum x2 = minimum x /\
                     maximum x2 = maximum x /\
                     mpsubrxu_plength data_length x2 =
                       mpsubrxu_plength data_length x) /\
                    minimum y2 = minimum y /\
                    maximum y2 = maximum y /\
                    mpsubrxu_plength data_length y2 =
                      mpsubrxu_plength data_length y)))))`;;

let statement =
  `!data_length:'p->num.
   !offset:'p->int.
   !minimum:'p->int.
   !maximum:'p->int.
   !writable:'p->bool.
   !zone:'p->'z.
   !pelts:'p->int->int.
   !zr:'m->'z.
   !zx:'m->'z.
   !zy:'m->'z.
   !mr:'m->int.
   !mx:'m->int.
   !my:'m->int.
   !lr:'m->int.
   !lx:'m->int.
   !ly:'m->int.
   !ok:'m->bool.
   !sy:int. !sx:int. !x:'p. !y:'p.
     mpsubrxu_pelts_in_bounds pelts
     ==>
     mpsubrxu_int32_function_in_bounds mr
     ==>
     mpsubrxu_int32_function_in_bounds mx
     ==>
     mpsubrxu_int32_function_in_bounds my
     ==>
     mpsubrxu_int32_function_in_bounds lr
     ==>
     mpsubrxu_int32_function_in_bounds lx
     ==>
     mpsubrxu_int32_function_in_bounds ly
     ==>
     mpsubrxu_int32_in_bounds sy
     ==>
     mpsubrxu_int32_in_bounds sx
     ==>
     (&0:int) <= sy
     ==>
     sy <= sx
     ==>
     mpsubrxu_valid
       data_length offset minimum maximum x sx
     ==>
     mpsubrxu_valid
       data_length offset minimum maximum y sy
     ==>
     writable x = T
     ==>
     mpsubrxu_valid
       data_length offset minimum maximum x sx /\
     mpsubrxu_valid
       data_length offset minimum maximum y sy /\
     (&0:int) <= sy /\
     sy <= sx /\
     writable x = T /\
     mpsubrxu_continuation
       data_length offset minimum maximum writable zone pelts
       zr zx zy mr mx my lr lx ly ok sx sy x y`;;
