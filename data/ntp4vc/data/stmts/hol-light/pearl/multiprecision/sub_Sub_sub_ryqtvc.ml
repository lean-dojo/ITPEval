(*
  Statement-only formalization of NTP4VC corpus artifact
  pearl/multiprecision/sub_Sub_sub_ryqtvc: the verification condition for
  possibly unequal-length multiprecision subtraction into the second operand,
  including borrow arithmetic, pointer aliasing, memory framing, and
  preservation of pointer metadata. This file contains no proof.
*)

let mpsubryv_statement_output = open_out "/dev/null";;
Format.set_formatter_out_channel mpsubryv_statement_output;;

needs "Library/words.ml";;
needs "Library/isum.ml";;

let mpsubryv_radix = new_definition
  `mpsubryv_radix = (&18446744073709551616:int)`;;

let mpsubryv_u64 = new_definition
  `mpsubryv_u64 (x:int64) = (&(val x):int)`;;

let mpsubryv_int32_in_bounds = new_definition
  `mpsubryv_int32_in_bounds (z:int) <=>
     --(&2147483648:int) <= z /\ z <= (&2147483647:int)`;;

let mpsubryv_radix_power = new_definition
  `mpsubryv_radix_power (n:int) =
     mpsubryv_radix pow (if n < (&0:int) then 0 else num_of_int n)`;;

let mpsubryv_value = new_definition
  `mpsubryv_value
     (pelts:'p->int->int64) (offset:'p->int) (p:'p) (n:int) =
     if n <= (&0:int) then (&0:int)
     else
       isum (0..num_of_int n - 1)
         (\k. mpsubryv_radix pow k *
              mpsubryv_u64 (pelts p (offset p + &k)))`;;

let mpsubryv_plength = new_definition
  `mpsubryv_plength (data_length:'p->num) (p:'p) =
     (&(data_length p):int)`;;

let mpsubryv_valid = new_definition
  `mpsubryv_valid
     (data_length:'p->num)
     (offset:'p->int)
     (minimum:'p->int)
     (maximum:'p->int)
     (p:'p) (n:int) <=>
     mpsubryv_int32_in_bounds n /\
     (&0:int) <= n /\
     (&0:int) <= minimum p /\
     minimum p <= offset p /\
     offset p + n <= maximum p /\
     maximum p <= mpsubryv_plength data_length p`;;

let mpsubryv_same_pelts = new_definition
  `mpsubryv_same_pelts
     (pelts:'p->int->int64) (left:'p) (right:'p) <=>
     !j:int. pelts left j = pelts right j`;;

let mpsubryv_same_data = new_definition
  `mpsubryv_same_data
     (data_length:'p->num)
     (pelts:'p->int->int64)
     (left:'p) (right:'p) <=>
     data_length left = data_length right /\
     mpsubryv_same_pelts pelts left right`;;

let mpsubryv_identical = new_definition
  `mpsubryv_identical
     (data_length:'p->num)
     (offset:'p->int)
     (minimum:'p->int)
     (maximum:'p->int)
     (zone:'p->'z)
     (pelts:'p->int->int64)
     (left:'p) (right:'p) <=>
     mpsubryv_same_data data_length pelts left right /\
     offset left = offset right /\
     minimum left = minimum right /\
     maximum left = maximum right /\
     zone left = zone right`;;

let mpsubryv_map_eq_sub_shift = new_definition
  `mpsubryv_map_eq_sub_shift
     (pelts:'p->int->int64)
     (left:'p) (right:'p)
     (left_start:int) (right_start:int) (size:int) <=>
     !i:int.
       (&0:int) <= i /\ i < size
       ==> pelts left (left_start + i) =
           pelts right (right_start + i)`;;

let mpsubryv_map_eq_sub = new_definition
  `mpsubryv_map_eq_sub
     (pelts:'p->int->int64)
     (left:'p) (right:'p) (lower:int) (upper:int) <=>
     !i:int.
       lower <= i /\ i < upper
       ==> pelts left i = pelts right i`;;

let mpsubryv_outside_equal = new_definition
  `mpsubryv_outside_equal
     (offset:'p->int)
     (pelts:'p->int->int64)
     (new:'p) (old:'p) (size:int) <=>
     !j:int.
       j < offset new \/ offset new + size <= j
       ==> pelts new j = pelts old j`;;

let mpsubryv_separated = new_definition
  `mpsubryv_separated
     (offset:'p->int) (left:'p) (right:'p) (size:int) <=>
     ((&0:int) <= offset left /\
      offset left + size <= offset right) \/
     ((&0:int) <= offset right /\
      offset right + size <= offset left)`;;

let mpsubryv_result_alias_safe = new_definition
  `mpsubryv_result_alias_safe
     (offset:'p->int)
     (result:'p) (result_size:int)
     (operand:'p) (operand_size:int) <=>
     offset result = offset operand \/
     offset result + result_size <= offset operand \/
     offset operand + operand_size <= offset result`;;

let mpsubryv_continuation = new_definition
  `mpsubryv_continuation
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
     (sy:int32) (sx:int32) (x:'p) (y:'p) <=>
     !y1:'p. !x1:'p.
       offset y1 = offset y /\
       writable y1 = writable y /\
       zone y1 = zone y
       ==>
       offset x1 = offset x /\
       writable x1 = writable x /\
       zone x1 = zone x
       ==>
       (!nr:'p. !ny:'p. !nx:'p. !m:'m.
          writable nr = T /\
          (mpsubryv_value pelts offset ny (ival sx) =
             mpsubryv_value pelts offset y (ival sx) /\
           mpsubryv_value pelts offset nx (ival sx) =
             mpsubryv_value pelts offset x (ival sx)) /\
          (mpsubryv_valid
             data_length offset minimum maximum ny (ival sx) /\
           mpsubryv_valid
             data_length offset minimum maximum nx (ival sx)) /\
          mpsubryv_identical
            data_length offset minimum maximum zone pelts nr ny /\
          mpsubryv_separated offset ny nx (ival sx) /\
          (zx m = zone y1 /\ zy m = zone x1) /\
          (ival (mx m) = maximum y /\ ival (my m) = maximum x) /\
          (lx m = sx /\ ly m = sx) /\
          ok m = T /\
          mpsubryv_map_eq_sub_shift
            pelts ny y1 (offset ny) (offset y1) (ival sx) /\
          mpsubryv_map_eq_sub_shift
            pelts nx x1 (offset nx) (offset x1) (ival sx) /\
          (mpsubryv_same_pelts pelts y1 y /\
           mpsubryv_same_pelts pelts x1 x) /\
          (mpsubryv_plength data_length y1 =
             mpsubryv_plength data_length y /\
           mpsubryv_plength data_length x1 =
             mpsubryv_plength data_length x) /\
          (minimum y1 = minimum y /\ minimum x1 = minimum x) /\
          mpsubryv_same_data data_length pelts nr ny /\
          mpsubryv_same_data data_length pelts ny nx
          ==>
          ((((&0:int) <= ival sy /\
            ival sy <= ival sx) /\
           (mpsubryv_valid
              data_length offset minimum maximum nr (ival sx) /\
            mpsubryv_valid
              data_length offset minimum maximum nx (ival sx) /\
            mpsubryv_valid
              data_length offset minimum maximum ny (ival sy)) /\
           mpsubryv_result_alias_safe
             offset nr (ival sx) nx (ival sx) /\
           mpsubryv_result_alias_safe
             offset nr (ival sx) ny (ival sy) /\
           (mpsubryv_same_data data_length pelts nr nx /\
            mpsubryv_same_data data_length pelts nx ny) /\
           writable nr = T) /\
          (!nx1:'p. !ny1:'p. !nr1:'p.
             mpsubryv_same_data data_length pelts nx1 nr1 /\
             data_length nr1 = data_length nx /\
             offset nx1 = offset nx /\
             minimum nx1 = minimum nx /\
             maximum nx1 = maximum nx /\
             writable nx1 = writable nx /\
             zone nx1 = zone nx
             ==>
             mpsubryv_same_data data_length pelts ny1 nr1 /\
             data_length nr1 = data_length ny /\
             offset ny1 = offset ny /\
             minimum ny1 = minimum ny /\
             maximum ny1 = maximum ny /\
             writable ny1 = writable ny /\
             zone ny1 = zone ny
             ==>
             data_length nr1 = data_length nr /\
             offset nr1 = offset nr /\
             minimum nr1 = minimum nr /\
             maximum nr1 = maximum nr /\
             writable nr1 = writable nr /\
             zone nr1 = zone nr
             ==>
             (!res:int64.
                mpsubryv_value pelts offset nr1 (ival sx) -
                  mpsubryv_radix_power (ival sx) * mpsubryv_u64 res =
                  mpsubryv_value pelts offset nx (ival sx) -
                  mpsubryv_value pelts offset ny (ival sy) /\
                ((&0:int) <= mpsubryv_u64 res /\
                 mpsubryv_u64 res <= (&1:int)) /\
                mpsubryv_outside_equal
                  offset pelts nr1 nr (ival sx) /\
                (offset nr1 = offset nx1 \/
                 mpsubryv_map_eq_sub
                   pelts nx1 nx (offset nx1)
                   (offset nx1 + ival sx)) /\
                (offset nr1 = offset ny1 \/
                 mpsubryv_map_eq_sub
                   pelts ny1 ny (offset ny1)
                   (offset ny1 + ival sy))
                ==>
                (((writable y1 = T /\ writable nr1 = T) /\
                  ok m = T /\
                  ((&0:int) <= ival sx /\
                   ival sx <= ival sx) /\
                  mpsubryv_identical
                    data_length offset minimum maximum zone pelts nr1 ny1 /\
                  mpsubryv_separated offset ny1 nx1 (ival sx) /\
                  (zx m = zone y1 /\ zy m = zone x1) /\
                  lx m = sx /\
                  ly m = sx) /\
                 (!m1:'m.
                  !nx2:'p. !ny2:'p. !y2:'p. !x2:'p.
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
                    offset nx2 = offset nx1 /\
                    writable nx2 = writable nx1 /\
                    zone nx2 = zone nx1
                    ==>
                    offset ny2 = offset ny1 /\
                    writable ny2 = writable ny1 /\
                    zone ny2 = zone ny1
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
                    (maximum y2 = ival (mx m1) /\
                     maximum x2 = ival (my m1)) /\
                    mpsubryv_map_eq_sub_shift
                      pelts ny1 y2
                      (offset ny2) (offset y2) (ival sx) /\
                    mpsubryv_map_eq_sub_shift
                      pelts nx1 x2
                      (offset nx2) (offset x2) (ival sx) /\
                    mpsubryv_outside_equal
                      offset pelts y2 y1 (ival sx) /\
                    mpsubryv_outside_equal
                      offset pelts x2 x1 (ival sx) /\
                    (mpsubryv_plength data_length y2 =
                       mpsubryv_plength data_length y1 /\
                     mpsubryv_plength data_length x2 =
                       mpsubryv_plength data_length x1) /\
                    minimum y2 = minimum y1 /\
                    minimum x2 = minimum x1
                    ==>
                    mpsubryv_value pelts offset y2 (ival sx) -
                      mpsubryv_radix_power (ival sx) * mpsubryv_u64 res =
                      mpsubryv_value pelts offset x (ival sx) -
                      mpsubryv_value pelts offset y (ival sy) /\
                    ((&0:int) <= mpsubryv_u64 res /\
                     mpsubryv_u64 res <= (&1:int)) /\
                    mpsubryv_outside_equal
                      offset pelts y2 y (ival sx) /\
                    mpsubryv_same_pelts pelts x2 x /\
                    mpsubryv_value pelts offset x2 (ival sx) =
                      mpsubryv_value pelts offset x (ival sx) /\
                    (minimum x2 = minimum x /\
                     maximum x2 = maximum x /\
                     mpsubryv_plength data_length x2 =
                       mpsubryv_plength data_length x) /\
                    minimum y2 = minimum y /\
                    maximum y2 = maximum y /\
                    mpsubryv_plength data_length y2 =
                      mpsubryv_plength data_length y))))))`;;

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
   !sy:int32. !sx:int32. !x:'p. !y:'p.
     (&0:int) <= ival sy
     ==>
     ival sy <= ival sx
     ==>
     mpsubryv_valid
       data_length offset minimum maximum x (ival sx)
     ==>
     mpsubryv_valid
       data_length offset minimum maximum y (ival sx)
     ==>
     writable y = T
     ==>
     mpsubryv_valid
       data_length offset minimum maximum y (ival sx) /\
     mpsubryv_valid
       data_length offset minimum maximum x (ival sx) /\
     (&0:int) <= ival sx /\
     ival sx <= ival sx /\
     writable y = T /\
     mpsubryv_continuation
       data_length offset minimum maximum writable zone pelts
       zr zx zy mr mx my lr lx ly ok sy sx x y`;;
