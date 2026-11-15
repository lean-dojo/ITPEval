(*
  Statement-only formalization of NTP4VC corpus artifact
  pearl/multiprecision/sub_Sub_subqtvc: the verification condition for
  alias-aware unequal-length multiprecision subtraction into a separate
  result pointer, including borrow arithmetic, memory framing, validity,
  and preservation of operand data and pointer metadata. This file contains
  no proof.
*)

needs "Library/words.ml";;
needs "Library/isum.ml";;

let statement =
  `!data:'p->int64 list.
   !offset:'p->int.
   !minimum:'p->int.
   !maximum:'p->int.
   !writable:'p->bool.
   !zone:'p->'z.
   !zr:'m->'z. !zx:'m->'z. !zy:'m->'z.
   !mr:'m->int32. !mx:'m->int32. !my:'m->int32.
   !lr:'m->int32. !lx:'m->int32. !ly:'m->int32.
   !ok:'m->bool.
   !sy:int32. !sx:int32.
   !r:'p. !x:'p. !y:'p.
     let radix = (&18446744073709551616:int) in
     let u64 = \w:int64. (&(val w):int) in
     let int32_in_bounds =
       \n:int.
         --(&2147483648:int) <= n /\
         n <= (&2147483647:int) in
     let pelts =
       \(p:'p) (i:int).
         let k = if i < (&0:int) then 0 else num_of_int i in
         if k < LENGTH (data p) then EL k (data p)
         else (word 0:int64) in
     let plength =
       \p:'p. (&(LENGTH (data p)):int) in
     let valid =
       \(p:'p) (n:int).
         int32_in_bounds n /\
         (&0:int) <= n /\
         (&0:int) <= minimum p /\
         minimum p <= offset p /\
         offset p + n <= maximum p /\
         maximum p <= plength p in
     let radix_power =
       \n:int. radix pow (if n < (&0:int) then 0 else num_of_int n) in
     let value =
       \(p:'p) (n:int).
         if n <= (&0:int) then (&0:int)
         else
           isum (0..num_of_int n - 1)
             (\k. radix pow k * u64 (pelts p (offset p + &k))) in
     let map_eq_sub_shift =
       \(left:'p) (right:'p)
        (left_start:int) (right_start:int) (size:int).
         !i:int.
           (&0:int) <= i /\ i < size
           ==> pelts left (left_start + i) =
               pelts right (right_start + i) in
     let map_eq_sub =
       \(left:'p) (right:'p) (lower:int) (upper:int).
         !i:int.
           lower <= i /\ i < upper
           ==> pelts left i = pelts right i in
     let outside_equal =
       \(newp:'p) (oldp:'p) (size:int).
         !j:int.
           j < offset newp \/ offset newp + size <= j
           ==> pelts newp j = pelts oldp j in
     let same_pelts =
       \(left:'p) (right:'p).
         !j:int. pelts left j = pelts right j in
     let view =
       \(current:'p) (oldp:'p).
         offset current = offset oldp /\
         writable current = writable oldp /\
         zone current = zone oldp in
     let view_with_minimum =
       \(current:'p) (oldp:'p).
         offset current = offset oldp /\
         minimum current = minimum oldp /\
         writable current = writable oldp /\
         zone current = zone oldp in
     let memory_view =
       \(current:'m) (oldm:'m).
         zr current = zr oldm /\
         zx current = zx oldm /\
         zy current = zy oldm /\
         mr current = mr oldm /\
         mx current = mx oldm /\
         my current = my oldm /\
         lr current = lr oldm /\
         lx current = lx oldm /\
         ly current = ly oldm in
     (&0:int) <= ival sy
     ==>
     ival sy <= ival sx
     ==>
     valid r (ival sx)
     ==>
     valid x (ival sx)
     ==>
     valid y (ival sy)
     ==>
     writable r = T
     ==>
     valid r (ival sx) /\
     valid x (ival sx) /\
     valid y (ival sy) /\
     writable r = T /\
     (&0:int) <= ival sy /\
     ival sy <= ival sx /\
     (!y1:'p. !x1:'p. !r1:'p.
        view y1 y
        ==>
        view x1 x
        ==>
        view r1 r
        ==>
        (!nr:'p. !nx:'p. !ny:'p. !m:'m.
           writable nr = T /\
           (value nx (ival sx) = value x (ival sx) /\
            value ny (ival sy) = value y (ival sy)) /\
           (valid nr (ival sx) /\
            valid nx (ival sx) /\
            valid ny (ival sy)) /\
           ((&0:int) <= offset nr /\
            offset nr + ival sx <= offset nx /\
            offset nx + ival sx <= offset ny) /\
           (zr m = zone r1 /\ zx m = zone x1 /\ zy m = zone y1) /\
           (ival (mr m) = maximum r /\
            ival (mx m) = maximum x /\
            ival (my m) = maximum y) /\
           (lr m = sx /\ lx m = sx /\ ly m = sy) /\
           ok m = T /\
           map_eq_sub_shift
             nr r1 (offset nr) (offset r1) (ival sx) /\
           map_eq_sub_shift
             nx x1 (offset nx) (offset x1) (ival sx) /\
           map_eq_sub_shift
             ny y1 (offset ny) (offset y1) (ival sy) /\
           (same_pelts r1 r /\
            same_pelts x1 x /\
            same_pelts y1 y) /\
           (plength r1 = plength r /\
            plength x1 = plength x /\
            plength y1 = plength y) /\
           (minimum r1 = minimum r /\
            minimum x1 = minimum x /\
            minimum y1 = minimum y) /\
           data nr = data nx /\
           data nx = data ny
           ==>
           (((&0:int) <= ival sy /\ ival sy <= ival sx) /\
            (valid nr (ival sx) /\
             valid nx (ival sx) /\
             valid ny (ival sy)) /\
            (offset nr = offset nx \/
             offset nr + ival sx <= offset nx \/
             offset nx + ival sx <= offset nr) /\
            (offset nr = offset ny \/
             offset nr + ival sx <= offset ny \/
             offset ny + ival sy <= offset nr) /\
            (data nr = data nx /\ data nx = data ny) /\
            writable nr = T) /\
           (!ny1:'p. !nx1:'p. !nr1:'p.
              data ny1 = data nr1 /\
              LENGTH (data nr1) = LENGTH (data ny) /\
              offset ny1 = offset ny /\
              minimum ny1 = minimum ny /\
              maximum ny1 = maximum ny /\
              writable ny1 = writable ny /\
              zone ny1 = zone ny
              ==>
              data nx1 = data nr1 /\
              LENGTH (data nr1) = LENGTH (data nx) /\
              offset nx1 = offset nx /\
              minimum nx1 = minimum nx /\
              maximum nx1 = maximum nx /\
              writable nx1 = writable nx /\
              zone nx1 = zone nx
              ==>
              LENGTH (data nr1) = LENGTH (data nr) /\
              offset nr1 = offset nr /\
              minimum nr1 = minimum nr /\
              maximum nr1 = maximum nr /\
              writable nr1 = writable nr /\
              zone nr1 = zone nr
              ==>
              (!res:int64.
                 value nr1 (ival sx) -
                   radix_power (ival sx) * u64 res =
                   value nx (ival sx) - value ny (ival sy) /\
                 ((&0:int) <= u64 res /\ u64 res <= (&1:int)) /\
                 outside_equal nr1 nr (ival sx) /\
                 (offset nr1 = offset nx1 \/
                  map_eq_sub
                    nx1 nx (offset nx1) (offset nx1 + ival sx)) /\
                 (offset nr1 = offset ny1 \/
                  map_eq_sub
                    ny1 ny (offset ny1) (offset ny1 + ival sy))
                 ==>
                 (ok m = T /\
                  ((&0:int) <= ival sy /\ ival sy <= ival sx) /\
                  (zr m = zone r1 /\
                   zx m = zone x1 /\
                   zy m = zone y1) /\
                  (lr m = sx /\ lx m = sx /\ ly m = sy) /\
                  ((&0:int) <= offset nr1 /\
                   offset nr1 + ival sx <= offset nx1 /\
                   offset nx1 + ival sx <= offset ny1) /\
                  writable r1 = T /\
                  writable nr1 = T) /\
                 (!m1:'m.
                  !ny2:'p. !nx2:'p. !nr2:'p.
                  !y2:'p. !x2:'p. !r2:'p.
                    memory_view m1 m
                    ==>
                    view ny2 ny1
                    ==>
                    view nx2 nx1
                    ==>
                    view nr2 nr1
                    ==>
                    view_with_minimum y2 y1
                    ==>
                    view_with_minimum x2 x1
                    ==>
                    view_with_minimum r2 r1
                    ==>
                    (maximum r2 = ival (mr m1) /\
                     maximum x2 = ival (mx m1) /\
                     maximum y2 = ival (my m1)) /\
                    map_eq_sub_shift
                      nr1 r2 (offset nr2) (offset r2) (ival sx) /\
                    map_eq_sub_shift
                      nx1 x2 (offset nx2) (offset x2) (ival sx) /\
                    map_eq_sub_shift
                      ny1 y2 (offset ny2) (offset y2) (ival sy) /\
                    outside_equal r2 r1 (ival sx) /\
                    outside_equal x2 x1 (ival sx) /\
                    outside_equal y2 y1 (ival sy) /\
                    (plength r2 = plength r1 /\
                     plength x2 = plength x1 /\
                     plength y2 = plength y1) /\
                    minimum r2 = minimum r1 /\
                    minimum x2 = minimum x1 /\
                    minimum y2 = minimum y1
                    ==>
                    value r2 (ival sx) -
                      radix_power (ival sx) * u64 res =
                      value x (ival sx) - value y (ival sy) /\
                    ((&0:int) <= u64 res /\ u64 res <= (&1:int)) /\
                    outside_equal r2 r (ival sx) /\
                    same_pelts x2 x /\
                    same_pelts y2 y /\
                    value x2 (ival sx) = value x (ival sx) /\
                    value y2 (ival sy) = value y (ival sy) /\
                    (minimum x2 = minimum x /\
                     maximum x2 = maximum x /\
                     plength x2 = plength x) /\
                    (minimum y2 = minimum y /\
                     maximum y2 = maximum y /\
                     plength y2 = plength y) /\
                    minimum r2 = minimum r /\
                    maximum r2 = maximum r /\
                    plength r2 = plength r)))))`;;
