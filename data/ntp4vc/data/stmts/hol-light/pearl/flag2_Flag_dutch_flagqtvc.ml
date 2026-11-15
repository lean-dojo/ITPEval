(*
  Statement-only formalization of NTP4VC corpus artifact
  pearl/flag2_Flag_dutch_flagqtvc: the Dutch national flag loop verification
  condition, including color-segment invariants, swaps, occurrence counts,
  termination decreases, and the final partition. This file contains no proof.
*)

let flag2_color_INDUCT,flag2_color_RECURSION = define_type
  "flag2_color = Flag2Blue | Flag2White | Flag2Red";;

let flag2_nth = new_definition
 `flag2_nth
    (default:flag2_color) (a:flag2_color list) (i:int) =
    if a = [] then default
    else if i < (&0:int) then EL 0 a
    else if num_of_int i < LENGTH a then EL (num_of_int i) a
    else default`;;

let flag2_monochrome = new_definition
 `flag2_monochrome
    (default:flag2_color) (a:flag2_color list)
    (i:int) (j:int) (c:flag2_color) <=>
    !k:int.
      i <= k /\ k < j
      ==> flag2_nth default a k = c`;;

let flag2_same_counts = new_definition
 `flag2_same_counts
    (default:flag2_color)
    (nb_occ:(int->flag2_color)->int->int->flag2_color->int)
    (a1:flag2_color list) (a:flag2_color list) <=>
    !c:flag2_color.
      nb_occ (flag2_nth default a1)
        (&0:int) (&(LENGTH a1):int) c =
      nb_occ (flag2_nth default a)
        (&0:int) (&(LENGTH a1):int) c`;;

let flag2_blue_case = new_definition
 `flag2_blue_case
    (default:flag2_color)
    (nb_occ:(int->flag2_color)->int->int->flag2_color->int)
    (a:flag2_color list)
    (b:int) (i:int) (r:int) (a1:flag2_color list) <=>
    (((&0:int) <= b /\ b < (&(LENGTH a1):int)) /\
     (&0:int) <= i /\ i < (&(LENGTH a1):int)) /\
    (!a2:flag2_color list.
       LENGTH a2 = LENGTH a1
       ==>
       (flag2_nth default a2 b = flag2_nth default a1 i /\
        flag2_nth default a2 i = flag2_nth default a1 b /\
        (!k:int.
           ~(k = b) /\ ~(k = i)
           ==> flag2_nth default a2 k = flag2_nth default a1 k) /\
        (!k1 k2:int.
         !c:flag2_color.
           (k1 <= b /\ b < k2) /\ k1 <= i /\ i < k2
           ==>
           nb_occ (flag2_nth default a2) k1 k2 c =
           nb_occ (flag2_nth default a1) k1 k2 c))
       ==>
       ((&0:int) <= r - i /\ r - (i + (&1:int)) < r - i) /\
       ((&0:int) <= b + (&1:int) /\
        b + (&1:int) <= i + (&1:int) /\
        i + (&1:int) <= r /\
        r <= (&(LENGTH a2):int)) /\
       flag2_monochrome default a2
         (&0:int) (b + (&1:int)) Flag2Blue /\
       flag2_monochrome default a2
         (b + (&1:int)) (i + (&1:int)) Flag2White /\
       flag2_monochrome default a2
         r (&(LENGTH a2):int) Flag2Red /\
       flag2_same_counts default nb_occ a2 a)`;;

let flag2_white_case = new_definition
 `flag2_white_case
    (default:flag2_color)
    (nb_occ:(int->flag2_color)->int->int->flag2_color->int)
    (a:flag2_color list)
    (b:int) (i:int) (r:int) (a1:flag2_color list) <=>
    ((&0:int) <= r - i /\ r - (i + (&1:int)) < r - i) /\
    ((&0:int) <= b /\
     b <= i + (&1:int) /\
     i + (&1:int) <= r /\
     r <= (&(LENGTH a1):int)) /\
    flag2_monochrome default a1 (&0:int) b Flag2Blue /\
    flag2_monochrome default a1 b (i + (&1:int)) Flag2White /\
    flag2_monochrome default a1
      r (&(LENGTH a1):int) Flag2Red /\
    flag2_same_counts default nb_occ a1 a`;;

let flag2_red_case = new_definition
 `flag2_red_case
    (default:flag2_color)
    (nb_occ:(int->flag2_color)->int->int->flag2_color->int)
    (a:flag2_color list)
    (b:int) (i:int) (r:int) (a1:flag2_color list) <=>
    (((&0:int) <= r - (&1:int) /\
      r - (&1:int) < (&(LENGTH a1):int)) /\
     (&0:int) <= i /\ i < (&(LENGTH a1):int)) /\
    (!a2:flag2_color list.
       LENGTH a2 = LENGTH a1
       ==>
       (flag2_nth default a2 (r - (&1:int)) =
          flag2_nth default a1 i /\
        flag2_nth default a2 i =
          flag2_nth default a1 (r - (&1:int)) /\
        (!k:int.
           ~(k = r - (&1:int)) /\ ~(k = i)
           ==> flag2_nth default a2 k = flag2_nth default a1 k) /\
        (!k1 k2:int.
         !c:flag2_color.
           (k1 <= r - (&1:int) /\ r - (&1:int) < k2) /\
           k1 <= i /\ i < k2
           ==>
           nb_occ (flag2_nth default a2) k1 k2 c =
           nb_occ (flag2_nth default a1) k1 k2 c))
       ==>
       ((&0:int) <= r - i /\
        r - (&1:int) - i < r - i) /\
       ((&0:int) <= b /\
        b <= i /\
        i <= r - (&1:int) /\
        r - (&1:int) <= (&(LENGTH a2):int)) /\
       flag2_monochrome default a2 (&0:int) b Flag2Blue /\
       flag2_monochrome default a2 b i Flag2White /\
       flag2_monochrome default a2
         (r - (&1:int)) (&(LENGTH a2):int) Flag2Red /\
       flag2_same_counts default nb_occ a2 a)`;;

let flag2_exit_case = new_definition
 `flag2_exit_case
    (default:flag2_color)
    (nb_occ:(int->flag2_color)->int->int->flag2_color->int)
    (a:flag2_color list) (a1:flag2_color list) <=>
    (?b1 r1:int.
       flag2_monochrome default a1 (&0:int) b1 Flag2Blue /\
       flag2_monochrome default a1 b1 r1 Flag2White /\
       flag2_monochrome default a1
         r1 (&(LENGTH a1):int) Flag2Red) /\
    flag2_same_counts default nb_occ a1 a`;;

let statement =
 `!default:flag2_color.
  !nb_occ:(int->flag2_color)->int->int->flag2_color->int.
  !a:flag2_color list.
    (!j i:int.
     !f:int->flag2_color.
     !c:flag2_color.
       nb_occ f i j c =
       (if j <= i then (&0:int)
        else if f (j - (&1:int)) = c
        then (&1:int) + nb_occ f i (j - (&1:int)) c
        else nb_occ f i (j - (&1:int)) c))
    ==>
    let o1 = (&(LENGTH a):int) in
    (((&0:int) <= (&0:int) /\
      (&0:int) <= (&0:int) /\
      (&0:int) <= o1 /\
      o1 <= (&(LENGTH a):int)) /\
     flag2_monochrome default a
       (&0:int) (&0:int) Flag2Blue /\
     flag2_monochrome default a
       (&0:int) (&0:int) Flag2White /\
     flag2_monochrome default a
       o1 (&(LENGTH a):int) Flag2Red) /\
    (!r i b:int.
     !a1:flag2_color list.
       LENGTH a1 = LENGTH a
       ==>
       ((&0:int) <= b /\ b <= i /\ i <= r /\
        r <= (&(LENGTH a1):int)) /\
       flag2_monochrome default a1 (&0:int) b Flag2Blue /\
       flag2_monochrome default a1 b i Flag2White /\
       flag2_monochrome default a1
         r (&(LENGTH a1):int) Flag2Red /\
       flag2_same_counts default nb_occ a1 a
       ==>
       if i < r then
         ((&0:int) <= i /\ i < (&(LENGTH a1):int)) /\
         (if flag2_nth default a1 i = Flag2Blue then
            flag2_blue_case default nb_occ a b i r a1
          else if flag2_nth default a1 i = Flag2White then
            flag2_white_case default nb_occ a b i r a1
          else
            flag2_red_case default nb_occ a b i r a1)
       else
         flag2_exit_case default nb_occ a a1)`;;
