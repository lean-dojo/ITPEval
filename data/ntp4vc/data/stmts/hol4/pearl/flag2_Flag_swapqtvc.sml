(*
  Statement-only formalization of NTP4VC corpus artifact
  pearl/flag2_Flag_swapqtvc: a verification condition that swapping two
  in-bounds elements of a three-color list exchanges those elements, leaves
  every other indexed lookup unchanged, and preserves interval color
  occurrence counts. This file contains no proof.
*)

open HolKernel Parse boolLib bossLib;
open integerTheory listTheory;

Datatype:
  flag_swap_color = FlagSwapBlue | FlagSwapWhite | FlagSwapRed
End

val flag_swap_to_num_def = Define `
  flag_swap_to_num (z : int) = if z < 0 then 0 else Num z`;

val flag_swap_get_def = Define `
  flag_swap_get default_color (xs : flag_swap_color list) (z : int) =
    if flag_swap_to_num z < LENGTH xs then
      EL (flag_swap_to_num z) xs
    else
      default_color`;

val flag_swap_monochrome_def = Define `
  flag_swap_monochrome a i j c <=>
    !k : int. i <= k /\ k < j ==> a k = c`;

val flag2_Flag_swap_vc =
  ``!default_color
      (nb_occ :
        (int -> flag_swap_color) ->
        int -> int -> flag_swap_color -> int).
      (!j i (arr : int -> flag_swap_color) c.
         nb_occ arr i j c =
           if j <= i then
             0
           else if arr (j - 1) = c then
             1 + nb_occ arr i (j - 1) c
           else
             nb_occ arr i (j - 1) c)
      ==>
      !i (a : flag_swap_color list) j.
        (0 : int) <= i ==>
        i < &(LENGTH a) ==>
        (0 : int) <= j ==>
        j < &(LENGTH a) ==>
        (0 : int) <= i /\
        i < &(LENGTH a) /\
        let ai = flag_swap_get default_color a i in
          ((0 : int) <= j /\ j < &(LENGTH a)) /\
          let aj = flag_swap_get default_color a j in
            ((0 : int) <= i /\ i < &(LENGTH a)) /\
            (LENGTH
               (LUPDATE aj (flag_swap_to_num i) a) =
             LENGTH a ==>
             (\z : int.
                flag_swap_get
                  default_color
                  (LUPDATE aj (flag_swap_to_num i) a)
                  z) =
               (\z : int.
                  if z = i then
                    aj
                  else
                    flag_swap_get default_color a z) ==>
             ((0 : int) <= j /\
              j <
                &(LENGTH
                    (LUPDATE aj (flag_swap_to_num i) a))) /\
             (LENGTH
                (LUPDATE
                   ai
                   (flag_swap_to_num j)
                   (LUPDATE aj (flag_swap_to_num i) a)) =
              LENGTH (LUPDATE aj (flag_swap_to_num i) a) ==>
              (\z : int.
                 flag_swap_get
                   default_color
                   (LUPDATE
                      ai
                      (flag_swap_to_num j)
                      (LUPDATE aj (flag_swap_to_num i) a))
                   z) =
                (\z : int.
                   if z = j then
                     ai
                   else
                     flag_swap_get
                       default_color
                       (LUPDATE aj (flag_swap_to_num i) a)
                       z) ==>
              flag_swap_get
                default_color
                (LUPDATE
                   ai
                   (flag_swap_to_num j)
                   (LUPDATE aj (flag_swap_to_num i) a))
                i =
                flag_swap_get default_color a j /\
              flag_swap_get
                default_color
                (LUPDATE
                   ai
                   (flag_swap_to_num j)
                   (LUPDATE aj (flag_swap_to_num i) a))
                j =
                flag_swap_get default_color a i /\
              (!k : int.
                 k <> i /\ k <> j ==>
                 flag_swap_get
                   default_color
                   (LUPDATE
                      ai
                      (flag_swap_to_num j)
                      (LUPDATE aj (flag_swap_to_num i) a))
                   k =
                   flag_swap_get default_color a k) /\
              (!k1 k2 c.
                 (k1 <= i /\ i < k2) /\
                 k1 <= j /\ j < k2 ==>
                 nb_occ
                   (flag_swap_get
                      default_color
                      (LUPDATE
                         ai
                         (flag_swap_to_num j)
                         (LUPDATE aj (flag_swap_to_num i) a)))
                   k1 k2 c =
                 nb_occ
                   (flag_swap_get default_color a)
                   k1 k2 c)))``;
