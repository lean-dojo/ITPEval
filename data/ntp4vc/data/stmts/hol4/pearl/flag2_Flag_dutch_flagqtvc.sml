(*
  Statement-only formalization of NTP4VC corpus artifact
  pearl/flag2_Flag_dutch_flagqtvc: the initialization, loop-step, and
  termination verification conditions for the three-color Dutch flag
  partition algorithm. This file contains no proof.
*)

open HolKernel Parse boolLib bossLib;
open integerTheory listTheory;

Datatype:
  flag_color = FlagBlue | FlagWhite | FlagRed
End

val flag_to_num_def = Define `
  flag_to_num (z : int) = if z < 0 then 0 else Num z`;

val flag_get_def = Define `
  flag_get default_color (xs : flag_color list) (z : int) =
    if flag_to_num z < LENGTH xs then
      EL (flag_to_num z) xs
    else
      default_color`;

val flag_monochrome_def = Define `
  flag_monochrome a i j c <=>
    !k : int. i <= k /\ k < j ==> a k = c`;

val flag2_Flag_dutch_flag_vc =
  ``!default_color
      (nb_occ :
        (int -> flag_color) -> int -> int -> flag_color -> int).
      (!j i (arr : int -> flag_color) c.
         nb_occ arr i j c =
           if j <= i then
             0
           else if arr (j - 1) = c then
             1 + nb_occ arr i (j - 1) c
           else
             nb_occ arr i (j - 1) c)
      ==>
      !a : flag_color list.
        let o1 = &(LENGTH a)
        in
          (((0 : int) <= 0 /\
            (0 : int) <= 0 /\
            (0 : int) <= o1 /\
            o1 <= &(LENGTH a)) /\
           flag_monochrome (flag_get default_color a) 0 0 FlagBlue /\
           flag_monochrome (flag_get default_color a) 0 0 FlagWhite /\
           flag_monochrome
             (flag_get default_color a) o1 (&(LENGTH a)) FlagRed) /\
          !r i b (a1 : flag_color list).
            LENGTH a1 = LENGTH a ==>
            ((0 : int) <= b /\
             b <= i /\
             i <= r /\
             r <= &(LENGTH a1)) /\
            flag_monochrome (flag_get default_color a1) 0 b FlagBlue /\
            flag_monochrome (flag_get default_color a1) b i FlagWhite /\
            flag_monochrome
              (flag_get default_color a1) r (&(LENGTH a1)) FlagRed /\
            (!c.
               nb_occ
                 (flag_get default_color a1) 0 (&(LENGTH a1)) c =
               nb_occ
                 (flag_get default_color a) 0 (&(LENGTH a1)) c)
            ==>
            if i < r then
              ((0 : int) <= i /\ i < &(LENGTH a1)) /\
              (case flag_get default_color a1 i of
                 FlagBlue =>
                   (((0 : int) <= b /\ b < &(LENGTH a1)) /\
                    (0 : int) <= i /\ i < &(LENGTH a1)) /\
                   !a2 : flag_color list.
                     LENGTH a2 = LENGTH a1 ==>
                     flag_get default_color a2 b =
                       flag_get default_color a1 i /\
                     flag_get default_color a2 i =
                       flag_get default_color a1 b /\
                     (!k : int.
                        k <> b /\ k <> i ==>
                        flag_get default_color a2 k =
                        flag_get default_color a1 k) /\
                     (!k1 k2 c.
                        (k1 <= b /\ b < k2) /\
                        k1 <= i /\ i < k2 ==>
                        nb_occ
                          (flag_get default_color a2) k1 k2 c =
                        nb_occ
                          (flag_get default_color a1) k1 k2 c)
                     ==>
                     ((0 : int) <= r - i /\
                      r - (i + 1) < r - i) /\
                     ((0 : int) <= b + 1 /\
                      b + 1 <= i + 1 /\
                      i + 1 <= r /\
                      r <= &(LENGTH a2)) /\
                     flag_monochrome
                       (flag_get default_color a2)
                       0 (b + 1) FlagBlue /\
                     flag_monochrome
                       (flag_get default_color a2)
                       (b + 1) (i + 1) FlagWhite /\
                     flag_monochrome
                       (flag_get default_color a2)
                       r (&(LENGTH a2)) FlagRed /\
                     (!c.
                        nb_occ
                          (flag_get default_color a2)
                          0 (&(LENGTH a2)) c =
                        nb_occ
                          (flag_get default_color a)
                          0 (&(LENGTH a2)) c)
               | FlagWhite =>
                   ((0 : int) <= r - i /\
                    r - (i + 1) < r - i) /\
                   ((0 : int) <= b /\
                    b <= i + 1 /\
                    i + 1 <= r /\
                    r <= &(LENGTH a1)) /\
                   flag_monochrome
                     (flag_get default_color a1) 0 b FlagBlue /\
                   flag_monochrome
                     (flag_get default_color a1)
                     b (i + 1) FlagWhite /\
                   flag_monochrome
                     (flag_get default_color a1)
                     r (&(LENGTH a1)) FlagRed /\
                   (!c.
                      nb_occ
                        (flag_get default_color a1)
                        0 (&(LENGTH a1)) c =
                      nb_occ
                        (flag_get default_color a)
                        0 (&(LENGTH a1)) c)
               | FlagRed =>
                   (((0 : int) <= r - 1 /\
                     r - 1 < &(LENGTH a1)) /\
                    (0 : int) <= i /\ i < &(LENGTH a1)) /\
                   !a2 : flag_color list.
                     LENGTH a2 = LENGTH a1 ==>
                     flag_get default_color a2 (r - 1) =
                       flag_get default_color a1 i /\
                     flag_get default_color a2 i =
                       flag_get default_color a1 (r - 1) /\
                     (!k : int.
                        k <> r - 1 /\ k <> i ==>
                        flag_get default_color a2 k =
                        flag_get default_color a1 k) /\
                     (!k1 k2 c.
                        (k1 <= r - 1 /\ r - 1 < k2) /\
                        k1 <= i /\ i < k2 ==>
                        nb_occ
                          (flag_get default_color a2) k1 k2 c =
                        nb_occ
                          (flag_get default_color a1) k1 k2 c)
                     ==>
                     ((0 : int) <= r - i /\
                      r - 1 - i < r - i) /\
                     ((0 : int) <= b /\
                      b <= i /\
                      i <= r - 1 /\
                      r - 1 <= &(LENGTH a2)) /\
                     flag_monochrome
                       (flag_get default_color a2) 0 b FlagBlue /\
                     flag_monochrome
                       (flag_get default_color a2) b i FlagWhite /\
                     flag_monochrome
                       (flag_get default_color a2)
                       (r - 1) (&(LENGTH a2)) FlagRed /\
                     (!c.
                        nb_occ
                          (flag_get default_color a2)
                          0 (&(LENGTH a2)) c =
                        nb_occ
                          (flag_get default_color a)
                          0 (&(LENGTH a2)) c))
            else
              (?b1 r1 : int.
                 flag_monochrome
                   (flag_get default_color a1) 0 b1 FlagBlue /\
                 flag_monochrome
                   (flag_get default_color a1) b1 r1 FlagWhite /\
                 flag_monochrome
                   (flag_get default_color a1)
                   r1 (&(LENGTH a1)) FlagRed) /\
              (!c.
                 nb_occ
                   (flag_get default_color a1)
                   0 (&(LENGTH a1)) c =
                 nb_occ
                   (flag_get default_color a)
                   0 (&(LENGTH a1)) c)``;
