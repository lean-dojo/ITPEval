(*
  Statement-only formalization of PutnamBench artifact putnam_1962_a1:
  among five points in the real plane with no three collinear, some four are
  the vertices of a convex quadrilateral. This file contains no proof.
*)

let statement =
  `!S:(real#real)->bool.
     S HAS_SIZE 5 /\
     (!s. s SUBSET S /\ s HAS_SIZE 3
          ==> ~(?p d:real#real.
                   !x. x IN s
                       ==> ?c:real.
                             x = (FST p + c * FST d,
                                  SND p + c * SND d)))
     ==> ?T. T SUBSET S /\
             T HAS_SIZE 4 /\
             ~(?t. t IN T /\
                   (!C:(real#real)->bool.
                      (T DELETE t) SUBSET C /\
                      (!x y:real#real.
                         !u v:real.
                           x IN C /\ y IN C /\
                           &0 <= u /\ &0 <= v /\ u + v = &1
                           ==> (u * FST x + v * FST y,
                                u * SND x + v * SND y) IN C)
                      ==> t IN C))`;;
