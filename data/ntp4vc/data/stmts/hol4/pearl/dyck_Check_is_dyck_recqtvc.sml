(*
  Statement-only formalization of NTP4VC corpus artifact
  pearl/dyck_Check_is_dyck_recqtvc: a recursive Dyck-word recognition
  verification condition using unique balanced-prefix decompositions and
  propagated failure conditions. This file contains no proof.
*)

open HolKernel Parse boolLib bossLib;
open integerTheory listTheory;

Datatype:
  dyck_paren = DyckL | DyckR
End

val (dyck_word_rules,
     dyck_word_ind,
     dyck_word_cases) =
  Hol_reln `
    dyck_word ([] : dyck_paren list) /\
    (!w1 w2.
       dyck_word w1 /\
       dyck_word w2 ==>
       dyck_word (DyckL :: (w1 ++ (DyckR :: w2))))
  `;

val dyck_fall_def = Define `
  dyck_fall p s <=>
    dyck_word p /\
    case s of
      [] => T
    | DyckL :: rest => F
    | DyckR :: rest => T`;

val dyck_Check_is_dyck_rec_vc =
  ``!w : dyck_paren list.
      case w of
        [] =>
          w = ([] : dyck_paren list) ++ w /\
          dyck_fall ([] : dyck_paren list) w /\
          (!p2 s.
             w = p2 ++ s /\
             dyck_fall p2 s ==>
             p2 = ([] : dyck_paren list) /\
             s = w)
      | head :: w0 =>
          if head = DyckL then
            ((0 : int) <= &(LENGTH w) /\
             LENGTH w0 < LENGTH w) /\
            (!p0.
               (!o1.
                  w0 = p0 ++ o1 /\
                  dyck_fall p0 o1 /\
                  (!p2 s.
                     w0 = p2 ++ s /\
                     dyck_fall p2 s ==>
                     p2 = p0 /\
                     s = o1)
                  ==>
                  case o1 of
                    [] =>
                      !p s.
                        w = p ++ s ==>
                        ~dyck_fall p s
                  | inner_head :: w1 =>
                      ((0 : int) <= &(LENGTH w) /\
                       LENGTH w1 < LENGTH w) /\
                      (!p1.
                         !w2.
                           w1 = p1 ++ w2 /\
                           dyck_fall p1 w2 /\
                           (!p2 s.
                              w1 = p2 ++ s /\
                              dyck_fall p2 s ==>
                              p2 = p1 /\
                              s = w2)
                           ==>
                           w =
                             (DyckL ::
                               (p0 ++ (DyckR :: p1))) ++
                             w2 /\
                           dyck_fall
                             (DyckL ::
                               (p0 ++ (DyckR :: p1)))
                             w2 /\
                           (!p2 s.
                              w = p2 ++ s /\
                              dyck_fall p2 s ==>
                              p2 =
                                DyckL ::
                                  (p0 ++ (DyckR :: p1)) /\
                              s = w2)) /\
                      ((!p s.
                          w1 = p ++ s ==>
                          ~dyck_fall p s)
                       ==>
                       (!p s.
                          w = p ++ s ==>
                          ~dyck_fall p s))) /\
               ((!p s.
                   w0 = p ++ s ==>
                   ~dyck_fall p s)
                ==>
                (!p s.
                   w = p ++ s ==>
                   ~dyck_fall p s)))
          else
            w = ([] : dyck_paren list) ++ w /\
            dyck_fall ([] : dyck_paren list) w /\
            (!p2 s.
               w = p2 ++ s /\
               dyck_fall p2 s ==>
               p2 = ([] : dyck_paren list) /\
               s = w)``;
