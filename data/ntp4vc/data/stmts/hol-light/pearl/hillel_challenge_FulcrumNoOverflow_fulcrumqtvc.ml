(*
  Statement-only formalization of NTP4VC corpus artifact
  pearl/hillel_challenge_FulcrumNoOverflow_fulcrumqtvc: the fulcrum-search
  verification condition for 32-bit array indices and exact integer partial
  sums, including the accumulator overflow bounds and minimum-difference loop
  invariants. This file contains no proof.
*)

let fulcrum_output = open_out "/dev/null";;
let fulcrum_formatter = Format.formatter_of_out_channel fulcrum_output;;
let fulcrum_previous_loader = !Hol_loader.file_loader;;
Hol_loader.file_loader :=
  (fun path -> Toploop.use_file fulcrum_formatter path);;
let fulcrum_words_loaded =
  Toploop.use_file fulcrum_formatter "Library/words.ml";;
Hol_loader.file_loader := fulcrum_previous_loader;;
Format.pp_print_flush fulcrum_formatter ();;
close_out fulcrum_output;;
if not fulcrum_words_loaded then failwith "could not load Library/words.ml";;

let _ = new_definition
  `fulcrum_int32_in_bounds (x:int) <=>
     --(&2147483648:int) <= x /\ x <= (&2147483647:int)`;;

let _ = new_definition
  `fulcrum_sum (elts:A->int->(32)word) (a:A) (l:int) (u:int) =
     isum {i:int | l <= i /\ i < u} (\i. ival (elts a i))`;;

let _ = new_definition
  `fulcrum_diff
      (elts:A->int->(32)word) (length:A->(32)word) (a:A) (i:int) =
     abs
       (fulcrum_sum elts a (&0:int) i -
        fulcrum_sum elts a i (ival (length a)))`;;

let _ = new_definition
  `fulcrum_big_invariant
      (q:B->(32)word) (r:B->(32)word) (v:B->int) (self:B) <=>
     --(&2147483648:int) <= ival (q self) /\
     ival (q self) <= (&2147483647:int) /\
     (&0:int) <= ival (r self) /\
     ival (r self) <= (&2147483647:int) /\
     v self =
       ival (q self) * (&2147483648:int) + ival (r self)`;;

let _ = new_definition
  `fulcrum_search_phase
      (q:B->(32)word) (r:B->(32)word) (v:B->int)
      (elts:A->int->(32)word) (length:A->(32)word)
      (a:A) (n:(32)word) (o2:(32)word) <=>
     !bestd1:B. !besti:(32)word. !left2:B. !right2:B.
       ((!i:(32)word.
           let i1 = ival i in
           ((&0:int) <= i1 /\ i1 <= ival o2) /\
           (&55:int) < (&89:int) /\
           v left2 = fulcrum_sum elts a (&0:int) i1 /\
           v right2 = fulcrum_sum elts a i1 (ival n) /\
           ((&0:int) <= ival besti /\ ival besti <= i1) /\
           v bestd1 = fulcrum_diff elts length a (ival besti) /\
           (!j:int.
              (&0:int) <= j /\ j <= i1
              ==> v bestd1 <= fulcrum_diff elts length a j)
           ==>
           ((&0:int) <= ival i /\ ival i < ival (length a)) /\
           (let o3 = elts a (ival i) in
            --(&2147483648:int) * (&2147483648:int) <=
              v left2 + ival o3 /\
            v left2 + ival o3 <=
              (&2147483648:int) * (&2147483648:int) - (&1:int) /\
            (!left3:B.
               v left3 = v left2 + ival o3
               ==>
               ((&0:int) <= ival i /\ ival i < ival (length a)) /\
               (let o4 = elts a (ival i) in
                --(&2147483648:int) * (&2147483648:int) <=
                  v right2 - ival o4 /\
                v right2 - ival o4 <=
                  (&2147483648:int) * (&2147483648:int) - (&1:int) /\
                (!right3:B.
                   v right3 = v right2 - ival o4
                   ==>
                   --(&2147483648:int) * (&2147483648:int) <=
                     abs (v left3 - v right3) /\
                   abs (v left3 - v right3) <=
                     (&2147483648:int) * (&2147483648:int) - (&1:int) /\
                   (!d:B.
                      v d = abs (v left3 - v right3)
                      ==>
                      ((&0:int) <= v d /\ (&0:int) <= v bestd1) /\
                      (if v d < v bestd1 then
                         !bestd2:B.
                           fulcrum_int32_in_bounds
                             (ival i + (&1:int)) /\
                           (!o5:(32)word.
                              ival o5 = ival i + (&1:int)
                              ==>
                              fulcrum_big_invariant q r v d /\
                              (v d = v bestd2 /\
                               r d = r bestd2 /\
                               q d = q bestd2
                               ==>
                               (&55:int) < (&89:int) /\
                               v left3 =
                                 fulcrum_sum
                                   elts a (&0:int) (i1 + (&1:int)) /\
                               v right3 =
                                 fulcrum_sum
                                   elts a (i1 + (&1:int)) (ival n) /\
                               ((&0:int) <= ival o5 /\
                                ival o5 <= i1 + (&1:int)) /\
                               v bestd2 =
                                 fulcrum_diff
                                   elts length a (ival o5) /\
                               (!j:int.
                                  (&0:int) <= j /\
                                  j <= i1 + (&1:int)
                                  ==>
                                  v bestd2 <=
                                    fulcrum_diff elts length a j)))
                       else
                         (&55:int) < (&89:int) /\
                         v left3 =
                           fulcrum_sum
                             elts a (&0:int) (i1 + (&1:int)) /\
                         v right3 =
                           fulcrum_sum
                             elts a (i1 + (&1:int)) (ival n) /\
                         ((&0:int) <= ival besti /\
                          ival besti <= i1 + (&1:int)) /\
                         v bestd1 =
                           fulcrum_diff elts length a (ival besti) /\
                         (!j:int.
                            (&0:int) <= j /\ j <= i1 + (&1:int)
                            ==>
                            v bestd1 <=
                              fulcrum_diff elts length a j)))))))) /\
        (((&55:int) < (&89:int) /\
          v left2 =
            fulcrum_sum elts a (&0:int) (ival o2 + (&1:int)) /\
          v right2 =
            fulcrum_sum elts a (ival o2 + (&1:int)) (ival n) /\
          ((&0:int) <= ival besti /\
           ival besti <= ival o2 + (&1:int)) /\
          v bestd1 = fulcrum_diff elts length a (ival besti) /\
          (!j:int.
             (&0:int) <= j /\ j <= ival o2 + (&1:int)
             ==> v bestd1 <= fulcrum_diff elts length a j))
         ==>
         ((&0:int) <= ival besti /\
          ival besti <= ival (length a)) /\
         (!i:int.
            (&0:int) <= i /\ i <= ival (length a)
            ==>
            fulcrum_diff elts length a (ival besti) <=
              fulcrum_diff elts length a i)))`;;

let _ = new_definition
  `fulcrum_after_right
      (q:B->(32)word) (r:B->(32)word) (v:B->int) (zero:B)
      (elts:A->int->(32)word) (length:A->(32)word)
      (a:A) (n:(32)word) (right:B) <=>
     let left1 = zero in
     --(&2147483648:int) * (&2147483648:int) <=
       abs (v left1 - v right) /\
     abs (v left1 - v right) <=
       (&2147483648:int) * (&2147483648:int) - (&1:int) /\
     (!bestd:B.
        v bestd = abs (v left1 - v right)
        ==>
        fulcrum_int32_in_bounds (ival n - (&1:int)) /\
        (!o2:(32)word.
           ival o2 = ival n - (&1:int)
           ==>
           (((&0:int) <= ival o2 + (&1:int)
             ==>
             ((&55:int) < (&89:int) /\
              v left1 = fulcrum_sum elts a (&0:int) (&0:int) /\
              v right = fulcrum_sum elts a (&0:int) (ival n) /\
              (&0:int) <= (&0:int) /\
              v bestd = fulcrum_diff elts length a (&0:int) /\
              (!j:int.
                 (&0:int) <= j /\ j <= (&0:int)
                 ==> v bestd <= fulcrum_diff elts length a j)) /\
             fulcrum_search_phase q r v elts length a n o2) /\
            (ival o2 + (&1:int) < (&0:int)
             ==>
             ((&0:int) <= (&0:int) /\
              (&0:int) <= ival (length a)) /\
             (!i:int.
                (&0:int) <= i /\ i <= ival (length a)
                ==> fulcrum_diff elts length a (&0:int) <=
                    fulcrum_diff elts length a i)))))`;;

let statement =
  `!q:B->(32)word.
   !r:B->(32)word.
   !v:B->int.
   !zero:B.
   !elts:A->int->(32)word.
   !length:A->(32)word.
     ((!self:B. fulcrum_big_invariant q r v self) /\
      (!x y:B.
         q x = q y /\ r x = r y /\ v x = v y ==> x = y) /\
      q zero = (word 0:(32)word) /\
      r zero = (word 0:(32)word) /\
      v zero = (&0:int))
     ==>
     !a:A.
       ival (length a) < (&2147483647:int)
       ==>
       let n = length a in
       let right1 = zero in
       fulcrum_int32_in_bounds (ival n - (&1:int)) /\
       (!o1:(32)word.
          ival o1 = ival n - (&1:int)
          ==>
          (((&0:int) <= ival o1 + (&1:int)
            ==>
            ((&55:int) < (&89:int) /\
             v right1 =
               fulcrum_sum elts a (&0:int) (&0:int)) /\
            (!right2:B.
               ((!i:(32)word.
                   let i1 = ival i in
                   ((&0:int) <= i1 /\ i1 <= ival o1) /\
                   (&55:int) < (&89:int) /\
                   v right2 =
                     fulcrum_sum elts a (&0:int) i1
                   ==>
                   ((&0:int) <= ival i /\
                    ival i < ival (length a)) /\
                   (let o2 = elts a (ival i) in
                    --(&2147483648:int) * (&2147483648:int) <=
                      v right2 + ival o2 /\
                    v right2 + ival o2 <=
                      (&2147483648:int) * (&2147483648:int) -
                      (&1:int) /\
                    (!right3:B.
                       v right3 = v right2 + ival o2
                       ==>
                       (&55:int) < (&89:int) /\
                       v right3 =
                         fulcrum_sum
                           elts a (&0:int) (i1 + (&1:int))))) /\
                (((&55:int) < (&89:int) /\
                  v right2 =
                    fulcrum_sum
                      elts a (&0:int) (ival o1 + (&1:int)))
                 ==>
                 fulcrum_after_right
                   q r v zero elts length a n right2)))) /\
           (ival o1 + (&1:int) < (&0:int)
            ==>
            fulcrum_after_right
              q r v zero elts length a n right1)))`;;
