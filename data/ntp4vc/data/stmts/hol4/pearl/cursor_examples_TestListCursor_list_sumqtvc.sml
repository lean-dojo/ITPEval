(*
  Statement-only formalization of NTP4VC corpus artifact
  pearl/cursor_examples_TestListCursor_list_sumqtvc: a list-cursor
  verification condition relating the visited-prefix sum, cursor invariant,
  decreasing remaining length, and full-list sum at completion. This file
  contains no proof.
*)

open HolKernel Parse boolLib bossLib;
open integerTheory listTheory;

val cursor_list_sum_def = Define `
  (cursor_list_sum ([] : int list) = (0 : int)) /\
  (cursor_list_sum (x::xs) = x + cursor_list_sum xs)`;

val cursor_examples_TestListCursor_list_sum_vc =
  ``!(visited : 'cursor -> int list)
      (collection : 'cursor -> int list)
      (c : 'cursor)
      (l : int list).
      let permitted =
        \d : 'cursor.
          LENGTH (visited d) <= LENGTH (collection d) /\
          !i : int.
            (0 : int) <= i /\
            i < &(LENGTH (visited d)) ==>
            EL (Num i) (visited d) = EL (Num i) (collection d)
      in
      let complete =
        \d : 'cursor.
          LENGTH (visited d) = LENGTH (collection d)
      in
        permitted c /\
        visited c = [] /\
        collection c = l ==>
        (0 : int) = cursor_list_sum (visited c) /\
        permitted c /\
        !c1 : 'cursor.
          collection c1 = collection c ==>
          permitted c1 ==>
          permitted c1 /\
          if ~complete c1 then
            (~complete c1 /\ permitted c1) /\
            !c2 : 'cursor.
              collection c2 = collection c1 ==>
              !x : int.
                visited c2 = APPEND (visited c1) [x] /\
                permitted c2 ==>
                ((0 : int) <=
                   &(LENGTH l) - &(LENGTH (visited c1)) /\
                 &(LENGTH l) - &(LENGTH (visited c2)) <
                   &(LENGTH l) - &(LENGTH (visited c1))) /\
                cursor_list_sum (visited c1) + x =
                  cursor_list_sum (visited c2) /\
                permitted c2
          else
            cursor_list_sum (visited c1) = cursor_list_sum l``;
