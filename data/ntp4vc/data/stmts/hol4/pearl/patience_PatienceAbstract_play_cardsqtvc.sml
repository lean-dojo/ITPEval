(*
  Statement-only formalization of NTP4VC corpus artifact
  pearl/patience_PatienceAbstract_play_cardsqtvc: the abstract patience
  solitaire play-cards verification condition, preserving the stack-state
  invariant, card count, prior values, and values appended from the input.
  This file contains no proof.
*)

open HolKernel Parse boolLib bossLib;
open integerTheory listTheory;

Datatype:
  patience_play_cards_state =
    PatiencePlayCardsState
      int
      int
      (int -> int)
      (int -> int)
      (int -> int -> int)
      (int -> int # int)
      (int -> int)
End

val patience_play_cards_num_stacks_def = Define `
  patience_play_cards_num_stacks
    (PatiencePlayCardsState
       num_stacks num_elts values stack_sizes stacks positions preds) =
    num_stacks`;

val patience_play_cards_num_elts_def = Define `
  patience_play_cards_num_elts
    (PatiencePlayCardsState
       num_stacks num_elts values stack_sizes stacks positions preds) =
    num_elts`;

val patience_play_cards_values_def = Define `
  patience_play_cards_values
    (PatiencePlayCardsState
       num_stacks num_elts values stack_sizes stacks positions preds) =
    values`;

val patience_play_cards_stack_sizes_def = Define `
  patience_play_cards_stack_sizes
    (PatiencePlayCardsState
       num_stacks num_elts values stack_sizes stacks positions preds) =
    stack_sizes`;

val patience_play_cards_stacks_def = Define `
  patience_play_cards_stacks
    (PatiencePlayCardsState
       num_stacks num_elts values stack_sizes stacks positions preds) =
    stacks`;

val patience_play_cards_positions_def = Define `
  patience_play_cards_positions
    (PatiencePlayCardsState
       num_stacks num_elts values stack_sizes stacks positions preds) =
    positions`;

val patience_play_cards_preds_def = Define `
  patience_play_cards_preds
    (PatiencePlayCardsState
       num_stacks num_elts values stack_sizes stacks positions preds) =
    preds`;

val patience_play_cards_to_num_def = Define `
  patience_play_cards_to_num (z : int) =
    if z < (0 : int) then 0 else Num z`;

val patience_play_cards_nth_def = Define `
  patience_play_cards_nth (xs : int list) (i : int) =
    if patience_play_cards_to_num i < LENGTH xs
    then EL (patience_play_cards_to_num i) xs
    else (0 : int)`;

val patience_play_cards_update_def = Define `
  patience_play_cards_update
    (f : int -> int) (key : int) (value : int) =
    \query. if query = key then value else f query`;

val patience_play_cards_inv_def = Define `
  patience_play_cards_inv (s : patience_play_cards_state) <=>
    ((0 : int) <= patience_play_cards_num_stacks s /\
     patience_play_cards_num_stacks s <=
       patience_play_cards_num_elts s) /\
    ((0 : int) < patience_play_cards_num_elts s ==>
     (0 : int) < patience_play_cards_num_stacks s) /\
    (!i : int.
       (0 : int) <= i /\
       i < patience_play_cards_num_stacks s ==>
       (1 : int) <= patience_play_cards_stack_sizes s i /\
       !j : int.
         (0 : int) <= j /\
         j < patience_play_cards_stack_sizes s i ==>
         (0 : int) <= patience_play_cards_stacks s i j /\
         patience_play_cards_stacks s i j <
           patience_play_cards_num_elts s) /\
    (!i : int.
       (0 : int) <= i /\
       i < patience_play_cards_num_elts s ==>
       let pos = patience_play_cards_positions s i
       in
         ((0 : int) <= FST pos /\
          FST pos < patience_play_cards_num_stacks s) /\
         ((0 : int) <= SND pos /\
          SND pos <
            patience_play_cards_stack_sizes s (FST pos)) /\
         patience_play_cards_stacks s (FST pos) (SND pos) = i) /\
    (!is : int.
       (0 : int) <= is /\
       is < patience_play_cards_num_stacks s ==>
       !ip : int.
         (0 : int) <= ip /\
         ip < patience_play_cards_stack_sizes s is ==>
         (is,ip) =
           patience_play_cards_positions
             s (patience_play_cards_stacks s is ip)) /\
    (!i : int.
       (0 : int) <= i /\
       i < patience_play_cards_num_stacks s ==>
       !j k : int.
         (0 : int) <= j /\
         j < k /\
         k < patience_play_cards_stack_sizes s i ==>
         patience_play_cards_stacks s i j <
           patience_play_cards_stacks s i k) /\
    (!i : int.
       (0 : int) <= i /\
       i < patience_play_cards_num_stacks s ==>
       !j k : int.
         (0 : int) <= j /\
         j <= k /\
         k < patience_play_cards_stack_sizes s i ==>
         patience_play_cards_values
           s (patience_play_cards_stacks s i k) <=
         patience_play_cards_values
           s (patience_play_cards_stacks s i j)) /\
    (!i : int.
       (0 : int) <= i /\
       i < patience_play_cards_num_elts s ==>
       let pred = patience_play_cards_preds s i
       in
         -(1 : int) <= pred /\
         pred < patience_play_cards_num_elts s /\
         pred < i /\
         let pos = patience_play_cards_positions s i
         in
           if pred < (0 : int) then
             FST pos = (0 : int)
           else
             patience_play_cards_values s pred <
               patience_play_cards_values s i /\
             (0 : int) < FST pos /\
             FST (patience_play_cards_positions s pred) =
               FST pos - (1 : int))`;

val patience_PatienceAbstract_play_cards_vc =
  ``!s : patience_play_cards_state.
    !input : int list.
      patience_play_cards_inv s ==>
      case input of
        [] =>
          patience_play_cards_inv s /\
          patience_play_cards_num_elts s =
            patience_play_cards_num_elts s + &(LENGTH input) /\
          (!i : int.
             patience_play_cards_num_elts s <= i /\
             i < patience_play_cards_num_elts s ==>
             patience_play_cards_values s i =
               patience_play_cards_nth
                 input
                 (i - patience_play_cards_num_elts s))
      | c :: rest =>
          patience_play_cards_inv s /\
          !s1 : patience_play_cards_state.
            patience_play_cards_inv s1 /\
            patience_play_cards_num_elts s1 =
              patience_play_cards_num_elts s + (1 : int) /\
            patience_play_cards_values s1 =
              patience_play_cards_update
                (patience_play_cards_values s)
                (patience_play_cards_num_elts s)
                c ==>
            ((case input of
                [] => F
              | _ :: tail => tail = rest) /\
             patience_play_cards_inv s1) /\
            !s2 : patience_play_cards_state.
              patience_play_cards_inv s2 /\
              patience_play_cards_num_elts s2 =
                patience_play_cards_num_elts s1 + &(LENGTH rest) /\
              (!i : int.
                 (0 : int) <= i /\
                 i < patience_play_cards_num_elts s1 ==>
                 patience_play_cards_values s2 i =
                   patience_play_cards_values s1 i) /\
              (!i : int.
                 patience_play_cards_num_elts s1 <= i /\
                 i < patience_play_cards_num_elts s2 ==>
                 patience_play_cards_values s2 i =
                   patience_play_cards_nth
                     rest
                     (i - patience_play_cards_num_elts s1)) ==>
              patience_play_cards_inv s2 /\
              patience_play_cards_num_elts s2 =
                patience_play_cards_num_elts s + &(LENGTH input) /\
              (!i : int.
                 (0 : int) <= i /\
                 i < patience_play_cards_num_elts s ==>
                 patience_play_cards_values s2 i =
                   patience_play_cards_values s i) /\
              (!i : int.
                 patience_play_cards_num_elts s <= i /\
                 i < patience_play_cards_num_elts s2 ==>
                 patience_play_cards_values s2 i =
                   patience_play_cards_nth
                     input
                     (i - patience_play_cards_num_elts s))``;
