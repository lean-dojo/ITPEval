(*
  Statement-only formalization of NTP4VC corpus artifact
  pearl/patience_PatienceAbstract_play_gameqtvc: the verification condition
  for an abstract patience-solitaire game, relating the final stack count to
  the maximum length of a strictly increasing input subsequence. This file
  contains no proof.
*)

open HolKernel Parse boolLib;
open integerTheory listTheory pairTheory;

val patience_PatienceAbstract_play_game_vc =
  ``let pg_to_num =
      \z : int. if z < (0 : int) then 0 else Num z
    in
    let pg_nth =
      \xs : int list. \i : int.
        if pg_to_num i < LENGTH xs
        then EL (pg_to_num i) xs
        else (0 : int)
    in
    let pg_update =
      \f : int -> int. \key value query : int.
        if query = key then value else f query
    in
    let pg_inv =
      \num_stacks num_elts : int.
      \values stack_sizes : int -> int.
      \stacks : int -> int -> int.
      \positions : int -> int # int.
      \preds : int -> int.
        ((0 : int) <= num_stacks /\ num_stacks <= num_elts) /\
        ((0 : int) < num_elts ==> (0 : int) < num_stacks) /\
        (!i : int.
           (0 : int) <= i /\ i < num_stacks ==>
           (1 : int) <= stack_sizes i /\
           !j : int.
             (0 : int) <= j /\ j < stack_sizes i ==>
             (0 : int) <= stacks i j /\ stacks i j < num_elts) /\
        (!i : int.
           (0 : int) <= i /\ i < num_elts ==>
           let pos = positions i
           in
             ((0 : int) <= FST pos /\ FST pos < num_stacks) /\
             ((0 : int) <= SND pos /\
              SND pos < stack_sizes (FST pos) /\
              stacks (FST pos) (SND pos) = i)) /\
        (!is : int.
           (0 : int) <= is /\ is < num_stacks ==>
           !ip : int.
             (0 : int) <= ip /\ ip < stack_sizes is ==>
             (is,ip) = positions (stacks is ip)) /\
        (!i : int.
           (0 : int) <= i /\ i < num_stacks ==>
           !j k : int.
             (0 : int) <= j /\ j < k /\ k < stack_sizes i ==>
             stacks i j < stacks i k) /\
        (!i : int.
           (0 : int) <= i /\ i < num_stacks ==>
           !j k : int.
             (0 : int) <= j /\ j <= k /\ k < stack_sizes i ==>
             values (stacks i k) <= values (stacks i j)) /\
        (!i : int.
           (0 : int) <= i /\ i < num_elts ==>
           let pred = preds i
           in
             (~1 : int) <= pred /\
             pred < num_elts /\
             pred < i /\
             let pos = positions i
             in
               if pred < (0 : int) then
                 FST pos = (0 : int)
               else
                 values pred < values i /\
                 (0 : int) < FST pos /\
                 FST (positions pred) = FST pos - (1 : int))
    in
    let pg_increasing_subsequence =
      \seq_len : int.
      \seq_val : int -> int.
      \input : int list.
        ((0 : int) <= seq_len /\ seq_len <= &(LENGTH input)) /\
        ((!i : int.
            (0 : int) <= i /\ i < seq_len ==>
            (0 : int) <= seq_val i /\
            seq_val i < &(LENGTH input)) /\
         (!i j : int.
            (0 : int) <= i /\ i < j /\ j < seq_len ==>
            seq_val i < seq_val j)) /\
        (!i j : int.
           (0 : int) <= i /\ i < j /\ j < seq_len ==>
           pg_nth input (seq_val i) < pg_nth input (seq_val j))
    in
    let pg_maximal_subsequence =
      \num_stacks : int. \input : int list.
        (?seq_len : int.
         ?seq_val : int -> int.
           seq_len = num_stacks /\
           pg_increasing_subsequence seq_len seq_val input) /\
        (!seq_len : int.
         !seq_val : int -> int.
           pg_increasing_subsequence seq_len seq_val input ==>
           seq_len <= num_stacks)
    in
    let pg_loop_inv =
      \num_elts : int.
      \values : int -> int.
      \positions : int -> int # int.
      \ns i : int.
      \sequence : int -> int.
      \index : int.
        ((~1 : int) <= index /\ index < num_elts) /\
        ((0 : int) <= i ==>
         (0 : int) <= index /\ FST (positions index) = i) /\
        (i + (1 : int) < ns ==>
         index < sequence (i + (1 : int))) /\
        (((0 : int) <= i /\ i < ns - (1 : int)) ==>
         values index < values (sequence (i + (1 : int)))) /\
        (!j : int.
           i < j /\ j < ns ==>
           (0 : int) <= sequence j /\ sequence j < num_elts) /\
        (!j k : int.
           i < j /\ j < k /\ k < ns ==>
           sequence j < sequence k) /\
        (!j k : int.
           i < j /\ j < k /\ k < ns ==>
           values (sequence j) < values (sequence k))
    in
    let pg_loop_preservation =
      \num_elts : int.
      \values : int -> int.
      \positions : int -> int # int.
      \preds : int -> int.
      \ns upper : int.
      \sequence : int -> int.
      \index : int.
        !i : int.
          (i <= upper /\ (0 : int) <= i) /\
          pg_loop_inv num_elts values positions ns i sequence index ==>
          pg_loop_inv
            num_elts
            values
            positions
            ns
            (i - (1 : int))
            (pg_update sequence i index)
            (preds index)
    in
    let pg_loop_obligations =
      \num_stacks num_elts : int.
      \values : int -> int.
      \positions : int -> int # int.
      \preds : int -> int.
      \input : int list.
      \ns upper : int.
        !sequence : int -> int.
        !index : int.
          pg_loop_preservation
            num_elts values positions preds ns upper sequence index /\
          (pg_loop_inv
             num_elts
             values
             positions
             ns
             ((0 : int) - (1 : int))
             sequence
             index ==>
           pg_maximal_subsequence num_stacks input)
    in
    let pg_nonempty_branch =
      \num_stacks num_elts : int.
      \values stack_sizes : int -> int.
      \stacks : int -> int -> int.
      \positions : int -> int # int.
      \preds : int -> int.
      \input : int list.
        let ns = num_stacks
        in
        let top_index =
          stacks
            (ns - (1 : int))
            (stack_sizes (ns - (1 : int)) - (1 : int))
        in
        let empty_sequence = \i : int. (~1 : int)
        in
        let upper = ns - (1 : int)
        in
          ((0 : int) - (1 : int) <= upper ==>
           pg_loop_inv
             num_elts
             values
             positions
             ns
             upper
             empty_sequence
             top_index /\
           pg_loop_obligations
             num_stacks
             num_elts
             values
             positions
             preds
             input
             ns
             upper) /\
          (upper < (0 : int) - (1 : int) ==>
           pg_maximal_subsequence num_stacks input)
    in
    let pg_final_state =
      \input : int list.
      \num_stacks num_elts : int.
      \values stack_sizes : int -> int.
      \stacks : int -> int -> int.
      \positions : int -> int # int.
      \preds : int -> int.
        pg_inv
          num_stacks
          num_elts
          values
          stack_sizes
          stacks
          positions
          preds /\
        num_elts = (0 : int) + &(LENGTH input) /\
        (!i : int.
           (0 : int) <= i /\ i < (0 : int) ==>
           values i = (~1 : int)) /\
        (!i : int.
           (0 : int) <= i /\ i < num_elts ==>
           values i = pg_nth input (i - (0 : int)))
    in
      !input : int list.
        pg_inv
          (0 : int)
          (0 : int)
          (\i : int. (~1 : int))
          (\i : int. (0 : int))
          (\i : int. \j : int. (~1 : int))
          (\i : int. ((~1 : int),(~1 : int)))
          (\i : int. (~1 : int)) /\
        !num_stacks num_elts : int.
        !values stack_sizes : int -> int.
        !stacks : int -> int -> int.
        !positions : int -> int # int.
        !preds : int -> int.
          pg_final_state
            input
            num_stacks
            num_elts
            values
            stack_sizes
            stacks
            positions
            preds ==>
          if num_stacks = (0 : int) then
            pg_maximal_subsequence num_stacks input
          else
            pg_nonempty_branch
              num_stacks
              num_elts
              values
              stack_sizes
              stacks
              positions
              preds
              input``;
