(*
  Statement-only formalization of the Thousand Theorems corpus artifact
  Q1687147, "Sprague–Grundy theorem": every well-founded impartial game is
  equivalent to the Nim game indexed by its recursively defined Grundy
  ordinal. This file contains no proof.
*)

open HolKernel Parse boolLib;
open pairTheory pred_setTheory relationTheory sumTheory;
open ordinalBasicTheory;

val q1687147_mex_def = new_definition (
  "q1687147_mex_def",
  ``q1687147_mex (s : 'a ordinal set) = oleast a. a NOTIN s``
);

val q1687147_grundy_def = new_definition (
  "q1687147_grundy_def",
  ``q1687147_grundy (move : 'a -> 'a -> bool) =
      (WFREC move
        (\rec g. q1687147_mex (IMAGE rec {h | move h g}))
        : 'a -> 'a ordinal)``
);

val q1687147_sum_move_def = new_definition (
  "q1687147_sum_move_def",
  ``q1687147_sum_move
      (move : 'a -> 'a -> bool)
      (child : 'a + 'a ordinal)
      (parent : 'a + 'a ordinal) <=>
      (?g h.
        child = INL g /\ parent = INL h /\ move g h) \/
      (?b a.
        child = INR b /\ parent = INR a /\ b < a)``
);

val q1687147_pair_step_def = new_definition (
  "q1687147_pair_step_def",
  ``q1687147_pair_step
      (move : 'a -> 'a -> bool)
      (child : 'a # 'a)
      (parent : 'a # 'a) <=>
      (move (FST child) (FST parent) /\
       SND child = SND parent) \/
      (FST child = FST parent /\
       move (SND child) (SND parent))``
);

val q1687147_order_state_step_def = new_definition (
  "q1687147_order_state_step_def",
  ``q1687147_order_state_step
      (move : 'a -> 'a -> bool)
      (child : ('a # 'a) # bool)
      (parent : ('a # 'a) # bool) <=>
      q1687147_pair_step move (FST child) (FST parent)``
);

val q1687147_game_order_aux_def = new_definition (
  "q1687147_game_order_aux_def",
  ``q1687147_game_order_aux (move : 'a -> 'a -> bool) =
      WFREC (q1687147_order_state_step move)
        (\rec state.
          let g = FST (FST state) in
          let h = SND (FST state) in
            if SND state then
              (!g'. move g' g ==> ~rec ((g', h), F)) /\
              (!h'. move h' h ==> ~rec ((g, h'), F))
            else
              (!h'. move h' h ==> ~rec ((g, h'), T)) /\
              (!g'. move g' g ==> ~rec ((g', h), T)))``
);

val q1687147_game_le_def = new_definition (
  "q1687147_game_le_def",
  ``q1687147_game_le (move : 'a -> 'a -> bool) g h <=>
      q1687147_game_order_aux move ((g, h), T)``
);

val q1687147_game_equiv_def = new_definition (
  "q1687147_game_equiv_def",
  ``q1687147_game_equiv (move : 'a -> 'a -> bool) g h <=>
      q1687147_game_le move g h /\
      q1687147_game_le move h g``
);

val IGame_Impartial_nim_grundy_equiv =
  ``!(move : 'a -> 'a -> bool) x.
      WF move
      ==>
      q1687147_game_equiv
        (q1687147_sum_move move)
        (INR (q1687147_grundy move x))
        (INL x)``;
