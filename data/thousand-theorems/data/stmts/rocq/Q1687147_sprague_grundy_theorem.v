(*
  Statement-only formalization of Thousand Theorems corpus artifact Q1687147
  (thousand-theorems__rocq__Q1687147), "Sprague-Grundy theorem": every
  impartial well-founded normal-play game is equivalent to the canonical game
  of Nim at its Grundy nimber. This file contains no proof.
*)

From Stdlib Require Import Wellfounded.

Set Universe Polymorphism.
Set Implicit Arguments.

Inductive q1687147_player : Type :=
| q1687147_left
| q1687147_right.

Definition q1687147_other (p : q1687147_player) : q1687147_player :=
  match p with
  | q1687147_left => q1687147_right
  | q1687147_right => q1687147_left
  end.

Record q1687147_game_system : Type := {
  q1687147_game : Type;
  q1687147_move :
    q1687147_player -> q1687147_game -> q1687147_game -> Prop;
  q1687147_move_well_founded :
    well_founded
      (fun child parent : q1687147_game =>
        exists p : q1687147_player,
          q1687147_move p parent child);
  q1687147_neg :
    q1687147_game -> q1687147_game;
  q1687147_neg_moves :
    forall (p : q1687147_player)
           (x y : q1687147_game),
      q1687147_move p (q1687147_neg x) y <->
      exists z : q1687147_game,
        q1687147_move (q1687147_other p) x z /\
        y = q1687147_neg z
}.

Arguments q1687147_game _ : clear implicits.
Arguments q1687147_move _ _ _ _ : assert.
Arguments q1687147_neg _ _ : assert.

(* Winning in the disjunctive sum of two games: on one's own turn one may
   move in either component, while on the opponent's turn every legal reply
   must leave a winning position. *)
Inductive q1687147_sum_wins
    (S : q1687147_game_system)
    (winner : q1687147_player) :
    q1687147_player ->
    q1687147_game S ->
    q1687147_game S ->
    Prop :=
| q1687147_sum_wins_move_first :
    forall x x' z : q1687147_game S,
      q1687147_move S winner x x' ->
      q1687147_sum_wins S winner (q1687147_other winner) x' z ->
      q1687147_sum_wins S winner winner x z
| q1687147_sum_wins_move_second :
    forall x z z' : q1687147_game S,
      q1687147_move S winner z z' ->
      q1687147_sum_wins S winner (q1687147_other winner) x z' ->
      q1687147_sum_wins S winner winner x z
| q1687147_sum_wins_opponent_turn :
    forall x z : q1687147_game S,
      (forall x' : q1687147_game S,
        q1687147_move S (q1687147_other winner) x x' ->
        q1687147_sum_wins S winner winner x' z) ->
      (forall z' : q1687147_game S,
        q1687147_move S (q1687147_other winner) z z' ->
        q1687147_sum_wins S winner winner x z') ->
      q1687147_sum_wins S winner (q1687147_other winner) x z.

Definition q1687147_game_equiv
    (S : q1687147_game_system)
    (x y : q1687147_game S) : Prop :=
  forall (context : q1687147_game S)
         (winner turn : q1687147_player),
    q1687147_sum_wins S winner turn x context <->
    q1687147_sum_wins S winner turn y context.

Inductive q1687147_impartial
    (S : q1687147_game_system) :
    q1687147_game S -> Prop :=
| q1687147_impartial_intro :
    forall x : q1687147_game S,
      q1687147_game_equiv S (q1687147_neg S x) x ->
      (forall (p : q1687147_player) (y : q1687147_game S),
        q1687147_move S p x y ->
        q1687147_impartial S y) ->
      q1687147_impartial S x.

Record q1687147_nimber_model
    (S : q1687147_game_system) : Type := {
  q1687147_nimber : Type;
  q1687147_nimber_lt :
    q1687147_nimber -> q1687147_nimber -> Prop;
  q1687147_nimber_lt_well_founded :
    well_founded q1687147_nimber_lt;
  q1687147_nimber_lt_irrefl :
    forall a : q1687147_nimber,
      ~ q1687147_nimber_lt a a;
  q1687147_nimber_lt_trans :
    forall a b c : q1687147_nimber,
      q1687147_nimber_lt a b ->
      q1687147_nimber_lt b c ->
      q1687147_nimber_lt a c;
  q1687147_nimber_lt_total :
    forall a b : q1687147_nimber,
      a = b \/
      q1687147_nimber_lt a b \/
      q1687147_nimber_lt b a;

  q1687147_grundy :
    q1687147_game S -> q1687147_nimber;
  q1687147_grundy_excluded :
    forall x : q1687147_game S,
      ~ exists y : q1687147_game S,
          q1687147_move S q1687147_right x y /\
          q1687147_grundy y = q1687147_grundy x;
  q1687147_grundy_covers_lower :
    forall (x : q1687147_game S) (a : q1687147_nimber),
      q1687147_nimber_lt a (q1687147_grundy x) ->
      exists y : q1687147_game S,
        q1687147_move S q1687147_right x y /\
        q1687147_grundy y = a;
  q1687147_grundy_least_excluded :
    forall (x : q1687147_game S) (a : q1687147_nimber),
      (~ exists y : q1687147_game S,
          q1687147_move S q1687147_right x y /\
          q1687147_grundy y = a) ->
      q1687147_grundy x = a \/
      q1687147_nimber_lt (q1687147_grundy x) a;

  q1687147_nim :
    q1687147_nimber -> q1687147_game S;
  q1687147_nim_moves :
    forall (p : q1687147_player)
           (a : q1687147_nimber)
           (y : q1687147_game S),
      q1687147_move S p (q1687147_nim a) y <->
      exists b : q1687147_nimber,
        q1687147_nimber_lt b a /\
        y = q1687147_nim b
}.

Arguments q1687147_nimber {_} _.
Arguments q1687147_grundy {_} _ _.
Arguments q1687147_nim {_} _ _.

Theorem q1687147_nim_grundy_equiv :
  forall (S : q1687147_game_system)
         (N : q1687147_nimber_model S)
         (x : q1687147_game S),
    q1687147_impartial S x ->
    q1687147_game_equiv S
      (q1687147_nim N (q1687147_grundy N x))
      x.
Admitted.
