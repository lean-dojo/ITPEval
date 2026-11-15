(*
  Statement-only formalization of Thousand Theorems corpus artifact Q1687147,
  "Sprague–Grundy theorem": every well-founded impartial combinatorial game is
  equivalent to the Nim game indexed by its minimum-excluded Grundy nimber.
  This file contains no proof.
*)

let Q1687147_SPRAGUE_GRUNDY_THEOREM =
  `let is_strict_well_order =
     \(lt:N->N->bool).
       WF lt /\
       (!a:N. ~(lt a a)) /\
       (!a b c:N. lt a b /\ lt b c ==> lt a c) /\
       (!a b:N. lt a b \/ a = b \/ lt b a) in
   let is_mex =
     \(lt:N->N->bool) (s:N->bool) (n:N).
       ~(n IN s) /\ (!m:N. lt m n ==> m IN s) in
   let is_impartial_game_model =
     \(move:A->A->bool) (lt:N->N->bool)
      (nim:N->A) (grundy:A->N) (game_le:A->A->bool).
       WF move /\
       is_strict_well_order lt /\
       (!a:N. !y:A.
          move y (nim a) <=> ?b:N. lt b a /\ y = nim b) /\
       (!x:A.
          is_mex lt
            {n:N | ?y:A. move y x /\ grundy y = n}
            (grundy x)) /\
       (!x y:A.
          game_le x y <=>
          (!u:A. move u x ==> ~(game_le y u)) /\
          (!v:A. move v y ==> ~(game_le v x))) in
   !move:A->A->bool.
   !lt:N->N->bool.
   !nim:N->A.
   !grundy:A->N.
   !game_le:A->A->bool.
     is_impartial_game_model move lt nim grundy game_le
     ==> !x:A.
           game_le (nim (grundy x)) x /\
           game_le x (nim (grundy x))`;;
