(*
  Statement-only formalization of PutnamBench corpus artifact putnam_2023_a6
  (putnambench__hol-light__putnam_2023_a6): Bob has a winning parity strategy
  in the alternating permutation game for every positive n. This file contains
  no proof.
*)

let statement =
  `let legal_sequence =
     \(n:num) (g:num list).
       (!i:num.
          i < LENGTH g
          ==> 1 <= EL i g /\ EL i g <= n) /\
       (!i:num. !j:num.
          i < LENGTH g /\ j < LENGTH g /\ EL i g = EL j g
          ==> i = j) in
   let valid_game =
     \(n:num) (g:num list).
       LENGTH g = n /\ legal_sequence n g in
   let conforms_to_strategy =
     \(g:num list) (s:num list->num).
       !h:num list. !x:num. !t:num list.
         g = APPEND h (CONS x t) /\ ODD (LENGTH h)
         ==> x = s h in
   let valid_strategy =
     \(n:num) (s:num list->num).
       !g:num list.
         legal_sequence n g /\
         ODD (LENGTH g) /\
         LENGTH g < n
         ==> 1 <= s g /\ s g <= n /\ ~MEM (s g) g in
   let odd_match_parity =
     \(g:num list).
       ODD (CARD {i:num | i < LENGTH g /\ EL i g = i + 1}) in
   let winning_strategy =
     \(n:num) (s:num list->num).
       valid_strategy n s /\
       ?goal_is_odd:bool.
         !g:num list.
           valid_game n g /\ conforms_to_strategy g s
           ==> (odd_match_parity g <=> goal_is_odd) in
   {n:num | 0 < n /\ ?s:num list->num. winning_strategy n s} =
   {n:num | 0 < n}`;;
