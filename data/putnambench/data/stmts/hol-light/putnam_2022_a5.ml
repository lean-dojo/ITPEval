(*
  Statement-only formalization of PutnamBench corpus artifact putnam_2022_a5
  (putnambench__hol-light__putnam_2022_a5): the greatest number of uncovered
  squares Alice can ensure in the 2022-square adjacent-domino game. This file
  contains no proof.
*)

let statement =
  `let board = 0..2021 in
   let is_state =
     \x:num->bool. x SUBSET board in
   let is_valid_move =
     \(x:num->bool) (y:num->bool).
       is_state x /\
       is_state y /\
       ((x = y /\
         (!i:num. i < 2021 /\ ~(i IN x) ==> i + 1 IN x)) \/
        (?i:num.
           i < 2021 /\
           ~(i IN x) /\
           ~((i + 1) IN x) /\
           y = x UNION {i,i + 1})) in
   let is_valid_game =
     \g:(num->bool)list.
       (?gt:(num->bool)list. g = CONS ({}:num->bool) gt) /\
       (!i:num.
          i + 1 < LENGTH g
          ==> is_valid_move (EL i g) (EL (i + 1) g)) in
   let conforms_to_strategy =
     \(g:(num->bool)list) (s:(num->bool)->(num->bool)).
       !i:num.
         i + 1 < LENGTH g /\ EVEN i
         ==> EL (i + 1) g = s (EL i g) in
   let achievable =
     \n:num.
       ?s:(num->bool)->(num->bool).
         (!x:num->bool. is_state x ==> is_valid_move x (s x)) /\
         (!g:(num->bool)list.
            is_valid_game g
            ==> conforms_to_strategy g s
            ==> ?gh:(num->bool)list. ?x:num->bool.
                  g = APPEND gh [x] /\
                  n <= CARD (board DIFF x)) in
   let is_greatest =
     \(values:num->bool) (n:num).
       n IN values /\ (!m:num. m IN values ==> m <= n) in
   is_greatest {n:num | achievable n} 290`;;
