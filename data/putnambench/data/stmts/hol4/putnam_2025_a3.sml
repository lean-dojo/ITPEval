(*
  Statement-only formalization of PutnamBench corpus artifact putnam_2025_a3
  (putnambench__hol4__putnam_2025_a3): Alice has no winning strategy in the
  non-repeating ternary-string game for any positive string length. This file
  contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory listTheory;

val putnam_2025_a3 =
  ``let initial_state = \i : num. 0 in
    let game_string =
      \n : num. \(s : num -> num).
        !i : num. if i < n then s i < 3 else s i = 0
    in
    let legal_move =
      \n : num. \(s : num -> num) (t : num -> num).
        game_string n s /\
        game_string n t /\
        ?i : num.
          i < n /\
          ~(s i = t i) /\
          (!j : num. j < n /\ ~(s j = t j) ==> j = i) /\
          (s i + 1 = t i \/ t i + 1 = s i)
    in
    let valid_play =
      \n : num. \(play : (num -> num) list).
        (!k : num.
           k < LENGTH play
           ==>
           game_string n (EL k play)) /\
        (!k : num.
           k < LENGTH play
           ==>
           legal_move n
             (if k = 0 then initial_state else EL (k - 1) play)
             (EL k play)) /\
        (!i j : num.
           i < LENGTH (CONS initial_state play) /\
           j < LENGTH (CONS initial_state play) /\
           EL i (CONS initial_state play) =
             EL j (CONS initial_state play)
           ==>
           i = j)
    in
    let has_winning_strategy =
      \n : num. \(play : (num -> num) list).
        !winning : (num -> num) list -> bool.
          (!p : (num -> num) list.
             (?s : num -> num.
                valid_play n (APPEND p [s]) /\
                (!t : num -> num.
                   valid_play n (APPEND p [s; t])
                   ==>
                   winning (APPEND p [s; t])))
             ==>
             winning p)
          ==>
          winning play
    in
    let putnam_2025_a3_solution = \n : num. F in
      !n : num.
        1 <= n
        ==>
        (putnam_2025_a3_solution n <=>
         has_winning_strategy n [])``;
