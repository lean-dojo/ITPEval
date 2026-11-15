(*
  Statement-only formalization of PutnamBench corpus artifact putnam_2023_a6:
  the positive game sizes are exactly those for which Bob has a strategy
  satisfying the specified validity and conformance conditions that forces a
  fixed parity for the fixed points of every valid play. This file contains no
  proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory listTheory pred_setTheory;

val putnam_2023_a6 =
  ``let valid_game =
      \g : num list.
        ALL_DISTINCT g /\
        (!x : num.
           MEM x g
           ==>
           1 <= x /\ x <= LENGTH g)
    in
    let parity_of =
      \g : num list.
        CARD
          {i : num |
             i < LENGTH g /\
             EL i g = i + 1} MOD 2
    in
    let conforms_to_strategy =
      \g : num list.
      \s : num list -> num.
        !i : num.
          i < LENGTH g /\ ODD i
          ==>
          EL i g = s (TAKE i g)
    in
    let valid_history =
      \n : num.
      \g : num list.
        ODD (LENGTH g) /\
        LENGTH g < n /\
        ALL_DISTINCT g /\
        (!x : num.
           MEM x g
           ==>
           1 <= x /\ x <= n)
    in
    let valid_strategy =
      \n : num.
      \s : num list -> num.
        !g : num list.
          valid_history n g
          ==>
          1 <= s g /\ s g <= n /\ ~MEM (s g) g
    in
    let winning_for =
      \n : num.
      \s : num list -> num.
        valid_strategy n s /\
        ?p : num.
          p < 2 /\
          !g : num list.
            LENGTH g = n /\
            valid_game g /\
            conforms_to_strategy g s
            ==>
            parity_of g = p
    in
      {n : num | 0 < n /\ ?s : num list -> num. winning_for n s} =
      {n : num | 0 < n}``;
