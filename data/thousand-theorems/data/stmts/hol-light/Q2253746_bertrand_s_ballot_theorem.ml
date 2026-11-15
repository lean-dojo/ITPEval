(*
  Statement-only formalization of Thousand Theorems corpus artifact Q2253746,
  "Bertrand's ballot theorem": among lists with p entries equal to +1 and q
  entries equal to -1, the uniform probability that every nonempty suffix has
  positive sum is (p - q) / (p + q) when q < p. This file contains no proof.
*)

let Q2253746_BERTRANDS_BALLOT_THEOREM =
  `let counted_sequence =
     \p:num. \q:num. \l:int list.
       LENGTH (FILTER (\x:int. x = &1) l) = p /\
       LENGTH (FILTER (\x:int. x = -- &1) l) = q /\
       ALL (\x:int. x = &1 \/ x = -- &1) l in
   let stays_positive =
     \l:int list.
       !s:int list.
         ~(s = []) /\
         (?prefix:int list. l = APPEND prefix s)
         ==> &0 < ITLIST (+) s (&0) in
   !q p:num.
     q < p
     ==>
     let sequences =
       {l:int list | counted_sequence p q l} in
     let positive_sequences =
       {l:int list | l IN sequences /\ stays_positive l} in
     ((&(CARD positive_sequences) / &(CARD sequences)):real) =
     (&p - &q) / (&p + &q)`;;
