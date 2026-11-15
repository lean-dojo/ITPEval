(*
  Statement-only formalization of PutnamBench corpus artifact putnam_2018_b1
  (putnambench__hol-light__putnam_2018_b1): classification of the integer
  grid points whose removal leaves two equal-size parts with equal coordinate
  sums. This file contains no proof.
*)

let statement =
  `let P =
     {w:int#int |
        &0 <= FST w /\ FST w <= &2 /\
        &0 <= SND w /\ SND w <= &100} in
   let solution =
     {w:int#int |
        FST w = &1 /\
        &0 <= SND w /\ SND w <= &100 /\
        ?k:int. SND w = &2 * k} in
   !v:int#int.
     (v IN P /\
      (?Q R:(int#int)->bool.
         FINITE Q /\
         FINITE R /\
         Q UNION R = P DELETE v /\
         DISJOINT Q R /\
         CARD Q = CARD R /\
         sum Q (\q:int#int. real_of_int (FST q)) =
         sum R (\r:int#int. real_of_int (FST r)) /\
         sum Q (\q:int#int. real_of_int (SND q)) =
         sum R (\r:int#int. real_of_int (SND r))))
     <=> v IN solution`;;
