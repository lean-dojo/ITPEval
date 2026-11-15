(*
  Statement-only formalization of PutnamBench corpus artifact putnam_2021_a1:
  the least number of length-five hops between integer-coordinate points needed
  to travel from (0,0) to (2021,2021) is 578. This file contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory integerTheory listTheory pairTheory;

val putnam_2021_a1 =
  ``let hop =
      \P Q : int # int.
        (FST P - FST Q) * (FST P - FST Q) +
        (SND P - SND Q) * (SND P - SND Q) =
        25
    in
    let valid_path =
      \path : (int # int) list.
        path <> [] /\
        HD path = (0, 0) /\
        LAST path = (2021, 2021) /\
        !i : num.
          SUC i < LENGTH path
          ==>
          hop (EL i path) (EL (SUC i) path)
    in
      (LEAST k : num.
         ?path : (int # int) list.
           valid_path path /\ LENGTH path = k + 1) =
      578``;
