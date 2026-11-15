(*
  Statement-only formalization of PutnamBench artifact putnam_1975_a1:
  equivalence between representing an integer as a sum of two triangular
  numbers and representing four times it plus one as a sum of two squares,
  with explicit forward witnesses. This file contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory integerTheory;

val putnam_1975_a1 =
  ``let solution =
      ((\a b : int. a + b + 1),
       (\a b : int. a - b))
    in
    let nab =
      \n a b : int.
        2 * n = a ** 2 + a + b ** 2 + b
    in
    let nxy =
      \n x y : int.
        4 * n + 1 = x ** 2 + y ** 2
    in
      (!n a b : int.
         nab n a b
         ==>
         nxy n ((FST solution) a b) ((SND solution) a b)) /\
      (!n : int.
         (?x y : int. nxy n x y)
         ==>
         ?a b : int. nab n a b)``;
