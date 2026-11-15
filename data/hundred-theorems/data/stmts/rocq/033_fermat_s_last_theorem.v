(*
  Statement-only formalization of "Fermat's Last Theorem" from Hundred Theorems item 033. This
  file contains no proof.
*)

Require Import Arith.

Theorem fermats_last_theorem :
  forall n a b c : nat,
    2 < n ->
    0 < a ->
    0 < b ->
    0 < c ->
    a ^ n + b ^ n <> c ^ n.
Admitted.
