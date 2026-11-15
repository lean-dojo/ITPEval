(*
  Statement-only formalization of the Thousand Theorems corpus artifact
  Q474881, "Cantor's theorem": no function from an arbitrary carrier to its
  powerset is surjective. This file contains no proof.
*)

open HolKernel Parse boolLib;

val cantor_surjective =
  ``!(A : 'a -> bool) (f : 'a -> 'a -> bool).
      ~(!s : 'a -> bool.
          (!x : 'a. s x ==> A x) ==>
          ?a : 'a.
            A a /\
            !x : 'a. A x ==> (f a x <=> s x))``;
