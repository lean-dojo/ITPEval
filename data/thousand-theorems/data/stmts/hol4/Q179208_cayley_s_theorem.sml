(*
  Statement-only formalization of the Thousand Theorems corpus artifact
  Q179208, "Cayley's theorem": a group with a faithful action is isomorphic
  to the image of its action homomorphism in the symmetric group. This file
  contains no proof.
*)

open HolKernel Parse boolLib;
open groupTheory pred_setTheory;

val cayley_permutation_group_def = new_definition (
  "cayley_permutation_group_def",
  ``cayley_permutation_group : ('a -> 'a) group =
      <| carrier := {p | BIJ p UNIV UNIV};
              op := (\f g. f o g);
              id := I
       |>``);

val subgroupOfMulAction =
  ``!(g : 'a group) (rho : 'a -> 'b -> 'b).
      Group g /\
      g.carrier = UNIV /\
      action rho g UNIV /\
      (!a b. (!x. rho a x = rho b x) ==> a = b)
      ==>
      GroupIso (\a. rho a) g
        (homo_image (\a. rho a) g
          (cayley_permutation_group : ('b -> 'b) group))``;
