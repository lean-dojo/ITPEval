-- Statement-only formalization of Logipedia corpus artifact
-- "permutation.eq_to_bijn" (catalog title "permutation.eq_to_bijn"):
-- bounded surjectivity of natural-number functions on an initial segment is
-- preserved when two functions agree throughout that initial segment.
-- This file contains no proof.

namespace permutation

def bijn (f : Nat -> Nat) (n : Nat) : Prop :=
  forall m : Nat, m <= n -> Exists fun p : Nat => And (p <= n) (f p = m)

theorem eq_to_bijn :
    forall (f g : Nat -> Nat) (n : Nat),
      (forall i : Nat, i <= n -> f i = g i) ->
        bijn f n ->
          bijn g n := sorry

end permutation
