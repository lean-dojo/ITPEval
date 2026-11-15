-- Statement-only formalization of Logipedia corpus artifact
-- "permutation.permut_S_to_permut_transpose" (catalog title
-- "permutation.permut_S_to_permut_transpose"): swapping the image of the new
-- endpoint with that endpoint turns a permutation through m + 1 into a
-- permutation through m. This file contains no proof.

namespace permutation

def injn (f : Nat -> Nat) (n : Nat) : Prop :=
  forall i j : Nat, i <= n -> j <= n -> f i = f j -> i = j

def permut (f : Nat -> Nat) (n : Nat) : Prop :=
  (forall i : Nat, i <= n -> f i <= n) /\ injn f n

def transpose (i j n : Nat) : Nat :=
  if n = i then j else if n = j then i else n

theorem permut_S_to_permut_transpose :
    forall (f : Nat -> Nat) (m : Nat),
      permut f (Nat.succ m) ->
        permut
          (fun n : Nat => transpose (f (Nat.succ m)) (Nat.succ m) (f n))
          m := sorry

end permutation
