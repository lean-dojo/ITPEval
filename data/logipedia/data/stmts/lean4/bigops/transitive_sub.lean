-- Statement-only formalization of Logipedia corpus artifact "bigops.transitive_sub"
-- (catalog title "bigops.transitive_sub"): transitivity of bounded correspondences
-- preserving Boolean-selected indices. The final two source parameters are retained
-- even though the source definition does not inspect them. This file contains no proof.

namespace bigops

def sub_hk
    (h k : Nat -> Nat) (n1 n2 : Nat) (p1 p2 : Nat -> Bool)
    (f1 f2 : Nat -> Nat) : Prop :=
  forall i : Nat, i < n1 -> p1 i = true ->
    ((h i < n2 /\ p2 (h i) = true) /\ k (h i) = i)

theorem transitive_sub
    (h1 k1 h2 k2 : Nat -> Nat) (n1 n2 n3 : Nat)
    (p1 p2 p3 : Nat -> Bool) (f1 f2 f3 : Nat -> Nat)
    (hsub1 : sub_hk h1 k1 n1 n2 p1 p2 f1 f2)
    (hsub2 : sub_hk h2 k2 n2 n3 p2 p3 f2 f3) :
    sub_hk (fun x => h2 (h1 x)) (fun x => k1 (k2 x))
      n1 n3 p1 p3 f1 f3 := sorry

end bigops
