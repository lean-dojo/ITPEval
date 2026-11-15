-- Statement-only formalization of Logipedia corpus artifact
-- "permutation.let_clause_1068" (catalog title "permutation.let_clause_1068"):
-- under repeated boundedness, image, closure, injectivity, and equality
-- assumptions, a bounded permutation maps a to its specified value i.
-- This file contains no proof.

namespace permutation

def injn (f : Nat → Nat) (n : Nat) : Prop :=
  ∀ i j : Nat, i ≤ n → j ≤ n → f i = f j → i = j

def permut (f : Nat → Nat) (n : Nat) : Prop :=
  (∀ i : Nat, i ≤ n → f i ≤ n) ∧ injn f n

theorem let_clause_1068 :
    ∀ (f : Nat → Nat) (n : Nat),
      permut f n →
        ∀ i j : Nat,
          i ≤ n →
            j ≤ n →
              ∀ a : Nat,
                (a ≤ n ∧ f a = i) →
                  a ≤ n →
                    f a = i →
                      ∀ b : Nat,
                        (b ≤ n ∧ f b = j) →
                          b ≤ n →
                            f b = j →
                              (∀ i0 : Nat, i0 ≤ n → f i0 ≤ n) →
                                injn f n →
                                  a = b →
                                    f a = i := sorry

end permutation
