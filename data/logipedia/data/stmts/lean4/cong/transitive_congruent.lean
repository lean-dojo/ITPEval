-- Statement-only formalization of Logipedia corpus artifact "cong.transitive_congruent"
-- (catalog title "cong.transitive_congruent"): for every natural modulus, congruence
-- defined by equality of remainders is a transitive relation. This file contains no proof.

namespace cong

def congruent (n m p : Nat) : Prop :=
  n % p = m % p

theorem transitive_congruent (p : Nat) :
    ∀ x y z : Nat, congruent x y p → congruent y z p → congruent x z p := sorry

end cong
