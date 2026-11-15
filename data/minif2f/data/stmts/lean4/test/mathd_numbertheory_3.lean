-- Statement-only formalization of miniF2F test problem mathd_numbertheory_3. This file
-- contains no proof.

import Mathlib

set_option maxHeartbeats 0

open BigOperators Real Nat Topology Rat

theorem mathd_numbertheory_3 :
  (∑ x ∈ Finset.range 9, ((x + 1)^2)) % 10 = 5 := by sorry
