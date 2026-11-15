-- Statement-only formalization of Logipedia corpus artifact "bool.andb_true_r"
-- (catalog title "bool.andb_true_r"): Boolean conjunction evaluating to true
-- implies that its right operand is true. This file contains no proof.

theorem bool.andb_true_r (b1 b2 : Bool) : b1 && b2 = true → b2 = true := sorry
