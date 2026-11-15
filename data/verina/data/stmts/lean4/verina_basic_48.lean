-- Statement-only formalization of "isPerfectSquare" from VERINA item verina_basic_48. This file
-- contains no proof.

-- !benchmark @start import type=solution
import Mathlib
-- !benchmark @end import

-- !benchmark @start solution_aux

-- !benchmark @end solution_aux

-- !benchmark @start precond_aux

-- !benchmark @end precond_aux

@[reducible, simp]
def isPerfectSquare_precond (n : Nat) : Prop :=
  -- !benchmark @start precond
  True
  -- !benchmark @end precond


-- !benchmark @start code_aux

-- !benchmark @end code_aux


def isPerfectSquare (n : Nat) : Bool :=
  -- !benchmark @start code
  if n = 0 then true
  else
    let rec check (x : Nat) (fuel : Nat) : Bool :=
      match fuel with
      | 0 => false
      | fuel + 1 =>
        if x * x > n then false
        else if x * x = n then true
        else check (x + 1) fuel
    check 1 n
  -- !benchmark @end code


-- !benchmark @start postcond_aux

-- !benchmark @end postcond_aux


@[reducible, simp]
def isPerfectSquare_postcond (n : Nat) (result : Bool) : Prop :=
  -- !benchmark @start postcond
  result ↔ ∃ i : Nat, i * i = n
  -- !benchmark @end postcond


-- !benchmark @start proof_aux
theorem check_correct (n : Nat) (x fuel : Nat) :
   isPerfectSquare.check n x fuel = true → ∃ i, x ≤ i ∧ i * i = n := by
  induction fuel generalizing x with
  | zero =>
    -- In the base case, check always returns false, so this is a contradiction
    unfold isPerfectSquare.check
    simp

  | succ fuel ih =>
    -- Unfold the definition of check for the successor case
    unfold isPerfectSquare.check
    simp_all

    -- Split into cases based on comparison of x*x with n
    if hgt : x * x > n then
      -- If x*x > n, check returns false, contradiction
      simp_all
    else if heq : x * x = n then
      -- If x*x = n, we found our witness
      simp_all
      exists x
    else
      -- Otherwise, we need to apply the induction hypothesis
      simp_all
      have h_rec := ih (x + 1)
      -- Complete the proof by transitivity of ≤
      intro h
      have ⟨i, hi, heqi⟩ := h_rec h
      exists i
      constructor
      · -- Show x ≤ i by transitivity: x ≤ x+1 ≤ i
        exact Nat.le_trans (Nat.le_succ x) hi
      · -- Pass through the equality i * i = n
        exact heqi

theorem check_complete (n : Nat) (x fuel : Nat) (i : Nat)
    (hx : x ≤ i) (hi : i * i = n) (hfuel : i < x + fuel) :
  isPerfectSquare.check n x fuel = true := by

  induction fuel generalizing x with
  | zero =>
    -- In the zero fuel case, we have a contradiction:
    -- i < x + 0 implies i < x, which contradicts x ≤ i
    unfold isPerfectSquare.check
    simp_all
    exact absurd hfuel (Nat.not_lt_of_le hx)

  | succ fuel ih =>
    -- For the successor case, unfold the definition
    unfold isPerfectSquare.check
    simp

    -- Check the first condition: x * x > n
    if hgt : x * x > n then
      -- This contradicts x ≤ i and i * i = n
      have x_le_i_squared : x * x ≤ i * i := Nat.mul_le_mul hx hx
      rw [hi] at x_le_i_squared
      exact absurd hgt (Nat.not_lt_of_ge x_le_i_squared)
    else if heq : x * x = n then
      -- Found a perfect square directly
      simp_all
    else
      -- Need to continue searching

      -- Check if x = i
      if hxi : x = i then
        -- If x = i, then x * x = i * i = n, contradicting heq
        rw [hxi] at heq
        exact absurd hi heq
      else
        simp_all
        -- x < i case: continue searching with x + 1
        have x_lt_i : x < i := Nat.lt_of_le_of_ne hx hxi
        have x_succ_le_i : x + 1 ≤ i := Nat.succ_le_of_lt x_lt_i

        -- Show i < (x + 1) + fuel
        have i_lt_next_fuel : i < (x + 1) + fuel := by
          rw [Nat.add_assoc, Nat.add_comm _ fuel]
          exact hfuel

        -- Apply induction hypothesis
        exact ih (x + 1) x_succ_le_i i_lt_next_fuel

-- !benchmark @end proof_aux

theorem isPerfectSquare_spec_satisfied (n : Nat) :
    isPerfectSquare_postcond n (isPerfectSquare n) := by
  -- !benchmark @start proof
  sorry
  -- !benchmark @end proof
