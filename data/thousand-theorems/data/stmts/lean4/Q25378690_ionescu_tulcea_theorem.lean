-- Statement-only formalization of Thousand Theorems artifact Q25378690
-- (thousand-theorems__lean4__Q25378690), "Ionescu-Tulcea theorem": a family of
-- Markov transition kernels on successive dependent coordinates uniquely extends
-- finite initial trajectories to a Markov kernel on infinite trajectories with
-- the prescribed finite-dimensional marginals. This file contains no proof.

module

public import Mathlib.Probability.Kernel.IonescuTulcea.PartialTraj

@[expose] public section

open Finset MeasureTheory ProbabilityTheory

variable {X : ℕ → Type*} [∀ n, MeasurableSpace (X n)]

namespace ProbabilityTheory.Kernel.Q25378690

/-- The Ionescu-Tulcea theorem for a sequence of Markov kernels on dependent state spaces. -/
theorem ionescu_tulcea_theorem
    (κ : (n : ℕ) → Kernel (Π i : Iic n, X i) (X (n + 1)))
    [∀ n, IsMarkovKernel (κ n)] (a : ℕ) :
    ∃! η : Kernel (Π i : Iic a, X i) (Π n, X n),
      IsMarkovKernel η ∧
        ∀ b : ℕ, η.map (fun (x : Π n, X n) (i : Iic b) ↦ x i.1) =
          partialTraj κ a b := sorry

end ProbabilityTheory.Kernel.Q25378690
