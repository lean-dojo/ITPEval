-- Statement-only formalization of Thousand Theorems artifact Q866116
-- (thousand-theorems__lean4__Q866116), "Hahn–Banach theorem": every continuous
-- linear functional on a subspace of a seminormed space over a real-like normed
-- field extends to the whole space without changing its norm. This file contains no proof.

module

public import Mathlib.Analysis.Normed.Operator.Basic
public import Mathlib.Analysis.RCLike.Basic

@[expose] public section

universe u

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] [IsRCLikeNormedField 𝕜]
variable {E : Type u} [SeminormedAddCommGroup E] [NormedSpace 𝕜 E]

/-- The norm-preserving Hahn–Banach extension theorem for continuous linear functionals. -/
theorem exists_extension_norm_eq (p : Subspace 𝕜 E) (f : StrongDual 𝕜 p) :
    ∃ g : StrongDual 𝕜 E, (∀ x : p, g x = f x) ∧ ‖g‖ = ‖f‖ := sorry
