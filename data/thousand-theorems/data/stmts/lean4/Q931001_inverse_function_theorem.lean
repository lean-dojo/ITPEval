-- Statement-only formalization of Thousand Theorems artifact Q931001
-- (thousand-theorems__lean4__Q931001), "Inverse function theorem": a function
-- with an invertible strict derivative has a local inverse whose strict derivative
-- is the inverse continuous linear equivalence. This file contains no proof.

module

public import Mathlib.Analysis.Calculus.InverseFunctionTheorem.FDeriv

@[expose] public section

noncomputable section

namespace Q931001

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] [CompleteSpace E]
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
variable {f : E → F} {f' : E ≃L[𝕜] F} {a : E}

/-- The local inverse of a function with an invertible strict derivative has the inverse
continuous linear equivalence as its strict derivative. -/
theorem inverse_function_theorem
    (hf : HasStrictFDerivAt f (f' : E →L[𝕜] F) a) :
    HasStrictFDerivAt (hf.localInverse f f' a) (f'.symm : F →L[𝕜] E) (f a) := sorry

end Q931001
