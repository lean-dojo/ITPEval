-- Statement-only formalization of Thousand Theorems artifact Q848375
-- (thousand-theorems__lean4__Q848375), "Implicit function theorem": for general
-- implicit-function data on complete normed spaces, the implicit function is the curried inverse
-- of the associated local open partial homeomorphism. This file contains no proof.

module

public import Mathlib.Analysis.Calculus.InverseFunctionTheorem.FDeriv

@[expose] public section

noncomputable section

namespace Q848375

structure ImplicitFunctionData (𝕜 : Type*) [NontriviallyNormedField 𝕜] (E : Type*)
    [NormedAddCommGroup E] [NormedSpace 𝕜 E] [CompleteSpace E] (F : Type*)
    [NormedAddCommGroup F] [NormedSpace 𝕜 F] [CompleteSpace F] (G : Type*)
    [NormedAddCommGroup G] [NormedSpace 𝕜 G] [CompleteSpace G] where
  leftFun : E → F
  leftDeriv : E →L[𝕜] F
  rightFun : E → G
  rightDeriv : E →L[𝕜] G
  pt : E
  hasStrictFDerivAt_leftFun : HasStrictFDerivAt leftFun leftDeriv pt
  hasStrictFDerivAt_rightFun : HasStrictFDerivAt rightFun rightDeriv pt
  range_leftDeriv : leftDeriv.toLinearMap.range = ⊤
  range_rightDeriv : rightDeriv.toLinearMap.range = ⊤
  isCompl_ker : IsCompl leftDeriv.toLinearMap.ker rightDeriv.toLinearMap.ker

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] [CompleteSpace E]
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F] [CompleteSpace F]
variable {G : Type*} [NormedAddCommGroup G] [NormedSpace 𝕜 G] [CompleteSpace G]

/-- A local product homeomorphism and its curried inverse implicit function. -/
structure ImplicitFunctionResult (φ : ImplicitFunctionData 𝕜 E F G) where
  toOpenPartialHomeomorph : OpenPartialHomeomorph E (F × G)
  coe_toOpenPartialHomeomorph :
    ⇑toOpenPartialHomeomorph = fun x ↦ (φ.leftFun x, φ.rightFun x)
  pt_mem_source : φ.pt ∈ toOpenPartialHomeomorph.source
  implicitFunction : F → G → E
  implicitFunction_eq :
    implicitFunction = Function.curry toOpenPartialHomeomorph.symm

/-- The general implicit function theorem, packaged with its local product homeomorphism. -/
def implicitFunction_statement (φ : ImplicitFunctionData 𝕜 E F G) :
    ImplicitFunctionResult φ := sorry

end Q848375
