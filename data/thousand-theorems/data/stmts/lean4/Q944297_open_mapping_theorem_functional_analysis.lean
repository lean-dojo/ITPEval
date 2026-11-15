-- Statement-only formalization of Thousand Theorems artifact Q944297
-- (thousand-theorems__lean4__Q944297), "Open mapping theorem (functional analysis)":
-- every surjective continuous semilinear map between Banach spaces over paired isometric
-- scalar-field homomorphisms is an open map. This file contains no proof.

module

public import Mathlib.Analysis.Normed.Operator.NormedSpace
public import Mathlib.Topology.Baire.CompleteMetrizable

@[expose] public section

namespace Q944297

/-- The Banach open mapping theorem for continuous semilinear maps. -/
theorem open_mapping_theorem
    {𝕜 𝕜' : Type*} [NontriviallyNormedField 𝕜] [NontriviallyNormedField 𝕜']
    {σ : 𝕜 →+* 𝕜'} {σ' : 𝕜' →+* 𝕜}
    [RingHomInvPair σ σ'] [RingHomIsometric σ] [RingHomIsometric σ']
    {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] [CompleteSpace E]
    {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜' F] [CompleteSpace F]
    (f : E →SL[σ] F) (surj : Function.Surjective f) :
    IsOpenMap f := sorry

end Q944297
