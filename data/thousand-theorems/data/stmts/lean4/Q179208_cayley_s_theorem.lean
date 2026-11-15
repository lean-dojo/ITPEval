-- Statement-only formalization of Thousand Theorems artifact Q179208
-- (thousand-theorems__lean4__Q179208), "Cayley's theorem": every group with a
-- faithful action is multiplicatively equivalent to the range subgroup of its
-- induced permutation action. This file contains no proof.

module

public import Mathlib.Algebra.Group.Action.End
public import Mathlib.Algebra.Group.Subgroup.Finite
public import Mathlib.Data.Fintype.Perm

@[expose] public section

namespace Q179208

/-- Cayley's theorem generalized to an arbitrary faithful group action. -/
noncomputable def subgroupOfMulAction_statement
    (G H : Type*) [Group G] [MulAction G H] [FaithfulSMul G H] :
    G ≃* (MulAction.toPermHom G H).range := sorry

end Q179208
