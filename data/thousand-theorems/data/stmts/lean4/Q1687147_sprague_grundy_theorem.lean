-- Statement-only formalization of Thousand Theorems artifact Q1687147
-- (thousand-theorems__lean4__Q1687147), "Sprague–Grundy theorem": every
-- impartial combinatorial game is equivalent to the game of Nim corresponding
-- to its Grundy value. This file contains no proof.

module

public import Mathlib.SetTheory.Game.Nim

@[expose] public section

universe u

open SetTheory
open scoped PGame

namespace Q1687147

/-- Every impartial game is equivalent to the Nim game determined by its Grundy value. -/
theorem sprague_grundy_theorem_statement (G : PGame.{u}) [G.Impartial] :
    PGame.nim (Nimber.toOrdinal (PGame.grundyValue G)) ≈ G := sorry

end Q1687147
