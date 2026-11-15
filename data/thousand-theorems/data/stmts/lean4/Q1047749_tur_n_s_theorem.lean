-- Statement-only formalization of Thousand Theorems artifact Q1047749
-- (thousand-theorems__lean4__Q1047749), "Turán's theorem": for positive r, a finite
-- graph is r-Turán-maximal exactly when it is isomorphic to the canonical complete r-partite
-- Turán graph on the same number of vertices. This file contains no proof.

module

public import Mathlib.Combinatorics.SimpleGraph.Clique
public import Mathlib.Combinatorics.SimpleGraph.Extremal.Basic

@[expose] public section

open Fintype

namespace SimpleGraph

variable {V : Type*} [Fintype V] {G : SimpleGraph V} [DecidableRel G.Adj] {r : ℕ}

variable (G) in
/-- An `r + 1`-cliquefree graph is `r`-Turán-maximal if every other such graph on
the same vertex type has at most as many edges. -/
def IsTuranMaximal (r : ℕ) : Prop := G.IsExtremal (CliqueFree · (r + 1))

/-- The canonical complete `r`-partite graph on `Fin n`, with parts indexed by residues modulo `r`. -/
def turanGraph (n r : ℕ) : SimpleGraph (Fin n) where
  Adj v w := v % r ≠ w % r

/-- Turán's theorem: the canonical Turán graph is the unique Turán-maximal graph up to isomorphism. -/
theorem isTuranMaximal_iff_nonempty_iso_turanGraph (hr : 0 < r) :
    G.IsTuranMaximal r ↔ Nonempty (G ≃g turanGraph (card V) r) := sorry

end SimpleGraph
