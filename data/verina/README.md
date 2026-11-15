# VERINA

This directory contains a pinned import of the VERINA program-verification benchmark. Upstream Lean files are retained under `data/proofs/lean4`; derived statement files preserve imports, auxiliary definitions used by the statement, preconditions, executable implementations, postconditions, and correctness theorems while replacing only the proof body with `sorry`. Four derived statements also replace the removed `emptyWithCapacity` constructor name with Lean 4.18's semantically identical `empty`. Two derived statements omit unused Float axioms that occur only in the upstream proof environment and do not occur in the program, contract, or theorem type. The exact upstream files remain unchanged under `data/proofs/lean4`, and each normalization is recorded in `data/index.json`.

Source revision: `66b3ce5014edafb20cb26b87c681e7f31847249f`
License: Apache-2.0 (see `LICENSE`).
