# Provers and libraries

Choose a prover to see how its logic works, read a proof in the native language, and load a project. Each guide also has a short proof you can edit yourself. [VS Code exercises](../start/proof-completion.md#choose-your-prover)

| Prover | Worked proof | Logical foundation | Library examples |
|---|---|---|---|
| [ACL2](acl2.md) | [Read the proof](acl2.md#read-a-proof) | [First-order logic with recursive functions](acl2.md#how-proof-checking-works) | [Community Books, Standard Library, Arithmetic-5](acl2.md#libraries) |
| [Agda](agda.md) | [Read the proof](agda.md#read-a-proof) | [Martin-Löf dependent type theory](agda.md#how-proof-checking-works) | [Agda.Builtin, Standard Library, Cubical Agda library](agda.md#libraries) |
| [HOL Light](hol-light.md) | [Read the proof](hol-light.md#read-a-proof) | [Classical higher-order logic](hol-light.md#how-proof-checking-works) | [HOL Light Library, Multivariate, Formalizing 100 Theorems](hol-light.md#libraries) |
| [HOL4](hol4.md) | [Read the proof](hol4.md#read-a-proof) | [Classical higher-order logic](hol4.md#how-proof-checking-works) | [HOL4 theories, HOL4 examples, CakeML](hol4.md#libraries) |
| [Isabelle/HOL](isabelle.md) | [Read the proof](isabelle.md#read-a-proof) | [Classical higher-order logic](isabelle.md#how-proof-checking-works) | [HOL, HOL-Analysis, Archive of Formal Proofs](isabelle.md#libraries) |
| [Lean 4](lean4.md) | [Read the proof](lean4.md#read-a-proof) | [Dependent type theory](lean4.md#how-proof-checking-works) | [Init, Std, Mathlib, CSLib, Batteries](lean4.md#libraries) |
| [Metamath](metamath.md) | [Read the proof](metamath.md#read-a-proof) | [Rules and axioms chosen by the database](metamath.md#how-proof-checking-works) | [set.mm, iset.mm](metamath.md#libraries) |
| [Mizar](mizar.md) | [Read the proof](mizar.md#read-a-proof) | [Classical first-order logic and set theory](mizar.md#how-proof-checking-works) | [Mizar Mathematical Library, REAL_1, GROUP_1](mizar.md#libraries) |
| [PVS](pvs.md) | [Read the proof](pvs.md#read-a-proof) | [Classical higher-order logic with dependent types](pvs.md#how-proof-checking-works) | [Prelude, PVS libraries, NASA PVS Library](pvs.md#libraries) |
| [Rocq](rocq.md) | [Read the proof](rocq.md#read-a-proof) | [Calculus of Inductive Constructions](rocq.md#how-proof-checking-works) | [Corelib, Stdlib, Mathematical Components, Iris](rocq.md#libraries) |

## Bring your own files

The examples use small bundled projects so you can read the whole proof. You can also point ITPEval at a file you already have. For example, Lean loads compiled dependencies, Rocq maps logical names to compiled modules, and Metamath follows the database’s include paths. For a proof-completion exercise, choose the theorem and the region a candidate can edit. [Check your own files](../guides/work-with-a-library.md)

[Compare proof and extraction features](../reference/capabilities.md) · [Install a prover](../runtime/toolchains.md)
