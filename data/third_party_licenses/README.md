# Third-Party License Texts

This directory collects license texts and copyright notices for third-party
datasets and theorem-library files represented in `data/`.

The repository root `LICENSE` applies to this repository's original material.
It does not replace the upstream terms for third-party benchmark files. Users
who redistribute, modify, or build on the benchmark data should also review the
upstream projects listed below.

This file is an index of license texts, not a theorem-by-theorem source map.
Historical statements under `data/*/stmts/` and extended representations under
`data/*/data/stmts/` retain their source provenance in dataset indexes and
[the dataset description](../../docs/new_data_description.md).

## License Index

| Local license file | Upstream dataset/library | Project URL | Upstream license/notice URL | License or notice represented |
|---|---|---|---|---|
| `babel-formal-MIT.txt` | Babel-Formal | <https://github.com/LLM4Rocq/babel-formal> | <https://github.com/LLM4Rocq/babel-formal/blob/main/LICENSE> | MIT |
| `openai-minif2f-lean-Apache-2.0.txt` | OpenAI miniF2F Lean data | <https://github.com/openai/miniF2F> | <https://github.com/openai/miniF2F/blob/master/README.md#license> | Apache-2.0 for the Lean folder in upstream miniF2F |
| `openai-minif2f-isabelle-Apache-2.0.txt` | OpenAI miniF2F Isabelle data | <https://github.com/openai/miniF2F> | <https://github.com/openai/miniF2F/blob/master/README.md#license> | Apache-2.0 for the Isabelle folder in upstream miniF2F |
| `openai-minif2f-hollight-BSD-style.txt` | OpenAI miniF2F HOL Light data | <https://github.com/openai/miniF2F> | <https://github.com/openai/miniF2F/blob/master/README.md#license> | FreeBSD/BSD-style notice for the HOL Light folder in upstream miniF2F |
| `openai-minif2f-metamath-MIT.txt` | OpenAI miniF2F Metamath data | <https://github.com/openai/miniF2F> | <https://github.com/openai/miniF2F/blob/master/README.md#license> | MIT for the Metamath folder in upstream miniF2F |
| `facebook-minif2f-MIT.txt` | Facebook Research miniF2F fork | <https://github.com/facebookresearch/miniF2F> | <https://github.com/facebookresearch/miniF2F/blob/main/LICENSE> | MIT |
| `minif2f-rocq-MIT.txt` | LLM4Rocq miniF2F-rocq | <https://github.com/LLM4Rocq/miniF2F-rocq> | <https://github.com/LLM4Rocq/miniF2F-rocq/blob/main/LICENSE> | MIT |
| `mathlib4-Apache-2.0.txt` | Lean mathlib4 | <https://github.com/leanprover-community/mathlib4> | <https://github.com/leanprover-community/mathlib4/blob/master/LICENSE> | Apache-2.0 |
| `coq-rocq-stdlib-LGPL-2.1.txt` | Rocq/Coq standard library | <https://github.com/rocq-prover/rocq> | <https://github.com/rocq-prover/rocq/blob/master/LICENSE> | LGPL-2.1 |
| `mathcomp-CeCILL-B.txt` | Mathematical Components (MathComp) | <https://github.com/math-comp/math-comp> | <https://github.com/math-comp/math-comp/blob/master/LICENCE> | CeCILL-B |
| `corn-GPL-2.0.txt` | CoRN | <https://github.com/rocq-community/corn> | <https://github.com/rocq-community/corn/blob/master/LICENSE> | GPL-2.0 |
| `coq-100-theorems-MIT.txt` | coq-100-theorems | <https://github.com/rocq-community/coq-100-theorems> | <https://github.com/rocq-community/coq-100-theorems/blob/master/LICENSE> | MIT, except where upstream file headers say otherwise |
| `qarith-stern-brocot-LGPL-2.1.txt` | Qarith-Stern-Brocot | <https://github.com/rocq-community/qarith-stern-brocot> | <https://github.com/rocq-community/qarith-stern-brocot/blob/master/LICENSE> | LGPL-2.1-or-later |
| `highschoolgeometry-LGPL-2.1.txt` | HighSchoolGeometry | <https://github.com/rocq-community/HighSchoolGeometry> | <https://github.com/rocq-community/HighSchoolGeometry/blob/master/LICENSE> | LGPL-2.1-or-later |
| `coqtail-math-LGPL-3.0-note.txt`, `coqtail-math-LGPL-3.0-full.txt` | coqtail-math | <https://github.com/rocq-community/coqtail-math> | <https://github.com/rocq-community/coqtail-math/blob/master/LICENSE>, <https://github.com/rocq-community/coqtail-math/blob/master/lgpl-3.0.txt> | LGPL-3.0-only repository license; some upstream file headers may carry older LGPL-2.1 notices |
| `fsets-LGPL-2.1.txt` | fsets | <https://github.com/rocq-archive/fsets> | <https://github.com/rocq-archive/fsets/blob/master/LICENSE> | LGPL-2.1 |
| `cauchy-schwarz-CeCILL-B.txt` | Cauchy-Schwarz | <https://github.com/roglo/cauchy_schwarz> | <https://github.com/roglo/cauchy_schwarz/blob/master/LICENSE> | CeCILL-B |
| `coq-friendship-theorem-MIT.txt` | coq-friendship-theorem | <https://github.com/aleloi/coq-friendship-theorem> | <https://github.com/aleloi/coq-friendship-theorem/blob/master/LICENCE> | MIT |
| `ekdohibs-coq-proofs-MIT.txt` | Ekdohibs/coq-proofs | <https://github.com/Ekdohibs/coq-proofs> | <https://github.com/Ekdohibs/coq-proofs/blob/master/LICENSE> | MIT |
| `hol-light-BSD-style.txt` | HOL Light | <https://github.com/jrh13/hol-light> | <https://github.com/jrh13/hol-light/blob/master/LICENSE> | HOL Light BSD-style copyright notice, license, and disclaimer |
| `isabelle-COPYRIGHT-BSD-style.txt` | Isabelle | <https://github.com/isabelle-prover/mirror-isabelle> | <https://github.com/isabelle-prover/mirror-isabelle/blob/master/COPYRIGHT> | Isabelle BSD-style copyright notice, license, and disclaimer |

## Extended sources

The extended release preserves the existing notices above and adds:

| Included notice | Source |
|---|---|
| `putnambench-lean4-LICENSE.txt` | Pinned PutnamBench `lean4/LICENSE` |
| `putnambench-coq-LICENSE.txt` | Pinned PutnamBench `coq/LICENSE` |
| `putnambench-isabelle-LICENSE.txt` | Pinned PutnamBench `isabelle/LICENSE` |
| `verina-Apache-2.0.txt` | VERINA source revision `66b3ce5014edafb20cb26b87c681e7f31847249f` |

Dataset indexes preserve source identifiers for nTP4VC, Logipedia, and Thousand
Theorems. No standalone license file was found in the locally pinned checkouts
of those three sources; this index does not assign them the repository's MIT
license or invent replacement notices. Their existing file headers and source
attributions are retained. See the source links in `data/<dataset>/data/index.json`
and the [dataset description](../../docs/new_data_description.md).

The release copies Putnam problem metadata into
`data/putnambench/data/upstream_problem_metadata.json` for a self-contained audit.
Development-only upstream gitlinks and generated build caches are not required.
