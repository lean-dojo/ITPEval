# Program verification

<span id="6-ntp4vc"></span>

## nTP4VC

nTP4VC uses Why3 and Frama-C to extract properties a program must satisfy, then exports them to Lean, Rocq and Isabelle. One program can yield several obligations, such as a loop property and a condition on the output. The upstream selection favors difficult cases and includes **300 program pearls and 300 real-C obligations**. [Paper, §4, Tables 2–4](https://arxiv.org/html/2601.18944v1#S4)

### Paper's verification-scenario taxonomy

These counts cover the original 600. The local metadata lacks a complete mapping to the nine paper categories. Use the source-project table for exact retained counts.

| Source family | Paper category | Original VCs | Property or problem type |
|---|---|---:|---|
| Program pearls | Algorithm | 55 | Algorithmic correctness |
| Program pearls | Data structure | 73 | Data-structure operations and invariants |
| Program pearls | Calculation | 66 | Computational/mathematical routines |
| Program pearls | Engineering | 54 | Verification-oriented programming tasks |
| Program pearls | Competition | 52 | Verification challenge problems |
| Real C | Function | 81 | Function contracts |
| Real C | Loop | 81 | Loop properties |
| Real C | Memory | 74 | Memory safety/properties |
| Real C | Invalid argument | 64 | Validity of operation arguments |
| **Total** | | **600** | |

### Exact local source-project breakdown

Local counts match the pinned manifest against the available files. The paper’s Table 3 combines `klibc_stdio` and `klibc_string`. [600-item manifest](../../data/ntp4vc/data/test_set.lean.txt.lst)

| Source project / local path group | Imported VCs | Ten-prover VCs | What it contributes |
|---|---:|---:|---|
| Why3 program pearls: `pearl/` | 300 | **299** | Algorithms, data structures, calculations, engineering, verification contests |
| Contiki linked lists: `frama_c/contiki_list` | 78 | **78** | Linked-list properties and memory relationships |
| Contiki allocator: `frama_c/contiki_memb` | 21 | **21** | Allocation and memory-block properties |
| C++ STL-derived algorithms: `frama_c/standard_algorithms` | 53 | **53** | Sorting, searching, heaps and sequence algorithms |
| X.509 parser: `frama_c/x509_parser` | 9 | **9** | Parser correctness and safety obligations |
| Linux scheduler: `frama_c/should_we_balance` | 24 | **24** | Scheduler balancing routine |
| Linux library functions: `frama_c/verker` | 85 | **85** | Verified kernel library routines |
| kLIBC stdio: `frama_c/klibc_stdio` | 3 | **3** | Standard-I/O routines |
| kLIBC strings: `frama_c/klibc_string` | 11 | **11** | String-library routines |
| Paparazzi/UAV mathematics: `frama_c/airborne` | 16 | **14** | Numerical routines involving rotations/quaternions |
| **Total** | **600** | **597** | **299 pearls + 298 real-C VCs** |

The pinned selection omits `examples/`, which appears in the broader index.

The three excluded canonical identities are:

- `frama_c/airborne/float_quat_of_rmat/float_quat_of_rmat_Why3_ide_VCfloat_quat_of_rmat_a00_max_post_goal9`
- `frama_c/airborne/float_quat_of_rmat/float_quat_of_rmat_Why3_ide_VCfloat_quat_of_rmat_a11_max_post_goal10`
- `pearl/register_allocation_DWP_wrapqtvc`

### Operation types and structural complexity

The paper’s Table 4 counts overlapping operation families for the original 600. A VC can appear in several rows. [Operation statistics](https://github.com/xqyww123/NTP4VC/blob/3ff8817c0fb04a5ef472a62a0fa5cd7a7934afe3/statistics/statistics_VC.csv)

| Operation family | Original 600 VCs containing it |
|---|---:|
| Integer arithmetic | 578 |
| Nonlinear arithmetic | 118 |
| Floating-point-related arithmetic | 18 |
| Lists / sequences | 202 |
| Sets / maps / bags | 59 |
| Trees / strings / matrices | 26 |
| Memory operations | 297 |
| Custom datatypes | 247 |

Across the original 600, Isabelle expressions average about **583 atomic terms**, depth **54.5**, and **10.8 quantifiers**. Appendix H describes the floating-point quantities as reals without rounding error.

The released per-item CSV contains size, depth and dependencies. Recomputing operation counts for the retained 597 needs item-level labels.

Examples include `pearl/binomial_heap_BinomialHeap_mergeqtvc`,
`pearl/imp/imp_SymbolicInterpreter_symbolic_interp_whileqtvc`, and
`pearl/verifythis_2024_challenge1_Top_smart_array_copy_0qtvc`. Each retains its program definitions and assumptions.

The index pins revision `3ff8817c0fb04a5ef472a62a0fa5cd7a7934afe3`. Canonical keys drop the `_vcg/<language>/` layer. Rocq or Isabelle may use `X_` where Lean uses `_`. Original `.mlw` files and reviewed corrections govern the extension, with exports as secondary references. [Source index](../../data/ntp4vc/data/index.json) · [Why3 path mapping](https://github.com/xqyww123/NTP4VC#the-benchmark)

The release materializes the three original prover representations as statement files for the pinned selection.

<span id="9-verina"></span>

## VERINA

VERINA asks models to write Lean programs, specifications and proofs separately and together. Each of its **189 tasks** includes a description, implementation, contract and tests. The paper reports **46 reference proofs**. [Paper, §3.1–3.2 and Table 2](https://arxiv.org/html/2505.23135v1#S3)

### Exact origin and difficulty-group breakdown

All 189 tasks appear in the ten-prover statement export. [Task index](../../data/verina/data/index.json)

| Paper subset | Upstream source | Exact local task IDs | Tasks | What these data are |
|---|---|---|---:|---|
| VERINA-basic | MBPP-DFY-50; local origin `dafny-synthesis` | `verina_basic_1`–`verina_basic_49` | **49** | Human-authored Dafny programming problems translated into Lean |
| VERINA-basic | CloverBench; local origin `clover` | `verina_basic_50`–`verina_basic_108` | **59** | Additional Dafny examples translated and reviewed |
| VERINA-adv | Course submissions; local origin `lab_assignment` | `verina_advanced_1`–`verina_advanced_81` | **81** | More advanced tasks formalized in Lean; sources include LeetCode/LiveCodeBench-style problems |
| **Total** | **3 origins** | **108 basic + 81 advanced** | **189** | |

The paper reports difficulty groups. Exact counts by algorithm or by LeetCode and LiveCodeBench origin would require finer labels.

Examples include `hasOppositeSign` (`verina_basic_1`), `sumOfDigits` (`verina_basic_18`) and `isSorted` (`verina_basic_19`). Different tasks can share an algorithm, as with `LongestCommonSubsequence` (`verina_advanced_2` and `verina_advanced_3`) and `insertionSort` (`verina_advanced_16` and `verina_advanced_17`).

### Paper's code/specification size measurements

These measurements cover program and specification sections only.

| Subset | Code lines: median / maximum | Specification lines: median / maximum |
|---|---:|---:|
| Basic | 6 / 26 | 2 / 17 |
| Advanced | 16 / 38 | 7 / 62 |
| All tasks | 9 / 38 | 4 / 62 |

Each translation item includes helpers, precondition, executable program, postcondition and correctness statement. The goal is to preserve computation and contract. The 189 imported tasks count statements, and VERINA’s code-generation and specification-generation experiments remain separate.

**Pinned import.** The source revision is
`66b3ce5014edafb20cb26b87c681e7f31847249f`. The [local import notes](../../data/verina/README.md)
document proof-body removal and six compatibility-normalized statements:
constructor renames in basic 22 and advanced 28/55/74; omission of unused,
proof-only Float axioms in basic 25/63. The original Lean files are retained.

**Files:** `data/verina/data/stmts/<prover>/<task-id>.<ext>`;
[descriptions](../../data/verina/data/descriptions) and
[metadata](../../data/verina/data/metadata) retain the informal tasks and signatures.
