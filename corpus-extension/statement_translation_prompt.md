# Statement Corpus Extension Prompt

Coordinate statement translation only. Do not translate or attempt proofs, or
add proof-related checks or metadata. Include only the target syntax required
to represent an unproved statement.

A completed translation must preserve the source statement's logical meaning.
A target-specific approximation, bounded model, or related easier statement is
not a faithful translation and must not be accepted.

## Scope

- The run manifest is authoritative. Translate every queued artifact in it and
  do not invent additional artifacts.
- Supported corpora are Babel-formal, miniF2F, PutnamBench, Hundred Theorems,
  Thousand Theorems, Logipedia, NTP4VC, MATP-Bench, and VERINA.
- The target set is Lean 4, Rocq, Isabelle, HOL Light, HOL4, PVS, Agda,
  ACL2, Metamath, and Mizar. A run may select any subset.
- One artifact is one `(corpus item, target prover)` statement translation or
  one explicitly identified shared support module.

## Parallel Orchestration

Enqueue every manifest job immediately. Do not use a sequential outer loop;
let the scheduler execute the full fan-out at its available concurrency.

Assign each artifact its own semantic-review agent. Trigger that reviewer as soon as the translator produces its first verified candidate. Reviewers and translators for different artifacts must continue in parallel; refinement of one artifact must not block another.

The translator alone edits the target candidate. The reviewer alone writes that artifact's review log. On `REVISE`, the reviewer sends specific feedback, the translator revises and re-verifies, and the same reviewer checks again. Continue until `ACCEPT` or `BLOCKED`.

The external coordinator alone launches reviewer jobs. A translator must not
spawn, invoke, delegate to, or wait for another agent. After successful
ITPEval verification, it must immediately return the required final JSON so
the coordinator can start the reviewer.

## Ground Truth

- Babel-formal: Lean 4 and Rocq are primary. Isabelle and HOL Light are
  secondary references and cannot silently override the primary sources.
- miniF2F: every available existing statement representation is ground truth.
- PutnamBench: the published informal problem statement is the semantic
  authority. Use Lean 4 as the primary formal reference and existing Rocq and
  Isabelle files as secondary, prover-native references. A reviewed
  `canonical_resolution` in the artifact record documents known source defects
  and is authoritative for that artifact. Do not require textual or
  representation-level agreement across provers: library objects, records,
  predicates, indexing conventions, and equivalent quantifier packaging may
  differ. If a secondary formalization has an evident typo, unused or
  unconstrained predicate, vacuous edge case, wrong numeric type, or other
  proposition-changing transcription defect, follow the published problem and
  the reviewed resolution rather than returning `BLOCKED`. If Lean conflicts
  with the published problem, the published problem and reviewed resolution
  take precedence.
- Hundred Theorems: use every local formal statement/proof source for the
  numeric theorem ID. A reviewed language-neutral specification in the
  manifest may supply an otherwise missing theorem.
- Thousand Theorems: use the indexed prover identifiers and their pinned local
  source files. Do not translate from a title alone or regex-copy an unrelated
  whole module.
- Logipedia: use the index's inline prover statements as primary ground truth
  and the local Coq/Lean modules as dependency context. Preserve the module
  dependency graph through shared support artifacts.
- NTP4VC: the original Why3 `.mlw` verification condition at the pinned
  upstream commit is primary ground truth. Lean 4, Rocq, and Isabelle exports
  with the same canonical VC key are secondary prover-native references. If an
  export changes integer division, nested map-update order, coercions, or any
  other proposition-level detail, follow the original Why3 goal and record the
  export defect. Shared declarations may be translated once and reused only
  when their original Why3 source prefix is identical. Do not repair an
  inconsistent original Why3 theory by adding assumptions or axioms; return
  `BLOCKED` unless a reviewed `canonical_resolution` supplies a source-faithful
  correction.
- MATP-Bench: the natural-language problem and its diagram are joint primary
  ground truth. Inspect both completely. The upstream Lean 4, Rocq, and
  Isabelle files are secondary prover-native references only: they may contain
  malformed syntax, incomplete definitions, unrelated content, global axioms,
  vacuous propositions, or proposition-changing formalization errors. Use
  sound target-native definitions and explicit theorem assumptions to express
  the text-and-diagram problem faithfully. Never copy an upstream defect or
  let one secondary formalization silently override the primary multimodal
  problem.
- VERINA: the official Lean file is primary ground truth for the complete
  program-verification package. Preserve semantically relevant helpers, the
  precondition, executable implementation, postcondition, and final
  correctness proposition. Do not replace the source program with an
  unconstrained target function, a nondeterministic relation admitting extra
  outputs, or a theorem that merely asserts the existence of some output
  satisfying the postcondition. An exact target-native operational or graph
  relation is acceptable when it characterizes precisely the same computation.
- If the designated sources have a substantive conflict that prevents a
  common interpretation and no reviewed canonical resolution is supplied, log
  it and return `BLOCKED`.
- If the target cannot express that common interpretation without a
  substantive change of domain, quantification, assumptions, or conclusion,
  return `BLOCKED`. Target limitations justify blocking an artifact, not
  accepting an approximation.

## Translator-Verifier

The translator must:

1. Read all supplied ground-truth files and translate their central
   mathematical content using semantics-preserving target-native encodings.
2. Preserve the mathematical objects, domains, quantifier scopes,
   assumptions, conclusion, and intended difficulty, up to an explicit
   definitional or logical equivalence.
3. Do not make any of the following changes unless the candidate contains a
   genuine equivalent encoding and the semantic reviewer records the
   bidirectional equivalence argument:
   - arbitrary or potentially infinite domains to finite carriers, bounded
     ranges, enumerations, or finite tables;
   - real or complex values to rationals, integers, floating-point values, or
     other proper subdomains;
   - arbitrary sets, functions, relations, or predicates to finite lists,
     lookup tables, tags, or a fixed collection of examples;
   - an internal existentially quantified witness to an additional external
     parameter, or a universal quantifier to a fixed input;
   - source equality, order, algebraic structure, or function extensionality
     to a weaker uninterpreted relation;
   - stronger assumptions, a weaker conclusion, a vacuous antecedent, or a
     source theorem bundled with an assumption that already states its
     conclusion.
4. If a faithful target-native representation is unavailable, report the
   limitation instead of producing an approximation.
5. Begin every candidate with a concise target-native comment that:
   - identifies the source corpus and canonical artifact name;
   - uses `catalog_title` when the manifest provides one;
   - summarizes the mathematical subject without inventing facts not supported
     by the ground truth; and
   - contains the exact case-sensitive phrase `Statement-only formalization of`
     and states that the file contains no proof.

   Use `--` for Lean 4 and Agda, `(* ... *)` for Rocq, Isabelle, HOL Light,
   and HOL4, `%` for PVS, `;;` for ACL2 and ACL2(r), `$( ... $)` for
   Metamath, and `::` for Mizar. Keep the wording mathematical and
   repository-facing: never
   mention an agent, model, prompt, generation process, or debugging session.
6. Treat the comment as part of the candidate. Preserve it in the exact file
   staged for ITPEval and update it whenever a revision changes the statement's
   meaning.
7. Verify through ITPEval with:

   ```bash
   ./itpeval/bin/itpeval eval --prover <hol4|pvs|agda|acl2|acl2r|metamath|mizar> --task-dir <task-directory> --json
   ```

8. Prepare `<task-directory>` according to
   `itpeval/provers/<prover>/check.sh`. Keep build files, logs, caches, and
   generated outputs there rather than in the corpus directories.
9. Use the ITPEval result as the acceptance check. Direct prover commands may
   help diagnose failures but cannot replace the final wrapper run.
10. If an adapter cannot handle arbitrary corpus tasks or assumes a hello
    filename, report a shared infrastructure issue for a central fix; do not
    bypass ITPEval with a private verifier.
11. After every reviewer-requested change, rerun the wrapper and give the
    latest JSON result to the reviewer.

Here, `verified` means accepted as a well-formed target statement: parsing, name resolution, and typechecking or the target's corresponding statement check. It does not mean the theorem is proved. Never report placeholders, Agda postulates, unproved PVS declarations, or Metamath `$a` assertions as proofs.

For ACL2, represent the proposition as a predicate-valued `defun` or
`defun-sk`, with all domain restrictions, quantifiers, and hypotheses explicit
in its Boolean body. Conservative `defchoose` auxiliaries are permitted.
Use `defstub` when a theorem is generic over arbitrary function or operation
symbols: `defstub` is ACL2's conservative interface for such symbols and does
not assert a proposition or provide a proof. Keep every algebraic, order,
domain, and closure assumption explicit in the statement predicate; a
`defstub` declaration alone must never be treated as supplying those laws.
Certified ACL2 community/system books may be imported only with a literal
`(include-book "..." :dir :system)` event from the pinned ITPEval toolchain;
local, absolute, parent-relative, uncertified, and trust-tagged book imports are
forbidden. End the file with `(value-triple
:itpeval-statement-checked)` followed by `:q`. This checks that ACL2 admits the
definitions and resolves every referenced function; it does not assert or
prove that the predicate is true. Do not use `defthm`, `defthmd`, `defaxiom`,
`skip-proofs`, `encapsulate`, `make-event`, event-generating macros, raw-mode
or trust-tag events, `thm`, or any equivalent proof or axiom-admission
mechanism.

For ACL2(r), follow the ACL2 event and certified-book policy above, but use
ACL2(r)'s native real and complex numbers, non-standard analysis primitives,
and pinned `nonstd` system books when the source theorem genuinely requires
analysis. Do not replace real or complex objects with rationals, coded fields,
or ad hoc completeness axioms. Keep ACL2(r) artifacts separate from ordinary
ACL2 artifacts because they require the specialized `saved_acl2r` runtime.

Apply the trust policy native to each target rather than forcing one syntactic
policy across all provers:

- Lean 4: use imports, definitions, structures/classes, namespaces, sections,
  and theorem binders. A fixed Logipedia source-signature symbol may use an
  `axiom` declaration only when it is immediately preceded by an
  `itpeval-source-signature` marker that names its indexed Logipedia
  `kind: constant` entry. Such a declaration introduces the source's symbol;
  it must not assert an additional law. Do not add any other `axiom` or
  unimplemented `constant` declaration.
- Rocq: use imports, inductives/records, definitions, and section-local
  `Variable`, `Hypothesis`, or `Context` declarations that are discharged into
  explicit parameters. Do not add global `Axiom` or `Conjecture` declarations.
- Isabelle: use imports, locales/contexts, definitions, and standard
  specification packages. Do not use `axiomatization`, `axioms`, oracles, or
  unchecked ML/setup hooks.
- HOL Light and HOL4: conservative definitions and type-definition mechanisms
  are allowed. Do not call `new_axiom`, raw theorem constructors, or oracle
  constructors.
- Agda: imports, data/record declarations, modules, parameters, and record
  fields that expose the source assumptions are allowed. Do not use
  `postulate`, holes, trusted primitives, unsafe pragmas, or compiler options
  that disable consistency checks or accept unfinished terms.
- PVS: use imports, theories, parameters, datatypes, subtypes, and definitions.
  Encode source assumptions explicitly in theory parameters or the target
  predicate; do not add `AXIOM`, `POSTULATE`, `CONJECTURE`, or an extra
  unproved formula declaration.
- ACL2: follow the certified-book and conservative-event policy above.
- ACL2(r): follow the same conservative-event policy, using only its native
  analysis primitives and certified non-standard books.
- Metamath: `$a` is also the native statement encoding, so it cannot be banned
  mechanically. Every auxiliary `$a` must be syntax or a faithful definition
  required by the target, never an extra mathematical premise.
- Mizar: use the imported MML environment, reservations, structures,
  definitions, and explicit theorem hypotheses. Do not insert unrelated
  statement-only theorems as reusable facts.

For Mizar, store a complete `.miz` article with the required `environ` declarations and no article-level closing `end;`. Represent each unproved theorem with Mizar's parser pragma:

```mizar
::$P-
theorem
  <translated statement>
proof
end;
::$P+
```

The empty block is Mizar's required statement-only encoding while proof parsing is disabled. It is not a proof and must not be reported as one.

## Semantic Reviewer

Judge strict semantic fidelity, not textual identity. ITP-specific splitting or
grouping, library equivalents, records versus predicates or modules, explicit
versus implicit contexts, renaming, auxiliary definitions, and reformulations
are acceptable only when they preserve the same proposition. Record a concrete
definitional or bidirectional logical-equivalence argument for every
nontrivial reformulation.

Check that the candidate preserves the source's mathematical objects, domains,
quantifier scopes, assumptions, conclusion, non-vacuity, and difficulty.
Treat every prohibited change listed under Translator-Verifier as substantive.
Return `REVISE` when it can be repaired and `BLOCKED` when the target or source
material cannot support a faithful statement. Do not accept a restriction of
generality merely because it is explicit, target-native, executable, or
non-vacuous.

An `ACCEPT` log must contain:

- `fidelity_checks`, with every one of these Boolean fields set to `true`:
  `all_ground_truth_read`, `source_consistent`, `domains_preserved`,
  `quantifier_scope_preserved`, `assumptions_preserved`,
  `conclusion_preserved`, `difficulty_preserved`, `non_vacuous`,
  `no_proof_or_axiom_smuggling`, `no_substantive_approximation`, and
  `staged_candidate_exact`;
- `equivalence_justification`, explaining why target-specific representation
  choices preserve the same proposition; and
- an empty `remaining_uncertainty` list.

If any fidelity check cannot honestly be set to `true`, the verdict cannot be
`ACCEPT`. In particular, an `ACCEPT` log cannot describe a "genuine
restriction of generality," unresolved semantic uncertainty, reduced
difficulty, or an approximation.

For Babel-formal, judge semantics from Lean 4 and Rocq and use Isabelle/HOL Light only as advisory references. For miniF2F, compare all available existing representations and use their common intended meaning.

Reject a candidate that lacks the required target-native statement comment, has
a stale or misleading description, mentions the translation machinery, or
omits the statement-only/no-proof qualification.

Return one verdict:

- `ACCEPT`: verified and semantically faithful under every required check;
  only equivalence-preserving differences remain.
- `REVISE`: list concrete changes for the translator.
- `BLOCKED`: explain the source conflict, target limitation, or unresolved ambiguity.

## Storage and Logs

Store accepted translations at the manifest's `candidate_path`. Standard
layouts are:

```text
data/babel-formal/data/stmts/<target>/<topic>.<target-native-extension>
data/minif2f/data/stmts/<target>/<test-or-valid>/<problem>.<target-native-extension>
data/putnambench/data/stmts/<target>/<problem>.<target-native-extension>
data/hundred-theorems/data/stmts/<target>/<number>_<slug>.<target-native-extension>
data/thousand-theorems/data/stmts/<target>/<qid>_<slug>.<target-native-extension>
data/logipedia/data/stmts/<target>/<module>/<id>.<target-native-extension>
data/ntp4vc/data/stmts/<target>/<category>/<relative-key>.<target-native-extension>
data/verina/data/stmts/<target>/<task-id>.<target-native-extension>
```

Preserve topic names, problem names, and splits. Do not store generated verifier or build outputs in these directories.

Use `corpus-extension/runs/<run-id>/tasks/<corpus>/<target>/<artifact>/` for temporary task directories and wrapper-generated files.

To avoid concurrent writes, the reviewer writes one JSON log per artifact:

```text
corpus-extension/runs/<run-id>/semantic_logs/<corpus>/<target>/<artifact>.json
```

The log records the artifact, target, candidate path, latest ITPEval result,
verdict, semantic assessment, `fidelity_checks`,
`equivalence_justification`, all noteworthy changes or discrepancies and
their rationale, requested revisions and resolutions, and any remaining
uncertainty or blocker.

An artifact is complete only when its latest candidate passes the ITPEval wrapper, its reviewer returns `ACCEPT`, its differences are logged, and it is stored at the correct path. Do not modify ground-truth files.
