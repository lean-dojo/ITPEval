---
name: extract-a-library
description: Extract declarations and visible context from a pinned ITPEval library project and export premise-selection or training data with provenance.
---

# Extract a library

Run from an ITPEval checkout. For an installed copy of this skill, resolve the guide links from `docs/agents/skills/extract-a-library/SKILL.md` in that checkout.

1. Find the prover, project root, source entrypoint, and native dependencies. Choose an entrypoint from the library itself when you need its declarations. Use `itpeval prepare PROVER --project DIR --cache CACHE` or reuse the provided lock. [Project configuration](../../../guides/environment-manifest.md)
2. Run `itpeval extract --lock LOCK --entrypoint FILE --output DIRECTORY` for the extraction bundle. Use `itpeval dataset --lock LOCK --entrypoint FILE --output DIRECTORY` to add premise-selection records. Supply a project-relative entrypoint. [Extract a library](../../../guides/extract-and-build-a-dataset/extract-a-library.md)
3. Read the bundle's `report.json` for file coverage, skipped units, and field availability. Keep each row's declaration ID, environment ID, and source locator with the output. Report the bundle path and any relevant coverage gaps. [Read an extraction bundle](../../../guides/extract-and-build-a-dataset/read-a-bundle.md)

## Premise retrieval and combined exports

Restrict premise lookup by the target's environment and context IDs. Keep `available`, `retrieved`, and `proof_used` separate. Inspect `proof_used_availability` before labeling a missing proof reference. [Scoped premise lookup](../../../guides/extract-and-build-a-dataset/read-a-bundle.md#look-up-premises-visible-at-a-theorem)

For a large Metamath database, pass `--context-storage compact`. In premise rows, resolve `available: null` with `declaration.context_id` and `ContextTable(bundle)` in the original bundle. For multi-library exports, combine extracts with `itpeval training-data libraries --catalog CATALOG --output DIRECTORY`. Add `--premise-visibility reference` to retain context references without expanding the visibility lists. [Compact contexts](../../../guides/extract-and-build-a-dataset/extract-a-library.md#extract-a-large-metamath-database) · [Combine libraries](../../../guides/extract-and-build-a-dataset/combine-libraries.md)
