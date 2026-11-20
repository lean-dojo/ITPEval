# Library extraction and datasets

An extraction bundle records declarations, source locations, and premises visible at each theorem. It also records proof references where the prover exposes them.

- <span id="export-a-library"></span><span id="extract-a-large-metamath-database"></span><span id="export-parquet"></span>[Extract a library](extract-and-build-a-dataset/extract-a-library.md) from a bundled example or your own project. Choose JSONL or Parquet and use compact contexts for large Metamath databases.
- <span id="read-an-extraction-bundle"></span><span id="look-up-premises-visible-at-a-theorem"></span>[Read an extraction bundle](extract-and-build-a-dataset/read-a-bundle.md) to check file coverage, follow source locations, and retrieve premises in scope.
- <span id="native-evidence-by-prover"></span>[Find native evidence by prover](extract-and-build-a-dataset/native-evidence.md), including Lean proof spans, Rocq goals, ACL2 rule use, and Metamath proof stacks.
- <span id="combine-libraries-across-provers"></span>[Combine libraries across provers](extract-and-build-a-dataset/combine-libraries.md) with one catalog that preserves revisions, source locations, and environment IDs.
- <span id="import-the-released-benchmark"></span><span id="keep-related-tasks-in-the-same-split"></span><span id="read-the-review-and-source-records"></span>[Import the released benchmark](extract-and-build-a-dataset/import-the-benchmark.md) to work with aligned artifacts, reviewed correspondences, and the original partitions.

To turn the output into examples for a model trainer, [choose a training dataset](training-data/choose-a-view.md).
