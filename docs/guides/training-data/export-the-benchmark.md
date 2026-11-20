# Export benchmark views

Benchmark views use `text` or `prompt` and `completion` columns for evaluating models and testing data pipelines. Keep their original partitions and provenance for benchmark comparisons. [Released corpus and proof coverage](../../benchmarks/translation.md#dataset-scope)

```bash
# Import the archived corpus and preserve its item identities.
python -m itpeval.corpus.importers.itpeval . build/benchmark-corpus
# Export the aligned statement references in prompt/completion format.
itpeval training-data benchmark --corpus build/benchmark-corpus \
  --include-benchmark-references --view statement_translation_reference \
  --output build/benchmark-training --format parquet
```

If you already imported the corpus, reuse its directory.

| Benchmark view | What it contains |
|---|---|
| `pretraining_reference` | Native source artifacts from the released benchmark |
| `statement_translation_reference` | Aligned statements in two prover languages |
| `statement_translation_reviewed` | Directed statement pairs with matching semantic review and native checker evidence |
| `proof_translation_reference` | Proofs from the four-prover proof archive |
| `formalization_reference` and `informalization_reference` | Released English and formal statement pairs, in either direction |

Keep the released benchmark out of training when you plan to evaluate on it. Each view writes one file per populated partition. The `train` partition name in a reference export comes from the corpus assignment, and every row retains `reference_only=true`. Statement alignment groups artifacts under the same item ID. The reviewed translation view requires evidence for the directed pair.
