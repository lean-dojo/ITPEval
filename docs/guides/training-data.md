# Training datasets

Build training data from [library extractions](extract-and-build-a-dataset.md), [recorded proof attempts](verification-and-learning/check-and-replay.md#save-and-replay-an-episode), and native proof sessions. Each export writes JSONL or Parquet with columns for your training task.

- <span id="choose-a-dataset-for-your-task"></span><span id="keep-related-examples-together"></span>[Choose a training dataset](training-data/choose-a-view.md) for pretraining, fine-tuning, proof repair, preference training, reinforcement learning, or premise retrieval.
- <span id="export-a-native-dataset"></span><span id="export-native-goal-and-action-data"></span>[Export a training dataset](training-data/export-a-dataset.md) from library bundles, verifier feedback, and native goal/action records.
- <span id="load-the-rows-in-hugging-face"></span>[Load datasets in Hugging Face](training-data/load-datasets.md), including prompt exports for live verifier rewards with GRPO.
- <span id="export-the-translation-benchmark"></span>[Export benchmark views](training-data/export-the-benchmark.md) for formalization and translation.
