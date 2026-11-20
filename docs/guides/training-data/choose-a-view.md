# Choose a training dataset

Choose the view with the columns your trainer expects. [TRL dataset formats](https://huggingface.co/docs/trl/dataset_formats)

| Training task | Export | Main columns |
|---|---|---|
| Continued pretraining | `pretraining` | `text` with native source and provenance |
| Supervised fine-tuning | `sft` | `prompt`, `completion` for an accepted edit |
| Proof repair | `repair` | `prompt` with the unsuccessful edit and checker feedback, plus `completion` with the accepted revision |
| Paired preferences for DPO or reward modeling | `preference` | `prompt`, `chosen`, `rejected` for the same locked theorem |
| Unpaired preferences for KTO | `unpaired` | `prompt`, `completion`, `label` |
| Online reinforcement learning with GRPO | `grpo` | `prompt`, `task_id` and `environment_id` to route generated proofs to their verifier |
| Offline learning from attempts | `trajectory` | Ordered actions, observations, and rewards for each episode |
| Learning from native proof states | `proof_steps` | Current state, action, native feedback, and terminal verifier evidence |
| Premise retrieval | `retrieval` | `anchor` and `positive` with target, premise, and context IDs |

Use conversational rows if your trainer expects messages. Unknown verifier outcomes appear in trajectories with a null reward. Premises without proof-use evidence have unknown labels. [Proof rewards](../verification-and-learning/verifier-rewards.md)

## Keep related examples together

Before exporting, keep variants of one theorem, translations of the same item, and attempts from the same proof task in one split. Use `--split` to record the partition you assigned to the native inputs.

Keep source files containing held-out proofs out of the pretraining inputs. To omit files by exact content, pass `--exclude-source-hashes FILE` with one SHA-256 per line.

Keep the provenance and license notices beside the export. A dataset card can record the source projects, split policy, checker versions, and label coverage so someone loading the files knows which rows they can use. [Source notices](../../../data/third_party_licenses/README.md) · [Hugging Face dataset cards](https://huggingface.co/docs/hub/datasets-cards)

[Export a training dataset](export-a-dataset.md) from your bundles and proof attempts.
