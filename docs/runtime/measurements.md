# Runtime measurements

Choose the workload closest to yours. The trial records give the exact toolchains, inputs, and timing scopes.

- <span id="throughput-on-distinct-proof-tasks"></span><span id="faster-lock-validation"></span><span id="longer-queues"></span><span id="mixed-prover-queue-latency"></span><span id="proof-completions"></span>[Throughput and queue latency](measurements/throughput.md) — Compare worker caps on new candidates and time to first verdict in mixed-prover queues.
- <span id="fresh-native-startup"></span><span id="loading-a-project-and-reusing-a-verification-result"></span><span id="reusing-dependencies-for-a-changed-candidate"></span><span id="warm-workers-in-the-paper"></span>[Startup and caching](measurements/startup-and-caching.md) — Compare fresh starts, cached results, compiled imports, and warm workers.
- <span id="restore-a-pvs-action-checkpoint"></span><span id="restore-acl2-metamath-and-rocq-checkpoints"></span><span id="restore-a-lean-tactic-checkpoint"></span><span id="fork-a-lean-or-rocq-proof-session"></span><span id="fork-a-metamath-search-state"></span><span id="automated-search-and-native-replay"></span>[Interactive proof benchmarks](measurements/proof-sessions.md) — Time checkpoint replay, branches from open goals, and Isabelle search with native replay.
- <span id="library-checks"></span><span id="building-a-library-retrieval-index"></span><span id="compact-metamath-extraction"></span><span id="comparing-verifiers-on-the-same-library"></span>[Library checks and extraction](measurements/libraries.md) — Compare whole-database verification, library checks, extraction, and retrieval indexing.

The project-loading, cache and same-database trials used a shared Linux x86-64 host with an AMD EPYC 7742, 64 physical cores, 128 logical CPUs and Python 3.13.12.
