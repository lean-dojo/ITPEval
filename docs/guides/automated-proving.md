# Automated proof search

Search a reviewed proof state in any of the ten built-in provers. E and Vampire support goals in Lean 4, Rocq, Agda, PVS, HOL4, and Isabelle/HOL through prover-specific bridges. [How interactive and automatic provers work together](../start/proving-landscape.md#automatic-search)

<span id="solve-a-tptp-problem"></span>

[Run a solver on TPTP](automated-proving/run-a-solver.md)
:   Submit a standalone problem to E or Vampire and read its search receipt.

<span id="search-and-replay-in-isabelle"></span>
<span id="search-and-replay-in-lean"></span>
<span id="search-and-replay-in-rocq"></span>
<span id="use-the-python-api"></span>
<span id="search-agda-and-pvs-goals-with-e-or-vampire"></span>

[Use a prover bridge](automated-proving/prover-bridges.md)
:   Send a supported native goal to a solver and check the proposed proof in the original project.

<span id="ask-an-atp-during-an-interactive-proof"></span>
<span id="search-one-hol-subgoal"></span>

[Search from a proof state](automated-proving/search-a-proof-state.md)
:   Introduce a hypothesis, focus a subgoal, or resume a checkpoint before asking for a suggestion.

<span id="search-with-native-actions"></span>

[Search with native actions](automated-proving/native-actions.md)
:   Try a prover’s own tactics, terms, assignments, or references on a fork.

<span id="explore-alternate-proof-branches"></span>
<span id="export-replayed-suggestions-for-training"></span>

[Branch and replay](automated-proving/branch-and-replay.md)
:   Try several continuations, inspect the attempts, and recheck the winning proof for a training episode.
