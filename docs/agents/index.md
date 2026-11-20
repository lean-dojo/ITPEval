# Agent skills

Give your agent the skill that matches the task. For a new prover, start with a native file checker. [Sprig example](sprig.md)

| Task | Skill |
|---|---|
| Connect a checker for a new proof language | [Integrate a prover](skills/integrate-a-prover/SKILL.md) |
| Convert between English and formal mathematics, or between two provers | [Formalize and translate](skills/formalize-and-translate/SKILL.md) |
| Check a file, repair a locked theorem, or try automated proof search | [Check and repair proofs](skills/check-and-repair-proofs/SKILL.md) |
| Extract declarations, premises, or training inputs from libraries | [Extract a library](skills/extract-a-library/SKILL.md) |
| Collect and replay proof episodes or train with native verifier rewards | [Train a proof agent](skills/train-a-proof-agent/SKILL.md) |

In an ITPEval checkout, ask the agent to read `docs/agents/skills/<skill-name>/SKILL.md` and run its commands from the repository root. Clients that discover `.agents/skills` can load the same files there.

To install the downloadable skills in another location, unpack the five folders into your agent client's skills directory. Work from the ITPEval checkout and use the linked guides from the checkout's copy of each skill. [Download the five skills](../assets/itpeval-agent-skills.zip) · [Agent Skills specification](https://agentskills.io/specification)
