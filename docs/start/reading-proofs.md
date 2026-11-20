# How to read a proof

Suppose we define the *next index* of $n$ to be $n + 1$. The first declaration below gives that operation a name. The second proves what happens when you call it on zero.

```lean4
-- Define the next index of a natural number.
def nextIndex (n : Nat) : Nat := n + 1

-- State the equality, then give its proof on the indented line.
theorem next_index_zero : nextIndex 0 = 1 := by
  rfl
```

**Definition.** `def` introduces `nextIndex`. It takes a natural number `n` and returns `n + 1`. On this line, the part after `:=` tells Lean how to compute the result.

**Statement.** The name of the theorem is `next_index_zero`. Read between `:` and `:=` to find its claim, `nextIndex 0 = 1`.

**Proof.** The expression after `:=` proves the claim. Here `by` starts a tactic block and `rfl` closes it. Lean computes both sides of the equality to the same value. Reflexivity is the rule that a value equals itself.

## What is a proof explanation?

Here is the reasoning in English, one step at a time.

1. We want to show `nextIndex 0 = 1`.
2. Use the definition of `nextIndex` with `n = 0`. The left side becomes `0 + 1`.
3. Compute the sum. The goal is now `1 = 1`, which is true by reflexivity.

A proof explanation walks through the reasoning in English. The tactic is the instruction Lean uses to build the proof. An English rendering of the *statement* says “the next index of zero is one.” The benchmark calls generating that English statement *auto-informalization*. [Formalization and translation](../guides/formalization-and-translation.md#auto-informalization) · [Lean’s guide to proofs](https://lean-lang.org/theorem_proving_in_lean4/Propositions-and-Proofs/)

## What is a lemma?

A **lemma** is a proved result used to help establish another result. In the library, Lean names the theorem above `Counts.next_index_zero`. A second theorem uses that name as its entire proof. Here is its declaration in the client file.

<figure class="proof-listing" data-listing="lean4" data-proof="Counts.next_index_zero" markdown="1">

<figcaption markdown="span"><strong>Lean 4</strong> [Client.lean](../../itpeval/tests/fixtures/projects/lean4/library/Client.lean)</figcaption>

```lean4
-- The helper already proves precisely the equality this client needs.
theorem first_successor : Counts.nextIndex 0 = 1 := Counts.next_index_zero
```

</figure>

The proof is the name `Counts.next_index_zero` to the right of `:=`. Lean looks up the lemma and checks that it already proves the required claim. Follow the name into `Counts.lean` to find the original `rfl` proof. [Read Counts.lean](../../itpeval/tests/fixtures/projects/lean4/library/Counts.lean)

## Where do I find the proof in ITPEval?

The proof can look different in each language. In Agda, a proof of equality is a term of an equality type, such as `refl` for `true ≡ true`. Metamath proofs list the labels of rules and hypotheses in the order they are applied. An ACL2 theorem event can ask the prover to find a proof itself. The prover guides underline the proof whenever it appears in the source. [Agda example](../provers/agda.md#read-a-proof) · [Metamath example](../provers/metamath.md#read-a-proof) · [ACL2 example](../provers/acl2.md#read-a-proof)

In a **library export**, `statement` contains what the declaration says and `checking_status` records what the prover checked. For a Lean theorem with a recorded proof range, you can also print the exact proof from the stored source. In the example above the output is `Counts.next_index_zero`. [See the proof text in a Lean export](../provers/lean4.md#see-the-original-proof-text)

Try breaking a proof on purpose. Read what the checker says, then fix it and watch the verdict change. You can do that in the browser or in a practice file. :) [Choose a proof exercise](proof-completion.md#choose-your-prover)
