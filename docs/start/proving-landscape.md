# The theorem proving landscape

A proof system’s **foundation** tells you what you can state and what counts as a proof. Its **workflow** tells you how you find that proof. For example, Lean checks terms in a dependent type theory and can still use automatic search to help construct them. [Lean’s type system](https://lean-lang.org/doc/reference/latest/The-Type-System/)

## Where the provers fit

<figure class="logic-map" aria-label="Foundations of the ten proof systems and how automatic search connects to verification" markdown="1">
<div class="logic-map-root">Proof assistants and formal verification systems</div>

<div class="logic-map-grid" markdown="1">

<div class="logic-map-node logic-types" markdown="1">

**[Dependent type theory](#dependent-types)**<br>
Terms can appear in types.

[Lean 4](../provers/lean4.md) · [Rocq](../provers/rocq.md) · [Agda](../provers/agda.md)

</div>
<div class="logic-map-node logic-hol" markdown="1">

**[Higher-order logic](#higher-order-logic)**<br>
Quantify over functions and predicates.

[Isabelle/HOL](../provers/isabelle.md) · [HOL4](../provers/hol4.md) · [HOL Light](../provers/hol-light.md) · [PVS](../provers/pvs.md)

</div>
<div class="logic-map-node logic-sets" markdown="1">

**[Set theory and axiomatic databases](#sets-and-axioms)**<br>
Track the axioms and rules of a library.

[Mizar](../provers/mizar.md) · [Metamath](../provers/metamath.md)

</div>
<div class="logic-map-node logic-programs" markdown="1">

**[First-order logic of programs](#first-order-program-reasoning)**<br>
Prove properties of recursive functions.

[ACL2](../provers/acl2.md)

</div>
</div>

<div class="logic-map-search" markdown="1">

**[Automatic theorem provers](#automatic-search)**<br>
E and Vampire search for a proof from supplied facts.

</div>

<figcaption>The groups describe the systems and libraries covered here. The arrows below describe a proof workflow.</figcaption>

</figure>

## Dependent types

A type can depend on a value. For example, $\operatorname{Vec}(A,n)$ describes a vector of elements of type $A$ whose length is $n$. An append function can describe the result length $m+n$ in its type. A proof is a term of the type that expresses the claim. Lean, Rocq and Agda share this broad idea and have their own core rules and available axioms. [Lean reference](https://lean-lang.org/doc/reference/latest/The-Type-System/) · [Rocq core language](https://rocq-prover.org/doc/V9.2.0/refman/language/core/index.html) · [What is Agda?](https://agda.readthedocs.io/en/stable/getting-started/what-is-agda.html)

## Higher-order logic

HOL systems have typed functions and can quantify over functions and predicates. Isabelle is a logical framework, and Isabelle/HOL is the object logic used by ITPEval’s Isabelle examples. HOL4 and HOL Light implement their own HOL systems. PVS uses typed higher-order logic and adds facilities such as predicate subtypes. For example, the type of positive integers can create an obligation to prove that a returned integer is positive. [Isabelle overview](https://isabelle.in.tum.de/overview.html) · [HOL4 manual](https://hol-theorem-prover.org/docs/trindemossen-2/) · [HOL Light](https://hol-light.github.io/) · [PVS introduction](https://pvs.csl.sri.com/introduction.shtml)

## Sets and axioms

The Mizar Mathematical Library rests on Tarski–Grothendieck set theory. Mizar verifies proofs written as structured articles. Metamath checks substitutions and proof steps against the axioms and rules written in the selected database. Its `set.mm` database develops classical mathematics from set theory, and other Metamath databases can use other foundations. [Mizar Mathematical Library](https://mizar.uwb.edu.pl/library/) · [Metamath Proof Explorer](https://us.metamath.org/mpeuni/mmset.html)

## First-order program reasoning

ACL2 combines a first-order logic of recursive functions with an executable language. You submit a `defthm` event and ACL2 tries to prove it, using induction, rewriting, and other procedures. A user can guide the search with hints or use the interactive proof builder. [ACL2 logic](https://acl2.org/doc/index-seo.php?xkey=ACL2____QUANTIFIER-TUTORIAL) · [Proof builder](https://acl2.org/doc/index-seo.php?xkey=ACL2____PROOF-BUILDER)

## Automatic search

An automatic theorem prover (ATP) searches for a derivation from a conjecture and axioms. You can give E or Vampire a standalone problem. From a proof assistant, a bridge such as Isabelle’s Sledgehammer translates the goal and selected facts, then helps recover a proof the original assistant can check. [TPTP language](https://tptp.org/UserDocs/QuickGuide/) · [Sledgehammer guide](https://isabelle.in.tum.de/website-Isabelle2019/dist/Isabelle2019/doc/sledgehammer.pdf) · [Lean Vampire-Hammer](https://arxiv.org/abs/2610.40310)

<ol class="logic-map-flow" aria-label="How a proof assistant and an automated prover work together">
  <li><strong>Start with a goal</strong><span>The assistant knows the local hypotheses and imports.</span></li>
  <li><strong>Search with an ATP</strong><span>The bridge sends a translated problem and its selected facts.</span></li>
  <li><strong>Recover a proof</strong><span>Turn solver output into a proof the assistant understands.</span></li>
  <li><strong>Check the original goal</strong><span>Save native evidence for the exact theorem and environment.</span></li>
</ol>

ITPEval can search reviewed states in all ten built-in provers. Its E and Vampire bridges cover supported goals in Lean 4, Rocq, Agda, PVS, HOL4, and Isabelle/HOL. For example, Agda can export local implications from a typed hole, and PVS can export Boolean hypotheses from a focused sequent. [Search during a proof](../guides/automated-proving/search-a-proof-state.md) · [Capabilities by prover](../reference/capabilities.md)
