$(
  Statement-only formalization of the Logipedia corpus artifact
  primes.reflexive_divides
  (logipedia__metamath__primes.reflexive_divides), catalog title
  "primes.reflexive_divides": divisibility on natural numbers is reflexive,
  so every natural number divides itself. This file contains no proof.
$)

$[ lib/set.mm $]

$(
  The source relation is characterized by a natural multiplier: divides n m
  exactly when some natural q satisfies m = n x. q. SetMM's NN0 is the class
  of nonnegative integers representing the source natural-number domain, and
  n || n has that same multiplier characterization. Thus the restricted
  universal statement below is definitionally the source proposition
  relations.reflexive nat divides. The final declaration is Metamath's native
  unproved $a statement encoding; this database contains no $p proof
  declaration.
$)

logipedia-primes-reflexive-divides $a |-
  A. n e. NN0 n || n
$.
