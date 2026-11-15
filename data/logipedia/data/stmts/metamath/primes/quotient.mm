$(
  Statement-only formalization of the Logipedia corpus artifact
  primes.quotient (logipedia__metamath__primes.quotient), catalog title
  "primes.quotient": for natural numbers n, m, and q, if m is n multiplied
  by q, then n divides m. This file contains no proof.
$)

$[ lib/set.mm $]

$(
  NN0 is SetMM's class of nonnegative integers and represents the source
  natural-number domain. For n and m in NN0, SetMM's n || m is equivalent to
  the source relation primes.divides n m, characterized by a natural
  multiplier. SetMM equality and multiplication directly represent the
  source natural-number equality and nat.times. The restricted universal
  quantifiers and nested implication preserve the source binder order,
  assumption, conclusion, and all scopes. The final declaration is
  Metamath's native unproved $a statement encoding; this database contains no
  $p proof declaration.
$)

${
  $d m n q $.

  logipedia-primes-quotient $a |-
    A. n e. NN0
      A. m e. NN0
        A. q e. NN0
          (
            m = ( n x. q )
            ->
            n || m
          )
  $.
$}
