$(
  Statement-only formalization of the Logipedia corpus artifact
  primes.match_divides_prop
  (logipedia__metamath__primes.match_divides_prop), catalog title
  "primes.match_divides_prop": elimination of natural-number divisibility
  into an arbitrary proposition from every quotient witness. This file
  contains no proof.
$)

$[ lib/set.mm $]

$(
  NN0 is SetMM's class of nonnegative integers and represents the source
  natural-number domain. For n and m in NN0, SetMM's n || m is equivalent to
  the source relation primes.divides n m, characterized by a natural
  multiplier q satisfying m = n x. q.

  Metamath's wff metavariable ph ranges schematically over the source
  return_type : Prop. The condition $d q ph ensures that return_type is
  independent of the internally quantified quotient witness, while allowing
  it to depend on the preceding n and m binders. The restricted quantifiers
  and nested implications preserve the source binder order, continuation,
  divisibility assumption, conclusion, and scopes. The final declaration is
  Metamath's native unproved $a statement encoding; this database contains no
  $p proof declaration.
$)

${
  $d m n q $.
  $d q ph $.

  logipedia-primes-match-divides-prop $a |-
    A. n e. NN0
      A. m e. NN0
        (
          (
            A. q e. NN0
              ( m = ( n x. q ) -> ph )
          )
          ->
          ( n || m -> ph )
        )
  $.
$}
