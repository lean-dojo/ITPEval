$(
  Statement-only formalization of the Logipedia corpus artifact
  fermat.prime_to_not_divides_fact
  (logipedia__metamath__fermat.prime_to_not_divides_fact), catalog title
  "fermat.prime_to_not_divides_fact": if a natural number p is prime, then p
  does not divide n! for any natural number n strictly below p. This file
  contains no proof.
$)

$[ lib/set.mm $]

$(
  NN0 preserves both source natural-number domains. SetMM's Prime, strict
  order, factorial, and divisibility are the corresponding source predicates
  and operation. The nested restricted quantifiers and implications preserve
  the source scope exactly. The final declaration is an unproved $a statement
  encoding; this database contains no $p proof declaration.
$)

${
  $d n p $.

  logipedia-fermat-prime-to-not-divides-fact $a |-
    A. p e. NN0
      (
        p e. Prime
        ->
        A. n e. NN0
          (
            n < p
            ->
            -. p || ( ! ` n )
          )
      )
  $.
$}
