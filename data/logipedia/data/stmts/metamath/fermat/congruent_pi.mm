$(
  Statement-only formalization of the Logipedia corpus artifact
  fermat.congruent_pi (logipedia__metamath__fermat.congruent_pi), catalog
  title "fermat.congruent_pi": reducing each term of a finite product of
  natural numbers modulo a positive modulus preserves the product's
  congruence modulo that modulus. This file contains no proof.
$)

$[ lib/set.mm $]

$(
  NN0 and ( NN0 ^m NN0 ) preserve the source natural-number and total-function
  domains. The source bigop has base one, multiplication, an always-true
  filter, and indices below n, so it is exactly the finite product over
  0 ..^ n. The source congruence predicate is unfolded as equality of
  remainders modulo p. The final declaration is an unproved $a statement
  encoding; this database contains no $p proof declaration.
$)

${
  $d f i n p $.

  logipedia-fermat-congruent-pi $a |-
    A. f e. ( NN0 ^m NN0 )
      A. n e. NN0
        A. p e. NN0
          (
            0 < p
            ->
            (
              ( ( prod_ i e. ( 0 ..^ n ) ( f ` i ) ) mod p )
              =
              (
                (
                  prod_ i e. ( 0 ..^ n )
                    ( ( f ` i ) mod p )
                )
                mod p
              )
            )
          )
  $.
$}
