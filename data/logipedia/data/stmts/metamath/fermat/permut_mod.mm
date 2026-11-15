$(
  Statement-only formalization of the Logipedia corpus artifact
  fermat.permut_mod (logipedia__metamath__fermat.permut_mod), catalog title
  "fermat.permut_mod": multiplication by a natural number not divisible by a
  prime, followed by reduction modulo that prime, permutes the natural
  residues below the prime. This file contains no proof.
$)

$[ lib/set.mm $]

$(
  NN0 preserves every source natural-number domain. Under the prime
  antecedent, i < p is equivalent to i <= pred(p). The two conclusion
  conjuncts directly unfold permutation.permut: the first says the
  beta-reduced source function maps that initial segment into itself, and the
  second says its restriction to the segment is injective. SetMM's remainder,
  multiplication, primality, and divisibility are the corresponding source
  operations and predicates. The final declaration is an unproved $a
  statement encoding; this database contains no $p proof declaration.
$)

${
  $d a i j p $.

  logipedia-fermat-permut-mod $a |-
    A. p e. NN0
      A. a e. NN0
        (
          p e. Prime
          ->
          (
            -. p || a
            ->
            (
              A. i e. NN0
                (
                  i < p
                  ->
                  ( ( ( a x. i ) mod p ) < p )
                )
              /\
              A. i e. NN0
                A. j e. NN0
                  (
                    (
                      ( i < p /\ j < p )
                      /\
                      (
                        ( ( a x. i ) mod p )
                        =
                        ( ( a x. j ) mod p )
                      )
                    )
                    ->
                    i = j
                  )
            )
          )
        )
  $.
$}
