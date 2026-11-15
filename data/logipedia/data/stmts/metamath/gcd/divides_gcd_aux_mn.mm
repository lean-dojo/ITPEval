$(
  Statement-only formalization of the Logipedia corpus artifact
  gcd.divides_gcd_aux_mn
  (logipedia__metamath__gcd.divides_gcd_aux_mn), catalog title
  "gcd.divides_gcd_aux_mn": for natural numbers p, m, and positive n with
  n at most m and p, the gcd auxiliary value gcd_aux p m n divides both m
  and n. This file contains no proof.
$)

$[ lib/set.mm $]

$(
  NN0 is SetMM's class of nonnegative integers and represents the source
  natural-number domain. LogGcdAux represents the fixed source constant
  gcd_aux with curried type NN0 -> NN0 -> NN0 -> NN0. On NN0, SetMM's
  order and divisibility predicates agree with the source natural-number
  predicates nat.lt, nat.le, and primes.divides. The restricted quantifiers,
  three nested implications, and final conjunction preserve the source scope
  exactly. Every declaration is an unproved $a statement encoding; this
  database contains no $p proof declaration.
$)

$c LogGcdAux $.

log-gcd-aux-syntax $a class ( LogGcdAux ) $.

${
  $d m n p $.

  logipedia-gcd-divides-gcd-aux-mn $a |-
    (
      ( LogGcdAux ) e.
        ( ( ( NN0 ^m NN0 ) ^m NN0 ) ^m NN0 )
      /\
      A. p e. NN0 A. m e. NN0 A. n e. NN0
        (
          0 < n
          ->
          (
            n <_ m
            ->
            (
              n <_ p
              ->
              (
                (
                  (
                    ( ( LogGcdAux ) ` p )
                    `
                    m
                  )
                  `
                  n
                )
                ||
                m
                /\
                (
                  (
                    ( ( LogGcdAux ) ` p )
                    `
                    m
                  )
                  `
                  n
                )
                ||
                n
              )
            )
          )
        )
    )
  $.
$}
