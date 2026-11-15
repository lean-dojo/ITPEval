$(
  Statement-only formalization of the Logipedia corpus artifact
  gcd.divides_to_gcd_aux
  (logipedia__metamath__gcd.divides_to_gcd_aux), catalog title
  "gcd.divides_to_gcd_aux": for natural numbers p, m, and n, if p and n
  are positive and n divides m, then gcd_aux p m n equals n. This file
  contains no proof.
$)

$[ lib/set.mm $]

$(
  NN0 is SetMM's class of nonnegative integers and represents the source
  natural-number domain. LogGcdAux represents the fixed source constant
  gcd_aux with curried type NN0 -> NN0 -> NN0 -> NN0. On NN0, SetMM's
  strict order and divisibility predicates agree with the source predicates
  nat.lt and primes.divides, and native equality represents logic.eq. The
  restricted quantifiers and three nested implications preserve the source
  scope exactly. Every declaration is an unproved $a statement encoding;
  this database contains no $p proof declaration.
$)

$c LogGcdAux $.

log-gcd-aux-syntax $a class ( LogGcdAux ) $.

${
  $d m n p $.

  logipedia-gcd-divides-to-gcd-aux $a |-
    (
      ( LogGcdAux ) e.
        ( ( ( NN0 ^m NN0 ) ^m NN0 ) ^m NN0 )
      /\
      A. p e. NN0 A. m e. NN0 A. n e. NN0
        (
          0 < p
          ->
          (
            0 < n
            ->
            (
              n || m
              ->
              (
                (
                  ( ( LogGcdAux ) ` p )
                  `
                  m
                )
                `
                n
              )
              =
              n
            )
          )
        )
    )
  $.
$}
