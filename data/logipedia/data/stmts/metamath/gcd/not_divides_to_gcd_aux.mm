$(
  Statement-only formalization of the Logipedia corpus artifact
  gcd.not_divides_to_gcd_aux
  (logipedia__metamath__gcd.not_divides_to_gcd_aux), catalog title
  "gcd.not_divides_to_gcd_aux": for natural numbers p, m, and positive n,
  if n does not divide m, then gcd_aux at successor p on m and n equals
  gcd_aux at p on n and the total remainder of m modulo n. This file
  contains no proof.
$)

$[ lib/set.mm $]

$(
  NN0 is SetMM's class of nonnegative integers and represents the source
  natural-number domain. LogGcdAux represents the fixed source constant
  gcd_aux with curried type NN0 -> NN0 -> NN0 -> NN0. SetMM addition by one
  represents nat.S, strict order and divisibility agree with nat.lt and
  primes.divides on NN0, and native equality represents logic.eq. The term

    if ( n = 0 , m , ( m mod n ) )

  is exactly the source's total div_mod.mod m n. The restricted quantifiers
  and two nested implications preserve the source scope exactly. Every
  declaration is an unproved $a statement encoding; this database contains
  no $p proof declaration.
$)

$c LogGcdAux $.

log-gcd-aux-syntax $a class ( LogGcdAux ) $.

${
  $d m n p $.

  logipedia-gcd-not-divides-to-gcd-aux $a |-
    (
      ( LogGcdAux ) e.
        ( ( ( NN0 ^m NN0 ) ^m NN0 ) ^m NN0 )
      /\
      A. p e. NN0 A. m e. NN0 A. n e. NN0
        (
          0 < n
          ->
          (
            -. n || m
            ->
            (
              (
                (
                  ( LogGcdAux )
                  `
                  ( p + 1 )
                )
                `
                m
              )
              `
              n
            )
            =
            (
              (
                ( ( LogGcdAux ) ` p )
                `
                n
              )
              `
              if (
                n = 0 ,
                m ,
                ( m mod n )
              )
            )
          )
        )
    )
  $.
$}
