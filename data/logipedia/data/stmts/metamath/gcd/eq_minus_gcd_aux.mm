$(
  Statement-only formalization of the Logipedia corpus artifact
  gcd.eq_minus_gcd_aux
  (logipedia__metamath__gcd.eq_minus_gcd_aux), catalog title
  "gcd.eq_minus_gcd_aux": for natural numbers p, m, and positive n with n
  at most m and p, natural coefficients make one of two truncated
  differences of multiples equal gcd_aux p m n. This file contains no proof.
$)

$[ lib/set.mm $]

$(
  NN0 is SetMM's class of nonnegative integers and represents the source
  natural-number domain. LogGcdAux represents the fixed source constant
  gcd_aux with curried type NN0 -> NN0 -> NN0 -> NN0. On NN0, SetMM
  multiplication and order agree with the source natural-number operations.
  Each conditional

    if ( y <_ x , x - y , 0 )

  is exactly the source truncated subtraction nat.minus x y. The restricted
  quantifiers, three nested implications, existential witnesses, disjunction,
  and equality preserve the source statement. Every declaration is an
  unproved $a statement encoding; this database contains no $p proof
  declaration.
$)

$c LogGcdAux $.

log-gcd-aux-syntax $a class ( LogGcdAux ) $.

${
  $d a b m n p $.

  logipedia-gcd-eq-minus-gcd-aux $a |-
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
              E. a e. NN0 E. b e. NN0
                (
                  if (
                    ( b x. m ) <_ ( a x. n ) ,
                    ( ( a x. n ) - ( b x. m ) ) ,
                    0
                  )
                  =
                  (
                    (
                      ( ( LogGcdAux ) ` p )
                      `
                      m
                    )
                    `
                    n
                  )
                  \/
                  if (
                    ( a x. n ) <_ ( b x. m ) ,
                    ( ( b x. m ) - ( a x. n ) ) ,
                    0
                  )
                  =
                  (
                    (
                      ( ( LogGcdAux ) ` p )
                      `
                      m
                    )
                    `
                    n
                  )
                )
            )
          )
        )
    )
  $.
$}
