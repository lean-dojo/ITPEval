$(
  Statement-only formalization of the Logipedia corpus artifact
  gcd.axiom_gcd_aux_body_S
  (logipedia__metamath__gcd.axiom_gcd_aux_body_S), catalog title
  "gcd.axiom_gcd_aux_body_S": for every natural number p, the gcd auxiliary
  body at the successor of p is the binary function that returns n when the
  total remainder of m modulo n is zero and otherwise returns gcd_aux p n
  applied to that remainder. This file contains no proof.
$)

$[ lib/set.mm $]

$(
  LogGcdAux and LogGcdAuxBody represent the fixed source constants of type

    NN0 -> NN0 -> NN0 -> NN0.

  LogNatBinaryFunction is the curried function space NN0 -> NN0 -> NN0,
  and LogNatToBinaryFunction is NN0 -> LogNatBinaryFunction. The term

    if ( n = 0 , m , ( m mod n ) )

  is exactly the source's total div_mod.mod m n. Since primes.dividesb n m
  is nat.eqb of that remainder with zero, the outer SetMM conditional is
  exactly bool.match_bool_type with true branch n and false branch
  gcd_aux p n (div_mod.mod m n). Native SetMM equality represents the source
  connectives.equal at the binary-function type through the catalogued
  bidirectional equality correspondence. All declarations are unproved $a
  statement encodings; this database contains no $p proof declaration.
$)

$c
  LogGcdAux LogGcdAuxBody
  LogNatBinaryFunction LogNatToBinaryFunction
$.

log-gcd-aux-syntax $a class ( LogGcdAux ) $.
log-gcd-aux-body-syntax $a class ( LogGcdAuxBody ) $.
log-nat-binary-function-syntax $a class ( LogNatBinaryFunction ) $.
log-nat-to-binary-function-syntax $a class
  ( LogNatToBinaryFunction )
$.

log-nat-binary-function-definition $a |-
  ( LogNatBinaryFunction ) =
    ( ( NN0 ^m NN0 ) ^m NN0 )
$.

log-nat-to-binary-function-definition $a |-
  ( LogNatToBinaryFunction ) =
    ( ( LogNatBinaryFunction ) ^m NN0 )
$.

${
  $d m n p $.

  logipedia-gcd-axiom-gcd-aux-body-s $a |-
    (
      (
        ( LogGcdAux ) e. ( LogNatToBinaryFunction )
        /\
        ( LogGcdAuxBody ) e. ( LogNatToBinaryFunction )
      )
      /\
      A. p e. NN0
        ( ( LogGcdAuxBody ) ` ( p + 1 ) ) =
          (
            m e. NN0 |->
              (
                n e. NN0 |->
                  if (
                    if (
                      n = 0 ,
                      m ,
                      ( m mod n )
                    )
                    =
                    0 ,
                    n ,
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
    )
  $.
$}
