$(
  Statement-only formalization of the Logipedia corpus artifact
  exp.axiom_exp_body_S (logipedia__metamath__exp.axiom_exp_body_S),
  catalog title "exp.axiom_exp_body_S": for all natural numbers n and m,
  exp_body at n and the successor of m equals exp at n and m multiplied
  by n. This file contains no proof.
$)

$[ lib/set.mm $]

$(
  LogExp and LogExpBody represent the fixed source constants of type

    NN0 -> NN0 -> NN0.

  LogNatUnaryFunction and LogNatBinaryFunction explicitly encode those
  curried function spaces. SetMM's m + 1 is the source successor nat.S m,
  and SetMM multiplication preserves the source argument order
  nat.times (exp n m) n. Native SetMM equality is bidirectionally
  equivalent to connectives.equal at the natural-number type by the
  catalogued equality correspondence. All declarations are unproved $a
  statement encodings; this database contains no $p proof declaration.
$)

$c LogExp LogExpBody LogNatUnaryFunction LogNatBinaryFunction $.

log-exp-syntax $a class ( LogExp ) $.
log-exp-body-syntax $a class ( LogExpBody ) $.
log-nat-unary-function-syntax $a class ( LogNatUnaryFunction ) $.
log-nat-binary-function-syntax $a class ( LogNatBinaryFunction ) $.

log-nat-unary-function-definition $a |-
  ( LogNatUnaryFunction ) = ( NN0 ^m NN0 )
$.

log-nat-binary-function-definition $a |-
  ( LogNatBinaryFunction ) =
    ( ( LogNatUnaryFunction ) ^m NN0 )
$.

${
  $d m n $.

  logipedia-exp-axiom-exp-body-s $a |-
    (
      (
        ( LogExp ) e. ( LogNatBinaryFunction )
        /\
        ( LogExpBody ) e. ( LogNatBinaryFunction )
      )
      /\
      A. n e. NN0 A. m e. NN0
        (
          ( ( LogExpBody ` n ) ` ( m + 1 ) )
          =
          ( ( ( LogExp ` n ) ` m ) x. n )
        )
    )
  $.
$}
