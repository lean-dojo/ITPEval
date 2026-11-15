$(
  Statement-only formalization of the Logipedia corpus artifact
  exp.sym_eq_exp_body_S (logipedia__metamath__exp.sym_eq_exp_body_S),
  catalog title "exp.sym_eq_exp_body_S": for all natural numbers n and m,
  exp at n and m multiplied by n is Leibniz equal to exp_body at n and the
  successor of m. This file contains no proof.
$)

$[ lib/set.mm $]

$(
  LogExp and LogExpBody represent the fixed source constants of type

    NN0 -> NN0 -> NN0.

  LogNatUnaryFunction and LogNatBinaryFunction explicitly encode those
  curried function spaces. SetMM's m + 1 is the source successor nat.S m,
  and SetMM multiplication preserves the source argument order
  nat.times (exp n m) n. A predicate on the natural-number carrier is
  represented extensionally by a subset p of NN0. Thus universal transport
  of membership from (exp n m) * n to exp_body n (S m) is exactly the source
  definition of leibniz.leibniz at nat.nat. Every declaration is an unproved
  $a statement encoding; this database contains no $p proof declaration.
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
  $d m n p $.

  logipedia-exp-sym-eq-exp-body-s $a |-
    (
      (
        ( LogExp ) e. ( LogNatBinaryFunction )
        /\
        ( LogExpBody ) e. ( LogNatBinaryFunction )
      )
      /\
      A. n e. NN0 A. m e. NN0
        A. p e. ~P NN0
          (
            ( ( ( ( LogExp ` n ) ` m ) x. n ) e. p )
            ->
            ( ( ( LogExpBody ` n ) ` ( m + 1 ) ) e. p )
          )
    )
  $.
$}
