$(
  Statement-only formalization of the Logipedia corpus artifact
  exp.sym_eq_exp_body_O (logipedia__metamath__exp.sym_eq_exp_body_O),
  catalog title "exp.sym_eq_exp_body_O": for every natural number n, the
  successor of zero is Leibniz equal to the exponentiation body at n and
  zero. This file contains no proof.
$)

$[ lib/set.mm $]

$(
  LogExpBody represents the fixed source constant of type

    NN0 -> NN0 -> NN0.

  LogNatUnaryFunction and LogNatBinaryFunction explicitly encode the source's
  curried natural-number function spaces. The numeral 1 is the SetMM natural
  number corresponding to the source term nat.S nat.O. A predicate on the
  natural-number carrier is represented extensionally by a subset p of NN0.
  Thus universal transport of membership from 1 to exp_body n 0 is exactly
  the source definition of leibniz.leibniz at nat.nat. Every declaration is
  an unproved $a statement encoding; this database contains no $p proof
  declaration.
$)

$c LogExpBody LogNatUnaryFunction LogNatBinaryFunction $.

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
  $d n p $.

  logipedia-exp-sym-eq-exp-body-o $a |-
    (
      ( LogExpBody ) e. ( LogNatBinaryFunction )
      /\
      A. n e. NN0
        A. p e. ~P NN0
          (
            ( 1 e. p )
            ->
            ( ( ( LogExpBody ` n ) ` 0 ) e. p )
          )
    )
  $.
$}
