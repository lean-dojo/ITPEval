$(
  Statement-only formalization of the Logipedia corpus artifact
  exp.axiom_exp_body_O (logipedia__metamath__exp.axiom_exp_body_O),
  catalog title "exp.axiom_exp_body_O": for every natural number n, the
  exponentiation body at n and zero equals the successor of zero. This file
  contains no proof.
$)

$[ lib/set.mm $]

$(
  LogExpBody represents the fixed source constant of type

    NN0 -> NN0 -> NN0.

  LogNatUnaryFunction and LogNatBinaryFunction explicitly encode the source's
  curried natural-number function spaces. The numeral 1 is the SetMM natural
  number corresponding to the source term nat.S nat.O. Native SetMM equality
  is bidirectionally equivalent to connectives.equal here: equal_leibniz
  yields native equality, while native equality rewrites the right side to the
  left and refl_equal supplies source reflexivity. All declarations are
  unproved $a statement encodings; this database contains no $p proof
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

logipedia-exp-axiom-exp-body-o $a |-
  (
    ( LogExpBody ) e. ( LogNatBinaryFunction )
    /\
    A. n e. NN0
      ( ( ( LogExpBody ` n ) ` 0 ) = 1 )
  )
$.
