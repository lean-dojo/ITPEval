$(
  Statement-only formalization of the Logipedia corpus artifact
  nat.axiom_plus_body_S
  (logipedia__metamath__nat.axiom_plus_body_S), catalog title
  "nat.axiom_plus_body_S": for every natural number n, the addition body at
  successor n equals the function mapping each natural m to the successor of
  plus n m. This file contains no proof.
$)

$[ lib/set.mm $]

$(
  LogPlus and LogPlusBody represent the fixed source constants of type

    NN0 -> NN0 -> NN0.

  LogNatUnaryFunction and LogNatBinaryFunction explicitly encode the source's
  curried natural-number function spaces. The maps-to term preserves the
  source lambda over every natural m, and n + 1 is the natural-number
  successor S n. Native SetMM equality is bidirectionally equivalent to
  connectives.equal here: equal_leibniz yields native equality, while native
  equality rewrites the right side to the left and refl_equal supplies source
  reflexivity. All declarations are unproved $a statement encodings; this
  database contains no $p proof declaration.
$)

$c LogPlus LogPlusBody LogNatUnaryFunction LogNatBinaryFunction $.

log-plus-syntax $a class ( LogPlus ) $.
log-plus-body-syntax $a class ( LogPlusBody ) $.
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

  logipedia-nat-axiom-plus-body-s $a |-
    (
      (
        ( LogPlus ) e. ( LogNatBinaryFunction )
        /\
        ( LogPlusBody ) e. ( LogNatBinaryFunction )
      )
      /\
      A. n e. NN0
        (
          (
            m e. NN0 |->
              ( ( ( LogPlus ` n ) ` m ) + 1 )
          ) e. ( LogNatUnaryFunction )
          /\
          ( LogPlusBody ` ( n + 1 ) ) =
            (
              m e. NN0 |->
                ( ( ( LogPlus ` n ) ` m ) + 1 )
            )
        )
    )
  $.
$}
