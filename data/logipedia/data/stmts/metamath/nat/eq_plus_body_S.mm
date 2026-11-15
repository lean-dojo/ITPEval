$(
  Statement-only formalization of the Logipedia corpus artifact
  nat.eq_plus_body_S (logipedia__metamath__nat.eq_plus_body_S), catalog title
  "nat.eq_plus_body_S": for every natural number n, the addition body at
  successor n is Leibniz equal, as a function on natural numbers, to the
  function mapping each natural m to the successor of plus n m. This file
  contains no proof.
$)

$[ lib/set.mm $]

$(
  LogPlus and LogPlusBody represent the fixed source constants of type

    NN0 -> NN0 -> NN0.

  LogNatUnaryFunction and LogNatBinaryFunction explicitly encode the source's
  curried natural-number function spaces. The maps-to term preserves the
  source lambda over every natural m, and n + 1 is the natural-number
  successor S n. A predicate on the unary-function carrier is represented
  extensionally by a subset p of that carrier. Universal transport of
  membership from plus_body (S n) to the lambda function is exactly the source
  definition of leibniz.leibniz at the function type. Every assertion
  introduced by this artifact is an unproved $a statement encoding; this
  artifact introduces no $p proof declaration.
$)

$c LogPlus LogPlusBody LogNatUnaryFunction LogNatBinaryFunction $.

log-plus-syntax $a class ( LogPlus ) $.
log-plus-body-syntax $a class ( LogPlusBody ) $.
log-nat-unary-function-syntax $a
  class ( LogNatUnaryFunction )
$.
log-nat-binary-function-syntax $a
  class ( LogNatBinaryFunction )
$.

log-nat-unary-function-definition $a |-
  ( LogNatUnaryFunction ) = ( NN0 ^m NN0 )
$.

log-nat-binary-function-definition $a |-
  ( LogNatBinaryFunction ) =
    ( ( LogNatUnaryFunction ) ^m NN0 )
$.

${
  $d m n p $.

  logipedia-nat-eq-plus-body-s $a |-
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
          A. p e. ~P ( LogNatUnaryFunction )
            (
              ( ( LogPlusBody ` ( n + 1 ) ) e. p )
              ->
              (
                (
                  m e. NN0 |->
                    ( ( ( LogPlus ` n ) ` m ) + 1 )
                )
                e.
                p
              )
            )
        )
    )
  $.
$}
