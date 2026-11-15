$(
  Statement-only formalization of the Logipedia corpus artifact
  nat.sym_eq_times_body_S
  (logipedia__metamath__nat.sym_eq_times_body_S), catalog title
  "nat.sym_eq_times_body_S": for every natural number n, the function mapping
  each natural number m to plus m (times n m) is Leibniz equal, as a function
  on natural numbers, to the multiplication body at successor n. This file
  contains no proof.
$)

$[ lib/set.mm $]

$(
  LogPlus, LogTimes, and LogTimesBody represent the fixed source constants
  of type

    NN0 -> NN0 -> NN0.

  LogNatUnaryFunction and LogNatBinaryFunction explicitly encode the source's
  curried natural-number function spaces. The maps-to term preserves the
  source lambda over every natural m, and n + 1 is the natural-number
  successor S n. A predicate on the unary-function carrier is represented
  extensionally by a subset p of that carrier. Universal transport of
  membership from the lambda function to times_body (S n) is exactly the
  source definition of leibniz.leibniz at the function type. Every assertion
  introduced by this artifact is an unproved $a statement encoding; this
  artifact introduces no $p proof declaration.
$)

$c
  LogPlus LogTimes LogTimesBody
  LogNatUnaryFunction LogNatBinaryFunction
$.

log-plus-syntax $a class ( LogPlus ) $.
log-times-syntax $a class ( LogTimes ) $.
log-times-body-syntax $a class ( LogTimesBody ) $.
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

  logipedia-nat-sym-eq-times-body-s $a |-
    (
      (
        (
          ( LogPlus ) e. ( LogNatBinaryFunction )
          /\
          ( LogTimes ) e. ( LogNatBinaryFunction )
        )
        /\
        ( LogTimesBody ) e. ( LogNatBinaryFunction )
      )
      /\
      A. n e. NN0
        (
          (
            m e. NN0 |->
              (
                ( LogPlus ` m )
                `
                ( ( LogTimes ` n ) ` m )
              )
          ) e. ( LogNatUnaryFunction )
          /\
          A. p e. ~P ( LogNatUnaryFunction )
            (
              (
                (
                  m e. NN0 |->
                    (
                      ( LogPlus ` m )
                      `
                      ( ( LogTimes ` n ) ` m )
                    )
                )
                e.
                p
              )
              ->
              ( ( LogTimesBody ` ( n + 1 ) ) e. p )
            )
        )
    )
  $.
$}
