$(
  Statement-only formalization of the Logipedia corpus artifact
  nat.axiom_times_body_S
  (logipedia__metamath__nat.axiom_times_body_S), catalog title
  "nat.axiom_times_body_S": for every natural number n, the multiplication
  body at successor n equals the function mapping each natural number m to
  plus m (times n m). This file contains no proof.
$)

$[ lib/set.mm $]

$(
  LogPlus, LogTimes, and LogTimesBody represent the fixed source constants
  of type

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
  $d m n $.

  logipedia-nat-axiom-times-body-s $a |-
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
          ( LogTimesBody ` ( n + 1 ) ) =
            (
              m e. NN0 |->
                (
                  ( LogPlus ` m )
                  `
                  ( ( LogTimes ` n ) ` m )
                )
            )
        )
    )
  $.
$}
