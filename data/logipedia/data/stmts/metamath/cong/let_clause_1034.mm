$(
  Statement-only formalization of the Logipedia corpus artifact
  cong.let_clause_1034, catalog title "cong.let_clause_1034": under an
  unrelated positive-natural assumption, every pair of natural numbers
  satisfies the total natural quotient-remainder identity. This file
  contains no proof.
$)

$[ lib/set.mm $]

$(
  NN0 is the source natural-number domain. LogCongDiv and LogCongMod are the
  source's total natural division and remainder: at divisor zero they return
  x + 1 and x respectively, and at a positive divisor they are the usual
  quotient and remainder. The declaration preserves the source's unused
  natural parameters n and m and its assumption 0 < p. All declarations are
  unproved $a statement encodings; this database contains no $p proof
  declaration.
$)

$c LogCongDiv LogCongMod $.

log-cong-div-syntax $a class ( LogCongDiv x y ) $.
log-cong-mod-syntax $a class ( LogCongMod x y ) $.

log-cong-div-definition $a |- (
  ( LogCongDiv x y )
  =
  if (
    y = 0 ,
    ( x + 1 ) ,
    ( |_ ` ( x / y ) )
  )
) $.

log-cong-mod-definition $a |- (
  ( LogCongMod x y )
  =
  if (
    y = 0 ,
    x ,
    ( x mod y )
  )
) $.

${
  $d n m p x y $.

  logipedia-cong-let-clause-1034 $a |-
    A. n e. NN0
      A. m e. NN0
        A. p e. NN0
          (
            0 < p
            ->
            A. x e. NN0
              A. y e. NN0
                x
                =
                (
                  ( LogCongMod x y )
                  +
                  (
                    y
                    x.
                    ( LogCongDiv x y )
                  )
                )
          )
  $.
$}
