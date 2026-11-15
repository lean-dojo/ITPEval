$(
  Statement-only formalization of the Logipedia corpus artifact
  gcd.let_clause_1544
  (logipedia__metamath__gcd.let_clause_1544), catalog title
  "gcd.let_clause_1544": a nested natural-number implication used in the
  gcd_aux induction, concluding that replacing b times n by n times b
  preserves the stated truncated-difference equality. This file contains no
  proof.
$)

$[ lib/set.mm $]

$(
  NN0 is the source natural-number domain. LogGcdAux represents the fixed
  source constant gcd_aux with curried type NN0 -> NN0 -> NN0 -> NN0.
  LogNatMod is the source's total natural remainder, returning its dividend
  at divisor zero. LogNatMinus is truncated natural subtraction. SetMM order,
  multiplication, and divisibility on NN0 represent the corresponding source
  operations. The declaration retains the unused outer parameter p, every
  quantifier and implication hypothesis, both existential witnesses and
  disjunctions, and the final change from b x. n to n x. b. All declarations
  are unproved $a statement encodings; this database contains no $p proof
  declaration.
$)

$c LogGcdAux LogNatMod LogNatMinus $.

log-gcd-aux-syntax $a class ( LogGcdAux ) $.
log-nat-mod-syntax $a class ( LogNatMod x y ) $.
log-nat-minus-syntax $a class ( LogNatMinus A B ) $.

log-nat-mod-definition $a |- (
  ( LogNatMod x y )
  =
  if (
    y = 0 ,
    x ,
    ( x mod y )
  )
) $.

log-nat-minus-definition $a |- (
  ( LogNatMinus A B )
  =
  if (
    B <_ A ,
    ( A - B ) ,
    0
  )
) $.

${
  $d a b m n p q $.

  logipedia-gcd-let-clause-1544 $a |-
    (
      ( LogGcdAux ) e.
        ( ( ( NN0 ^m NN0 ) ^m NN0 ) ^m NN0 )
      /\
      A. p e. NN0 A. q e. NN0
        (
          A. m e. NN0 A. n e. NN0
            (
              0 < n
              ->
              (
                n <_ m
                ->
                (
                  n <_ q
                  ->
                  E. a e. NN0 E. b e. NN0
                    (
                      (
                        LogNatMinus
                        ( a x. n )
                        ( b x. m )
                      )
                      =
                      (
                        (
                          ( ( LogGcdAux ) ` q )
                          `
                          m
                        )
                        `
                        n
                      )
                      \/
                      (
                        LogNatMinus
                        ( b x. m )
                        ( a x. n )
                      )
                      =
                      (
                        (
                          ( ( LogGcdAux ) ` q )
                          `
                          m
                        )
                        `
                        n
                      )
                    )
                )
              )
            )
          ->
          A. m e. NN0 A. n e. NN0
            (
              0 < n
              ->
              (
                n <_ m
                ->
                (
                  n <_ ( q + 1 )
                  ->
                  (
                    -. n || m
                    ->
                    A. a e. NN0
                      (
                        E. b e. NN0
                          (
                            (
                              LogNatMinus
                              ( a x. ( LogNatMod m n ) )
                              ( b x. n )
                            )
                            =
                            (
                              (
                                ( ( LogGcdAux ) ` q )
                                `
                                n
                              )
                              `
                              ( LogNatMod m n )
                            )
                            \/
                            (
                              LogNatMinus
                              ( b x. n )
                              ( a x. ( LogNatMod m n ) )
                            )
                            =
                            (
                              (
                                ( ( LogGcdAux ) ` q )
                                `
                                n
                              )
                              `
                              ( LogNatMod m n )
                            )
                          )
                        ->
                        A. b e. NN0
                          (
                            (
                              (
                                LogNatMinus
                                ( a x. ( LogNatMod m n ) )
                                ( b x. n )
                              )
                              =
                              (
                                (
                                  ( ( LogGcdAux ) ` q )
                                  `
                                  n
                                )
                                `
                                ( LogNatMod m n )
                              )
                              \/
                              (
                                LogNatMinus
                                ( b x. n )
                                ( a x. ( LogNatMod m n ) )
                              )
                              =
                              (
                                (
                                  ( ( LogGcdAux ) ` q )
                                  `
                                  n
                                )
                                `
                                ( LogNatMod m n )
                              )
                            )
                            ->
                            (
                              (
                                LogNatMinus
                                ( a x. ( LogNatMod m n ) )
                                ( b x. n )
                              )
                              =
                              (
                                (
                                  ( ( LogGcdAux ) ` q )
                                  `
                                  n
                                )
                                `
                                ( LogNatMod m n )
                              )
                              ->
                              (
                                LogNatMinus
                                ( a x. ( LogNatMod m n ) )
                                ( n x. b )
                              )
                              =
                              (
                                (
                                  ( ( LogGcdAux ) ` q )
                                  `
                                  n
                                )
                                `
                                ( LogNatMod m n )
                              )
                            )
                          )
                      )
                  )
                )
              )
            )
        )
    )
  $.
$}
