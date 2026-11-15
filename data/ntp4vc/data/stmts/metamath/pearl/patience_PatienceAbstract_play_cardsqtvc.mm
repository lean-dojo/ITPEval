$(
  Statement-only formalization of the NTP4VC corpus artifact
  pearl/patience_PatienceAbstract_play_cardsqtvc: the abstract patience
  solitaire play-cards verification condition preserves the complete stack,
  position, ordering, value, and predecessor invariant while appending an
  arbitrary finite list of integer-valued cards. This file contains no proof.
$)

$[ lib/set.mm $]

$(
  NTP4VCState is exactly the source seven-field state record: two integers,
  two integer-valued maps, one curried integer map, one integer-pair-valued
  map, and one further integer-valued map. The named projections are the
  corresponding nested-product projections, so quantification over states
  retains every possible source record rather than using an uninterpreted
  carrier. SetMM Word ZZ is exactly the full type of arbitrary finite
  zero-based integer lists.

  NTP4VCUpdate is total function update and NTP4VCTail is the exact tail of
  a nonempty word. NTP4VCInv expands every conjunct of the Why3 invariant
  over the full unbounded integer domain. The source list match is rendered
  by exhaustive zero-length and positive-length guarded branches. Its head
  and tail are substituted definitionally, while the intermediate states
  remain universally quantified at their original scopes.

  The original Why3 verification condition and the Lean, Rocq, and Isabelle
  exports agree on this proposition. Every auxiliary $a below is syntax or
  a faithful definition required to state it. The final $a declaration is
  Metamath's native unproved statement encoding; this database contains no
  $p proof declaration.
$)

$c
  NTP4VCState NTP4VCNumStacks NTP4VCNumElts NTP4VCValues
  NTP4VCStackSizes NTP4VCStacks NTP4VCPositions NTP4VCPreds
  NTP4VCUpdate NTP4VCTail NTP4VCInv NTP4VCEmptyCase
  NTP4VCStepCase NTP4VCPlayCardsVC
$.

ntp4vc-state-syntax $a class NTP4VCState $.
ntp4vc-num-stacks-syntax $a class ( NTP4VCNumStacks A ) $.
ntp4vc-num-elts-syntax $a class ( NTP4VCNumElts A ) $.
ntp4vc-values-syntax $a class ( NTP4VCValues A ) $.
ntp4vc-stack-sizes-syntax $a class ( NTP4VCStackSizes A ) $.
ntp4vc-stacks-syntax $a class ( NTP4VCStacks A ) $.
ntp4vc-positions-syntax $a class ( NTP4VCPositions A ) $.
ntp4vc-preds-syntax $a class ( NTP4VCPreds A ) $.
ntp4vc-update-syntax $a class ( NTP4VCUpdate A B C ) $.
ntp4vc-tail-syntax $a class ( NTP4VCTail A ) $.
ntp4vc-inv-syntax $a wff ( NTP4VCInv A ) $.
ntp4vc-empty-case-syntax $a wff ( NTP4VCEmptyCase A B ) $.
ntp4vc-step-case-syntax $a wff ( NTP4VCStepCase A B ) $.
ntp4vc-play-cards-vc-syntax $a wff ( NTP4VCPlayCardsVC A B ) $.

ntp4vc-state-definition $a |- NTP4VCState =
  (
    ZZ
    X.
    (
      ZZ
      X.
      (
        ( ZZ ^m ZZ )
        X.
        (
          ( ZZ ^m ZZ )
          X.
          (
            ( ( ZZ ^m ZZ ) ^m ZZ )
            X.
            (
              ( ( ZZ X. ZZ ) ^m ZZ )
              X.
              ( ZZ ^m ZZ )
            )
          )
        )
      )
    )
  ) $.

ntp4vc-num-stacks-definition $a |- (
  NTP4VCNumStacks A
) = ( 1st ` A ) $.

ntp4vc-num-elts-definition $a |- (
  NTP4VCNumElts A
) = ( 1st ` ( 2nd ` A ) ) $.

ntp4vc-values-definition $a |- (
  NTP4VCValues A
) = ( 1st ` ( 2nd ` ( 2nd ` A ) ) ) $.

ntp4vc-stack-sizes-definition $a |- (
  NTP4VCStackSizes A
) = ( 1st ` ( 2nd ` ( 2nd ` ( 2nd ` A ) ) ) ) $.

ntp4vc-stacks-definition $a |- (
  NTP4VCStacks A
) = (
  1st `
  ( 2nd ` ( 2nd ` ( 2nd ` ( 2nd ` A ) ) ) )
) $.

ntp4vc-positions-definition $a |- (
  NTP4VCPositions A
) = (
  1st `
  ( 2nd ` ( 2nd ` ( 2nd ` ( 2nd ` ( 2nd ` A ) ) ) ) )
) $.

ntp4vc-preds-definition $a |- (
  NTP4VCPreds A
) = (
  2nd `
  ( 2nd ` ( 2nd ` ( 2nd ` ( 2nd ` ( 2nd ` A ) ) ) ) )
) $.

${
  $d x A B C $.

  ntp4vc-update-definition $a |- (
    NTP4VCUpdate A B C
  ) = (
    x e. ZZ |->
      if ( x = B , C , ( A ` x ) )
  ) $.
$}

${
  $d i A $.

  ntp4vc-tail-definition $a |- (
    NTP4VCTail A
  ) = (
    i e. ( 0 ..^ ( ( # ` A ) - 1 ) ) |->
      ( A ` ( i + 1 ) )
  ) $.
$}

${
  $d i j k A $.

  ntp4vc-inv-definition $a |- (
    NTP4VCInv A
  ) <-> (
    (
      0 <_ ( NTP4VCNumStacks A )
      /\
      ( NTP4VCNumStacks A ) <_ ( NTP4VCNumElts A )
    )
    /\
    (
      (
        0 < ( NTP4VCNumElts A )
        ->
        0 < ( NTP4VCNumStacks A )
      )
      /\
      (
        A. i e. ZZ
          (
            (
              0 <_ i
              /\
              i < ( NTP4VCNumStacks A )
            )
            ->
            (
              1 <_ ( ( NTP4VCStackSizes A ) ` i )
              /\
              A. j e. ZZ
                (
                  (
                    0 <_ j
                    /\
                    j < ( ( NTP4VCStackSizes A ) ` i )
                  )
                  ->
                  (
                    0 <_ ( ( ( NTP4VCStacks A ) ` i ) ` j )
                    /\
                    (
                      ( ( ( NTP4VCStacks A ) ` i ) ` j )
                      <
                      ( NTP4VCNumElts A )
                    )
                  )
                )
            )
          )
        /\
        (
          A. i e. ZZ
            (
              (
                0 <_ i
                /\
                i < ( NTP4VCNumElts A )
              )
              ->
              (
                (
                  0 <_
                  ( 1st ` ( ( NTP4VCPositions A ) ` i ) )
                  /\
                  (
                    ( 1st ` ( ( NTP4VCPositions A ) ` i ) )
                    <
                    ( NTP4VCNumStacks A )
                  )
                )
                /\
                (
                  (
                    0 <_
                    ( 2nd ` ( ( NTP4VCPositions A ) ` i ) )
                    /\
                    (
                      ( 2nd ` ( ( NTP4VCPositions A ) ` i ) )
                      <
                      (
                        ( NTP4VCStackSizes A )
                        `
                        ( 1st ` ( ( NTP4VCPositions A ) ` i ) )
                      )
                    )
                  )
                  /\
                  (
                    (
                      ( NTP4VCStacks A )
                      `
                      ( 1st ` ( ( NTP4VCPositions A ) ` i ) )
                    )
                    `
                    ( 2nd ` ( ( NTP4VCPositions A ) ` i ) )
                  )
                  =
                  i
                )
              )
            )
          /\
          (
            A. i e. ZZ
              (
                (
                  0 <_ i
                  /\
                  i < ( NTP4VCNumStacks A )
                )
                ->
                A. j e. ZZ
                  (
                    (
                      0 <_ j
                      /\
                      j < ( ( NTP4VCStackSizes A ) ` i )
                    )
                    ->
                    <. i , j >.
                    =
                    (
                      ( NTP4VCPositions A )
                      `
                      ( ( ( NTP4VCStacks A ) ` i ) ` j )
                    )
                  )
              )
            /\
            (
              A. i e. ZZ
                (
                  (
                    0 <_ i
                    /\
                    i < ( NTP4VCNumStacks A )
                  )
                  ->
                  A. j e. ZZ A. k e. ZZ
                    (
                      (
                        0 <_ j
                        /\
                        (
                          j < k
                          /\
                          k < ( ( NTP4VCStackSizes A ) ` i )
                        )
                      )
                      ->
                      (
                        ( ( ( NTP4VCStacks A ) ` i ) ` j )
                        <
                        ( ( ( NTP4VCStacks A ) ` i ) ` k )
                      )
                    )
                )
              /\
              (
                A. i e. ZZ
                  (
                    (
                      0 <_ i
                      /\
                      i < ( NTP4VCNumStacks A )
                    )
                    ->
                    A. j e. ZZ A. k e. ZZ
                      (
                        (
                          0 <_ j
                          /\
                          (
                            j <_ k
                            /\
                            k < ( ( NTP4VCStackSizes A ) ` i )
                          )
                        )
                        ->
                        (
                          ( NTP4VCValues A )
                          `
                          ( ( ( NTP4VCStacks A ) ` i ) ` k )
                        )
                        <_
                        (
                          ( NTP4VCValues A )
                          `
                          ( ( ( NTP4VCStacks A ) ` i ) ` j )
                        )
                      )
                  )
                /\
                A. i e. ZZ
                  (
                    (
                      0 <_ i
                      /\
                      i < ( NTP4VCNumElts A )
                    )
                    ->
                    (
                      (
                        ( -u 1 ) <_ ( ( NTP4VCPreds A ) ` i )
                        /\
                        (
                          ( ( NTP4VCPreds A ) ` i )
                          <
                          ( NTP4VCNumElts A )
                        )
                      )
                      /\
                      (
                        ( ( NTP4VCPreds A ) ` i ) < i
                        /\
                        (
                          (
                            ( ( NTP4VCPreds A ) ` i ) < 0
                            /\
                            (
                              1st `
                              ( ( NTP4VCPositions A ) ` i )
                            ) = 0
                          )
                          \/
                          (
                            -.
                            ( ( NTP4VCPreds A ) ` i ) < 0
                            /\
                            (
                              (
                                ( NTP4VCValues A )
                                `
                                ( ( NTP4VCPreds A ) ` i )
                              )
                              <
                              ( ( NTP4VCValues A ) ` i )
                              /\
                              (
                                0 <
                                (
                                  1st `
                                  ( ( NTP4VCPositions A ) ` i )
                                )
                                /\
                                (
                                  1st `
                                  (
                                    ( NTP4VCPositions A )
                                    `
                                    ( ( NTP4VCPreds A ) ` i )
                                  )
                                )
                                =
                                (
                                  (
                                    1st `
                                    ( ( NTP4VCPositions A ) ` i )
                                  )
                                  -
                                  1
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
          )
        )
      )
    )
  ) $.
$}

${
  $d i A B $.

  ntp4vc-empty-case-definition $a |- (
    NTP4VCEmptyCase A B
  ) <-> (
    ( NTP4VCInv A )
    /\
    (
      ( NTP4VCNumElts A )
      =
      ( ( NTP4VCNumElts A ) + ( # ` B ) )
      /\
      A. i e. ZZ
        (
          (
            ( NTP4VCNumElts A ) <_ i
            /\
            i < ( NTP4VCNumElts A )
          )
          ->
          (
            ( ( NTP4VCValues A ) ` i )
            =
            ( B ` ( i - ( NTP4VCNumElts A ) ) )
          )
        )
    )
  ) $.
$}

${
  $d i x y A B $.

  ntp4vc-step-case-definition $a |- (
    NTP4VCStepCase A B
  ) <-> (
    ( NTP4VCInv A )
    /\
    A. x e. NTP4VCState
      (
        (
          ( NTP4VCInv x )
          /\
          (
            ( NTP4VCNumElts x )
            =
            ( ( NTP4VCNumElts A ) + 1 )
            /\
            (
              NTP4VCValues x
            ) = (
              NTP4VCUpdate
                ( NTP4VCValues A )
                ( NTP4VCNumElts A )
                ( B ` 0 )
            )
          )
        )
        ->
        (
          (
            ( NTP4VCTail B ) = ( NTP4VCTail B )
            /\
            ( NTP4VCInv x )
          )
          /\
          A. y e. NTP4VCState
            (
              (
                ( NTP4VCInv y )
                /\
                (
                  ( NTP4VCNumElts y )
                  =
                  (
                    ( NTP4VCNumElts x )
                    +
                    ( # ` ( NTP4VCTail B ) )
                  )
                  /\
                  (
                    A. i e. ZZ
                      (
                        (
                          0 <_ i
                          /\
                          i < ( NTP4VCNumElts x )
                        )
                        ->
                        (
                          ( ( NTP4VCValues y ) ` i )
                          =
                          ( ( NTP4VCValues x ) ` i )
                        )
                      )
                    /\
                    A. i e. ZZ
                      (
                        (
                          ( NTP4VCNumElts x ) <_ i
                          /\
                          i < ( NTP4VCNumElts y )
                        )
                        ->
                        (
                          ( ( NTP4VCValues y ) ` i )
                          =
                          (
                            ( NTP4VCTail B )
                            `
                            ( i - ( NTP4VCNumElts x ) )
                          )
                        )
                      )
                  )
                )
              )
              ->
              (
                ( NTP4VCInv y )
                /\
                (
                  ( NTP4VCNumElts y )
                  =
                  (
                    ( NTP4VCNumElts A )
                    +
                    ( # ` B )
                  )
                  /\
                  (
                    A. i e. ZZ
                      (
                        (
                          0 <_ i
                          /\
                          i < ( NTP4VCNumElts A )
                        )
                        ->
                        (
                          ( ( NTP4VCValues y ) ` i )
                          =
                          ( ( NTP4VCValues A ) ` i )
                        )
                      )
                    /\
                    A. i e. ZZ
                      (
                        (
                          ( NTP4VCNumElts A ) <_ i
                          /\
                          i < ( NTP4VCNumElts y )
                        )
                        ->
                        (
                          ( ( NTP4VCValues y ) ` i )
                          =
                          (
                            B
                            `
                            ( i - ( NTP4VCNumElts A ) )
                          )
                        )
                      )
                  )
                )
              )
            )
        )
      )
  ) $.
$}

ntp4vc-play-cards-vc-definition $a |- (
  NTP4VCPlayCardsVC A B
) <-> (
  (
    ( # ` B ) = 0
    /\
    ( NTP4VCEmptyCase A B )
  )
  \/
  (
    0 < ( # ` B )
    /\
    ( NTP4VCStepCase A B )
  )
) $.

${
  $d i j k x y A B $.

  $( Source theorem parameters A=s and B=input, followed by fact0. $)
  ntp4vc-s-state $e |- A e. NTP4VCState $.
  ntp4vc-input-word $e |- B e. Word ZZ $.
  ntp4vc-fact0 $e |- ( NTP4VCInv A ) $.

  ntp4vc-pearl-patience-patience-abstract-play-cards-vc
    $a |- ( NTP4VCPlayCardsVC A B ) $.
$}
