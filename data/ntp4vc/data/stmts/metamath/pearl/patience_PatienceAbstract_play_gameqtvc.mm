$(
  Statement-only formalization of the NTP4VC corpus artifact
  pearl/patience_PatienceAbstract_play_gameqtvc: the abstract patience
  solitaire play-game verification condition initializes the complete state
  invariant and uses predecessor links to show that the final stack count is
  the length of a longest strictly increasing input subsequence. This file
  contains no proof.
$)

$[ lib/set.mm $]

$(
  NTP4VCState is exactly the source seven-field state record over unbounded
  integers and total integer maps. NTP4VCSeq is exactly the source pair of an
  integer length and a total integer-indexed map. SetMM Word ZZ is the full
  type of arbitrary finite zero-based integer lists.

  NTP4VCInv and NTP4VCIncreasing expand the source predicates. Function
  update is exact, record and sequence projections are nested-product
  projections, and source proposition-valued conditionals are represented
  by exhaustive guarded disjunctions. NTP4VCLoopBody is precisely the seven
  descending-loop invariants, while NTP4VCDescent preserves the original
  initialization, preservation, exit, and maximality scopes.

  Expanding the definitions below recovers the original Why3 verification
  condition and the agreeing Lean, Rocq, and Isabelle exports. Every
  auxiliary $a is syntax or a faithful definition needed to state that
  condition. The final $a is Metamath's native unproved statement encoding;
  this database contains no $p proof declaration.
$)

$c
  NTP4VCState NTP4VCNumStacks NTP4VCNumElts NTP4VCValues
  NTP4VCStackSizes NTP4VCStacks NTP4VCPositions NTP4VCPreds
  NTP4VCSeq NTP4VCSeqLen NTP4VCSeqVal
  NTP4VCMinusOneMap NTP4VCZeroMap NTP4VCUpdate
  NTP4VCInitial NTP4VCTop
  NTP4VCInv NTP4VCIncreasing NTP4VCMaximal
  NTP4VCLoopBody NTP4VCStepBody NTP4VCDescent
  NTP4VCFinalState NTP4VCPlayGameVC
$.

ntp4vc-state-syntax $a class NTP4VCState $.
ntp4vc-num-stacks-syntax $a class ( NTP4VCNumStacks A ) $.
ntp4vc-num-elts-syntax $a class ( NTP4VCNumElts A ) $.
ntp4vc-values-syntax $a class ( NTP4VCValues A ) $.
ntp4vc-stack-sizes-syntax $a class ( NTP4VCStackSizes A ) $.
ntp4vc-stacks-syntax $a class ( NTP4VCStacks A ) $.
ntp4vc-positions-syntax $a class ( NTP4VCPositions A ) $.
ntp4vc-preds-syntax $a class ( NTP4VCPreds A ) $.
ntp4vc-seq-syntax $a class NTP4VCSeq $.
ntp4vc-seq-len-syntax $a class ( NTP4VCSeqLen A ) $.
ntp4vc-seq-val-syntax $a class ( NTP4VCSeqVal A ) $.
ntp4vc-minus-one-map-syntax $a class NTP4VCMinusOneMap $.
ntp4vc-zero-map-syntax $a class NTP4VCZeroMap $.
ntp4vc-update-syntax $a class ( NTP4VCUpdate A B C ) $.
ntp4vc-initial-syntax $a class NTP4VCInitial $.
ntp4vc-top-syntax $a class ( NTP4VCTop A ) $.
ntp4vc-inv-syntax $a wff ( NTP4VCInv A ) $.
ntp4vc-increasing-syntax $a wff ( NTP4VCIncreasing A B ) $.
ntp4vc-maximal-syntax $a wff ( NTP4VCMaximal A B ) $.
ntp4vc-loop-body-syntax $a wff ( NTP4VCLoopBody A B C D ) $.
ntp4vc-step-body-syntax $a wff ( NTP4VCStepBody A B C D ) $.
ntp4vc-descent-syntax $a wff ( NTP4VCDescent A B ) $.
ntp4vc-final-state-syntax $a wff ( NTP4VCFinalState A B ) $.
ntp4vc-play-game-vc-syntax $a wff ( NTP4VCPlayGameVC A ) $.

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

ntp4vc-seq-definition $a |- NTP4VCSeq =
  ( ZZ X. ( ZZ ^m ZZ ) ) $.

ntp4vc-seq-len-definition $a |- (
  NTP4VCSeqLen A
) = ( 1st ` A ) $.

ntp4vc-seq-val-definition $a |- (
  NTP4VCSeqVal A
) = ( 2nd ` A ) $.

${
  ntp4vc-minus-one-map-definition $a |- NTP4VCMinusOneMap =
    ( x e. ZZ |-> ( -u 1 ) ) $.

  ntp4vc-zero-map-definition $a |- NTP4VCZeroMap =
    ( x e. ZZ |-> 0 ) $.
$}

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
  $d x y $.

  ntp4vc-initial-definition $a |- NTP4VCInitial =
    <.
      0 ,
      <.
        0 ,
        <.
          NTP4VCMinusOneMap ,
          <.
            NTP4VCZeroMap ,
            <.
              ( x e. ZZ |-> ( y e. ZZ |-> ( -u 1 ) ) ) ,
              <.
                ( x e. ZZ |-> <. ( -u 1 ) , ( -u 1 ) >. ) ,
                NTP4VCMinusOneMap
              >.
            >.
          >.
        >.
      >.
    >. $.
$}

ntp4vc-top-definition $a |- (
  NTP4VCTop A
) = (
  (
    ( NTP4VCStacks A )
    `
    ( ( NTP4VCNumStacks A ) - 1 )
  )
  `
  (
    (
      ( NTP4VCStackSizes A )
      `
      ( ( NTP4VCNumStacks A ) - 1 )
    )
    -
    1
  )
) $.

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
  $d i j A B $.

  ntp4vc-increasing-definition $a |- (
    NTP4VCIncreasing A B
  ) <-> (
    (
      0 <_ ( NTP4VCSeqLen A )
      /\
      ( NTP4VCSeqLen A ) <_ ( # ` B )
    )
    /\
    (
      (
        A. i e. ZZ
          (
            (
              0 <_ i
              /\
              i < ( NTP4VCSeqLen A )
            )
            ->
            (
              0 <_ ( ( NTP4VCSeqVal A ) ` i )
              /\
              ( ( NTP4VCSeqVal A ) ` i ) < ( # ` B )
            )
          )
        /\
        A. i e. ZZ A. j e. ZZ
          (
            (
              0 <_ i
              /\
              (
                i < j
                /\
                j < ( NTP4VCSeqLen A )
              )
            )
            ->
            (
              ( ( NTP4VCSeqVal A ) ` i )
              <
              ( ( NTP4VCSeqVal A ) ` j )
            )
          )
      )
      /\
      A. i e. ZZ A. j e. ZZ
        (
          (
            0 <_ i
            /\
            (
              i < j
              /\
              j < ( NTP4VCSeqLen A )
            )
          )
          ->
          (
            B ` ( ( NTP4VCSeqVal A ) ` i )
          )
          <
          (
            B ` ( ( NTP4VCSeqVal A ) ` j )
          )
        )
    )
  ) $.
$}

${
  $d q A B $.

  ntp4vc-maximal-definition $a |- (
    NTP4VCMaximal A B
  ) <-> (
    (
      E. q e. NTP4VCSeq
        (
          ( NTP4VCSeqLen q ) = ( NTP4VCNumStacks A )
          /\
          ( NTP4VCIncreasing q B )
        )
    )
    /\
    A. q e. NTP4VCSeq
      (
        ( NTP4VCIncreasing q B )
        ->
        ( NTP4VCSeqLen q ) <_ ( NTP4VCNumStacks A )
      )
  ) $.
$}

${
  $d j k A B C D $.

  ntp4vc-loop-body-definition $a |- (
    NTP4VCLoopBody A B C D
  ) <-> (
    (
      ( -u 1 ) <_ C
      /\
      C < ( NTP4VCNumElts A )
    )
    /\
    (
      (
        0 <_ D
        ->
        (
          0 <_ C
          /\
          (
            1st ` ( ( NTP4VCPositions A ) ` C )
          ) = D
        )
      )
      /\
      (
        (
          ( D + 1 ) < ( NTP4VCNumStacks A )
          ->
          C < ( B ` ( D + 1 ) )
        )
        /\
        (
          (
            0 <_ D
            /\
            D < ( ( NTP4VCNumStacks A ) - 1 )
          )
          ->
          (
            ( NTP4VCValues A ) ` C
          )
          <
          (
            ( NTP4VCValues A )
            `
            ( B ` ( D + 1 ) )
          )
        )
      )
    )
    /\
    (
      A. j e. ZZ
        (
          (
            D < j
            /\
            j < ( NTP4VCNumStacks A )
          )
          ->
          (
            0 <_ ( B ` j )
            /\
            ( B ` j ) < ( NTP4VCNumElts A )
          )
        )
      /\
      (
        A. j e. ZZ A. k e. ZZ
          (
            (
              D < j
              /\
              (
                j < k
                /\
                k < ( NTP4VCNumStacks A )
              )
            )
            ->
            ( B ` j ) < ( B ` k )
          )
        /\
        A. j e. ZZ A. k e. ZZ
          (
            (
              D < j
              /\
              (
                j < k
                /\
                k < ( NTP4VCNumStacks A )
              )
            )
            ->
            (
              ( NTP4VCValues A ) ` ( B ` j )
            )
            <
            (
              ( NTP4VCValues A ) ` ( B ` k )
            )
          )
      )
    )
  ) $.
$}

ntp4vc-step-body-definition $a |- (
  NTP4VCStepBody A B C D
) <-> (
  NTP4VCLoopBody
    A
    ( NTP4VCUpdate B D C )
    ( ( NTP4VCPreds A ) ` C )
    ( D - 1 )
) $.

${
  $d f i n A B $.

  ntp4vc-descent-definition $a |- (
    NTP4VCDescent A B
  ) <-> (
    (
      ( -u 1 ) <_ ( ( NTP4VCNumStacks A ) - 1 )
      ->
      (
        (
          NTP4VCLoopBody
            A
            NTP4VCMinusOneMap
            ( NTP4VCTop A )
            ( ( NTP4VCNumStacks A ) - 1 )
        )
        /\
        A. f e. ( ZZ ^m ZZ ) A. n e. ZZ
          (
            (
              A. i e. ZZ
                (
                  (
                    (
                      i <_ ( ( NTP4VCNumStacks A ) - 1 )
                      /\
                      0 <_ i
                    )
                    /\
                    ( NTP4VCLoopBody A f n i )
                  )
                  ->
                  ( NTP4VCStepBody A f n i )
                )
            )
            /\
            (
              ( NTP4VCLoopBody A f n ( -u 1 ) )
              ->
              ( NTP4VCMaximal A B )
            )
          )
      )
    )
    /\
    (
      ( ( NTP4VCNumStacks A ) - 1 ) < ( -u 1 )
      ->
      ( NTP4VCMaximal A B )
    )
  ) $.
$}

ntp4vc-final-state-definition $a |- (
  NTP4VCFinalState A B
) <-> (
  (
    ( NTP4VCNumStacks A ) = 0
    /\
    ( NTP4VCMaximal A B )
  )
  \/
  (
    -. ( NTP4VCNumStacks A ) = 0
    /\
    ( NTP4VCDescent A B )
  )
) $.

${
  $d i s A $.

  ntp4vc-play-game-vc-definition $a |- (
    NTP4VCPlayGameVC A
  ) <-> (
    ( NTP4VCInv NTP4VCInitial )
    /\
    A. s e. NTP4VCState
      (
        (
          ( NTP4VCInv s )
          /\
          (
            ( NTP4VCNumElts s ) = ( 0 + ( # ` A ) )
            /\
            (
              A. i e. ZZ
                (
                  (
                    0 <_ i
                    /\
                    i < 0
                  )
                  ->
                  (
                    ( NTP4VCValues s ) ` i
                  ) = ( NTP4VCMinusOneMap ` i )
                )
              /\
              A. i e. ZZ
                (
                  (
                    0 <_ i
                    /\
                    i < ( NTP4VCNumElts s )
                  )
                  ->
                  (
                    ( NTP4VCValues s ) ` i
                  ) = ( A ` ( i - 0 ) )
                )
            )
          )
        )
        ->
        ( NTP4VCFinalState s A )
      )
  ) $.
$}

${
  $d f i j k n q s x y A $.

  ntp4vc-input-word $e |- A e. Word ZZ $.

  ntp4vc-pearl-patience-patience-abstract-play-game-vc
    $a |- ( NTP4VCPlayGameVC A ) $.
$}
