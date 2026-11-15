$(
  Statement-only formalization of the NTP4VC corpus artifact
  pearl/verifythis_2021_shearsort_ShearSort_shear_sortqtvc: the complete
  ShearSort verification condition for logarithmic phase bounds, alternating
  row and column sorting, zero-one separation, and preservation of matrix
  multiplicities. This file contains no proof.
$)

$[ lib/set.mm $]

$(
  A source matrix is represented exactly by its nonnegative row and column
  counts and an arbitrary total function from integer index pairs to
  integers. Thus lookup retains the full source integer domain, including
  distinct out-of-bounds indices. Intermediate same-shape matrices are
  represented by arbitrary functions in the same full function space.

  NTP4VCTDiv2 is signed division by two truncated toward zero, NTP4VCCMod2 is
  its associated remainder, and NTP4VCPow2 uses the source convention that a
  negative exponent is converted to zero. Occurrence predicates use exact
  finite half-open integer intervals. The pair-valued nzo function remains
  internally quantified; NTP4VCProjectionPhase retains its first and second
  projections and the quantified newz and newo functions.

  The remaining biconditional definitions factor the generated verification
  condition. Expanding them recovers every matrix, integer, function, pair,
  and Boolean quantifier, every loop and selection invariant, all guarded
  branches, and the final sortedness and multiplicity conclusions. Boolean
  values are represented by SetMM's two-element set { 0, 1 }, with 1 true
  and 0 false. The official Why3 source and the Lean and Isabelle ground truths use
  quotient for division and remainder for parity; the Rocq export swaps these
  operations in several positions, so this statement follows the agreeing
  primary and secondary sources. The final $a declaration is Metamath's
  native unproved statement encoding; this database contains no $p proof.
$)

$c
  NTP4VCConst NTP4VCRow NTP4VCNumof NTP4VCMocc
  NTP4VCToNat NTP4VCPow2 NTP4VCTDiv2 NTP4VCCMod2
  NTP4VCPermut NTP4VCRowOrder NTP4VCRowSnake
  NTP4VCCrossSorted NTP4VCRowPermuted NTP4VCColumnPermuted
  NTP4VCColumnSorted NTP4VCBounds NTP4VCOccPreserved
  NTP4VCLogBound NTP4VCSelectContract NTP4VCSelectVC
  NTP4VCPairSpec NTP4VCNZOInvariant NTP4VCNZOVC
  NTP4VCAuxUp NTP4VCAuxDown NTP4VCFinal
  NTP4VCColumnPhase NTP4VCProjectionPhase NTP4VCNZOPhase
  NTP4VCLoopBody NTP4VCLoopInvariant NTP4VCPostLoop
  NTP4VCCompletion NTP4VCInitial NTP4VCMain
$.

shearsort-const-syntax $a class ( NTP4VCConst A ) $.
shearsort-row-syntax $a class ( NTP4VCRow A B ) $.
shearsort-numof-syntax $a class ( NTP4VCNumof A B C D ) $.
shearsort-mocc-syntax $a class ( NTP4VCMocc A B C D ) $.
shearsort-to-nat-syntax $a class ( NTP4VCToNat A ) $.
shearsort-pow2-syntax $a class ( NTP4VCPow2 A ) $.
shearsort-tdiv2-syntax $a class ( NTP4VCTDiv2 A ) $.
shearsort-cmod2-syntax $a class ( NTP4VCCMod2 A ) $.

shearsort-permut-syntax
  $a wff ( NTP4VCPermut A B C D ) $.
shearsort-row-order-syntax
  $a wff ( NTP4VCRowOrder A B C ) $.
shearsort-row-snake-syntax
  $a wff ( NTP4VCRowSnake A B C ) $.
shearsort-cross-sorted-syntax
  $a wff ( NTP4VCCrossSorted A B C ) $.
shearsort-row-permuted-syntax
  $a wff ( NTP4VCRowPermuted A B C D ) $.
shearsort-column-permuted-syntax
  $a wff ( NTP4VCColumnPermuted A B C D ) $.
shearsort-column-sorted-syntax
  $a wff ( NTP4VCColumnSorted A B C ) $.
shearsort-bounds-syntax
  $a wff ( NTP4VCBounds A B C D E F ) $.
shearsort-occ-preserved-syntax
  $a wff ( NTP4VCOccPreserved A B C D ) $.
shearsort-log-bound-syntax
  $a wff ( NTP4VCLogBound A B C ) $.
shearsort-select-contract-syntax
  $a wff ( NTP4VCSelectContract A B C D E ) $.
shearsort-select-vc-syntax
  $a wff ( NTP4VCSelectVC A B ) $.
shearsort-pair-spec-syntax
  $a wff ( NTP4VCPairSpec A B C D E F G ) $.
shearsort-nzo-invariant-syntax
  $a wff ( NTP4VCNZOInvariant A B C D E F G H I ) $.
shearsort-nzo-vc-syntax
  $a wff ( NTP4VCNZOVC A B C D E F G ) $.
shearsort-aux-up-syntax
  $a wff ( NTP4VCAuxUp A B C ) $.
shearsort-aux-down-syntax
  $a wff ( NTP4VCAuxDown A B C ) $.
shearsort-final-syntax
  $a wff ( NTP4VCFinal A B C ) $.
shearsort-column-phase-syntax
  $a wff ( NTP4VCColumnPhase A B C D E F G H I J K ) $.
shearsort-projection-phase-syntax
  $a wff ( NTP4VCProjectionPhase A B C D E F G H I J ) $.
shearsort-nzo-phase-syntax
  $a wff ( NTP4VCNZOPhase A B C D E F G H I ) $.
shearsort-loop-body-syntax
  $a wff ( NTP4VCLoopBody A B C D E F G H I ) $.
shearsort-loop-invariant-syntax
  $a wff ( NTP4VCLoopInvariant A B C D E F G H I ) $.
shearsort-post-loop-syntax
  $a wff ( NTP4VCPostLoop A B C D E F G H ) $.
shearsort-completion-syntax
  $a wff ( NTP4VCCompletion A B C D ) $.
shearsort-initial-syntax
  $a wff ( NTP4VCInitial A B C D ) $.
shearsort-main-syntax
  $a wff ( NTP4VCMain A B C ) $.

${
  $d v A $.

  shearsort-const-definition $a |- (
    NTP4VCConst A
  ) = (
    v e. ZZ |-> A
  ) $.
$}

${
  $d j A B $.

  shearsort-row-definition $a |- (
    NTP4VCRow A B
  ) = (
    j e. ZZ |-> ( A ` <. B , j >. )
  ) $.
$}

${
  $d i A B C D $.

  shearsort-numof-definition $a |- (
    NTP4VCNumof A B C D
  ) = (
    # ` { i e. ( C ..^ D ) | ( A ` i ) = B }
  ) $.
$}

${
  $d i j v A B C D $.

  shearsort-mocc-definition $a |- (
    NTP4VCMocc A B C D
  ) = sum_ i e. ( 0 ..^ C )
    (
      # `
      { j e. ( 0 ..^ D ) | ( A ` <. i , j >. ) = B }
    ) $.
$}

shearsort-to-nat-definition $a |- (
  NTP4VCToNat A
) = if ( A < 0 , 0 , A ) $.

shearsort-pow2-definition $a |- (
  NTP4VCPow2 A
) = ( 2 ^ ( NTP4VCToNat A ) ) $.

shearsort-tdiv2-definition $a |- (
  NTP4VCTDiv2 A
) = if (
  A < 0 ,
  ( |^ ` ( A / 2 ) ) ,
  ( |_ ` ( A / 2 ) )
) $.

shearsort-cmod2-definition $a |- (
  NTP4VCCMod2 A
) = ( A - ( 2 x. ( NTP4VCTDiv2 A ) ) ) $.

${
  $d i v A B C D $.

  shearsort-permut-definition $a |- (
    NTP4VCPermut A B C D
  ) <->
  A. v e. ZZ
    (
      ( NTP4VCNumof A v C D )
      =
      ( NTP4VCNumof B v C D )
    ) $.
$}

${
  $d j k A B C $.

  shearsort-row-order-definition $a |- (
    NTP4VCRowOrder A B C
  ) <->
  A. j e. ZZ
    A. k e. ZZ
      (
        (
          (
            0 <_ j
            /\
            j <_ k
          )
          /\
          k < C
        )
        ->
        (
          (
            B = 1
            ->
            ( A ` j ) <_ ( A ` k )
          )
          /\
          (
            B = 0
            ->
            ( A ` k ) <_ ( A ` j )
          )
        )
      ) $.
$}

${
  $d i j k A B C $.

  shearsort-row-snake-definition $a |- (
    NTP4VCRowSnake A B C
  ) <->
  A. i e. ZZ
    A. j e. ZZ
      A. k e. ZZ
        (
          (
            (
              0 <_ i
              /\
              i < B
            )
            /\
            (
              (
                0 <_ j
                /\
                j <_ k
              )
              /\
              k < C
            )
          )
          ->
          (
            (
              ( NTP4VCCMod2 i ) = 0
              ->
              ( A ` <. i , j >. ) <_ ( A ` <. i , k >. )
            )
            /\
            (
              -. ( NTP4VCCMod2 i ) = 0
              ->
              ( A ` <. i , k >. ) <_ ( A ` <. i , j >. )
            )
          )
        ) $.
$}

${
  $d i j k l A B C $.

  shearsort-cross-sorted-definition $a |- (
    NTP4VCCrossSorted A B C
  ) <->
  A. i e. ZZ
    A. j e. ZZ
      A. k e. ZZ
        A. l e. ZZ
          (
            (
              (
                (
                  0 <_ i
                  /\
                  i < k
                )
                /\
                k < B
              )
              /\
              (
                (
                  0 <_ j
                  /\
                  j < C
                )
                /\
                (
                  0 <_ l
                  /\
                  l < C
                )
              )
            )
            ->
            ( A ` <. i , j >. ) <_ ( A ` <. k , l >. )
          ) $.
$}

${
  $d i A B C D $.

  shearsort-row-permuted-definition $a |- (
    NTP4VCRowPermuted A B C D
  ) <->
  A. i e. ZZ
    (
      (
        0 <_ i
        /\
        i < C
      )
      ->
      (
        NTP4VCPermut
          ( NTP4VCRow A i )
          ( NTP4VCRow B i )
          0 D
      )
    ) $.
$}

${
  $d i j v A B C D $.

  shearsort-column-permuted-definition $a |- (
    NTP4VCColumnPermuted A B C D
  ) <->
  A. j e. ZZ
    (
      (
        0 <_ j
        /\
        j < D
      )
      ->
      A. v e. ZZ
        (
          (
            NTP4VCNumof
              ( i e. ZZ |-> ( A ` <. i , j >. ) )
              v 0 C
          )
          =
          (
            NTP4VCNumof
              ( i e. ZZ |-> ( B ` <. i , j >. ) )
              v 0 C
          )
        )
    ) $.
$}

${
  $d i j k A B C $.

  shearsort-column-sorted-definition $a |- (
    NTP4VCColumnSorted A B C
  ) <->
  A. i e. ZZ
    A. j e. ZZ
      A. k e. ZZ
        (
          (
            (
              (
                0 <_ i
                /\
                i <_ k
              )
              /\
              k < B
            )
            /\
            (
              0 <_ j
              /\
              j < C
            )
          )
          ->
          ( A ` <. i , j >. ) <_ ( A ` <. k , j >. )
        ) $.
$}

${
  $d i j v A B C D E F $.

  shearsort-bounds-definition $a |- (
    NTP4VCBounds A B C D E F
  ) <->
  (
    A. v e. ZZ
      (
        (
          0 <_ ( B ` v )
          /\
          ( B ` v ) <_ ( C ` v )
        )
        /\
        ( C ` v ) <_ E
      )
    /\
    (
      A. v e. ZZ
        ( C ` v ) <_ ( ( B ` v ) + D )
      /\
      (
        A. v e. ZZ
          A. i e. ZZ
            A. j e. ZZ
              (
                (
                  (
                    (
                      0 <_ i
                      /\
                      i < ( B ` v )
                    )
                    /\
                    0 <_ j
                  )
                  /\
                  j < F
                )
                ->
                ( A ` <. i , j >. ) <_ v
              )
        /\
        A. v e. ZZ
          A. i e. ZZ
            A. j e. ZZ
              (
                (
                  (
                    (
                      ( C ` v ) <_ i
                      /\
                      i < E
                    )
                    /\
                    0 <_ j
                  )
                  /\
                  j < F
                )
                ->
                v < ( A ` <. i , j >. )
              )
      )
    )
  ) $.
$}

${
  $d x A B C D $.

  shearsort-occ-preserved-definition $a |- (
    NTP4VCOccPreserved A B C D
  ) <->
  A. x e. ZZ
    (
      ( NTP4VCMocc A x C D )
      =
      ( NTP4VCMocc B x C D )
    ) $.
$}

shearsort-log-bound-definition $a |- (
  NTP4VCLogBound A B C
) <->
(
  0 < A
  /\
  (
    ( ( A - 1 ) x. ( NTP4VCPow2 B ) ) < C
    /\
    C <_ ( A x. ( NTP4VCPow2 B ) )
  )
) $.

${
  $d i A B C D E $.

  shearsort-select-contract-definition $a |- (
    NTP4VCSelectContract A B C D E
  ) <->
  (
    (
      E = 1
      ->
      A. i e. ZZ
        (
          (
            0 <_ i
            /\
            i < D
          )
          ->
          (
            ( A ` i ) <_ C
            \/
            ( B ` i ) <_ C
          )
        )
    )
    /\
    (
      E = 0
      ->
      A. i e. ZZ
        (
          (
            0 <_ i
            /\
            i < D
          )
          ->
          (
            C < ( A ` i )
            \/
            C < ( B ` i )
          )
        )
    )
  ) $.
$}

${
  $d b c d i j o r A B $.

  shearsort-select-vc-definition $a |- (
    NTP4VCSelectVC A B
  ) <->
  A. c e. ( ZZ ^m ZZ )
    A. d e. ( ZZ ^m ZZ )
      A. b e. { 0 , 1 }
        (
          (
            ( NTP4VCRowOrder c b B )
            /\
            ( NTP4VCRowOrder d ( 1 - b ) B )
          )
          ->
          (
            (
              b = 0
              ->
              (
                (
                  0 <_ 1
                  /\
                  0 < 1
                )
                /\
                (
                  ( NTP4VCRowOrder d 1 B )
                  /\
                  (
                    ( NTP4VCRowOrder c 0 B )
                    /\
                    A. r e. { 0 , 1 }
                      (
                        ( NTP4VCSelectContract d c A B r )
                        ->
                        ( NTP4VCSelectContract c d A B r )
                      )
                  )
                )
              )
            )
            /\
            (
              b = 1
              ->
              (
                (
                  0 <_ 0
                  /\
                  0 <_ B
                )
                /\
                (
                  A. j e. ZZ
                    (
                      (
                        0 <_ j
                        /\
                        j < 0
                      )
                      ->
                      (
                        ( c ` j ) <_ A
                        /\
                        A < ( d ` j )
                      )
                    )
                  /\
                  A. i e. ZZ
                    (
                      (
                        (
                          (
                            0 <_ i
                            /\
                            i <_ B
                          )
                          /\
                          A. j e. ZZ
                            (
                              (
                                0 <_ j
                                /\
                                j < i
                              )
                              ->
                              (
                                ( c ` j ) <_ A
                                /\
                                A < ( d ` j )
                              )
                            )
                        )
                        ->
                        A. o e. { 0 , 1 }
                          (
                            o = if (
                              -. i = B ,
                              if (
                                ( c ` i ) <_ A ,
                                if ( A < ( d ` i ) , 1 , 0 ) ,
                                0
                              ) ,
                              0
                            )
                            ->
                            (
                              (
                                o = 1
                                ->
                                (
                                  (
                                    0 <_ ( B - i )
                                    /\
                                    ( B - ( i + 1 ) ) < ( B - i )
                                  )
                                  /\
                                  (
                                    (
                                      0 <_ ( i + 1 )
                                      /\
                                      ( i + 1 ) <_ B
                                    )
                                    /\
                                    A. j e. ZZ
                                      (
                                        (
                                          0 <_ j
                                          /\
                                          j < ( i + 1 )
                                        )
                                        ->
                                        (
                                          ( c ` j ) <_ A
                                          /\
                                          A < ( d ` j )
                                        )
                                      )
                                  )
                                )
                              )
                              /\
                              (
                                o = 0
                                ->
                                A. r e. { 0 , 1 }
                                  (
                                    r = if (
                                      i = B ,
                                      1 ,
                                      if ( ( d ` i ) <_ A , 1 , 0 )
                                    )
                                    ->
                                    (
                                      NTP4VCSelectContract c d A B r
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
  $d i j A B C D E F G $.

  shearsort-pair-spec-definition $a |- (
    NTP4VCPairSpec A B C D E F G
  ) <->
  (
    (
      0 <_ B
      /\
      B <_ C
    )
    /\
    (
      C <_ E
      /\
      C <_ ( B + D )
    )
    /\
    A. i e. ZZ
      (
        (
          0 <_ i
          /\
          i < F
        )
        ->
        (
          B <_
          (
            # `
            { j e. ( 0 ..^ E ) |
              ( A ` <. j , i >. ) <_ G
            }
          )
          /\
          ( E - C ) <_
          (
            # `
            { j e. ( 0 ..^ E ) |
              G < ( A ` <. j , i >. )
            }
          )
        )
      )
  ) $.
$}

${
  $d i j A B C D E F G H I $.

  shearsort-nzo-invariant-definition $a |- (
    NTP4VCNZOInvariant A B C D E F G H I
  ) <->
  (
    (
      B <_ F
      /\
      F <_ C
    )
    /\
    (
      B <_ D
      /\
      E <_ C
    )
    /\
    (
      ( F - B )
      =
      ( 2 x. ( ( D - B ) + ( C - E ) ) )
    )
    /\
    A. j e. ZZ
      (
        (
          0 <_ j
          /\
          j < H
        )
        ->
        (
          D <_
          (
            # `
            { i e. ( 0 ..^ F ) |
              ( A ` <. i , j >. ) <_ I
            }
          )
          /\
          ( G - E ) <_
          (
            (
              # `
              { i e. ( 0 ..^ F ) |
                I < ( A ` <. i , j >. )
              }
            )
            +
            (
              # `
              { i e. ( C ..^ G ) |
                I < ( A ` <. i , j >. )
              }
            )
          )
        )
      )
  ) $.
$}

${
  $d i n o r z A B C D E F G $.

  shearsort-nzo-vc-definition $a |- (
    NTP4VCNZOVC A B C D E F G
  ) <->
  (
    (
      NTP4VCNZOInvariant
        A ( B ` G ) ( C ` G ) ( B ` G ) ( C ` G )
        ( B ` G ) E F G
    )
    /\
    A. i e. ZZ
      A. o e. ZZ
        A. n e. ZZ
          (
            (
              NTP4VCNZOInvariant
                A ( B ` G ) ( C ` G ) n o i E F G
            )
            ->
            (
              (
                ( i + 1 ) < ( C ` G )
                ->
                (
                  ( NTP4VCSelectVC G F )
                  /\
                  2 =/= 0
                  /\
                  (
                    (
                      NTP4VCRowOrder
                        ( NTP4VCRow A i )
                        if ( ( NTP4VCCMod2 i ) = 0 , 1 , 0 )
                        F
                    )
                    /\
                    (
                      NTP4VCRowOrder
                        ( NTP4VCRow A ( i + 1 ) )
                        if ( ( NTP4VCCMod2 i ) = 0 , 0 , 1 )
                        F
                    )
                  )
                  /\
                  A. r e. { 0 , 1 }
                    (
                      (
                        NTP4VCSelectContract
                          ( NTP4VCRow A i )
                          ( NTP4VCRow A ( i + 1 ) )
                          G F r
                      )
                      ->
                      (
                        (
                          r = 1
                          ->
                          (
                            (
                              0 <_ ( ( C ` G ) - i )
                              /\
                              (
                                ( C ` G ) - ( i + 2 )
                              ) < ( ( C ` G ) - i )
                            )
                            /\
                            (
                              NTP4VCNZOInvariant
                                A ( B ` G ) ( C ` G )
                                ( n + 1 ) o ( i + 2 ) E F G
                            )
                          )
                        )
                        /\
                        (
                          r = 0
                          ->
                          (
                            (
                              0 <_ ( ( C ` G ) - i )
                              /\
                              (
                                ( C ` G ) - ( i + 2 )
                              ) < ( ( C ` G ) - i )
                            )
                            /\
                            (
                              NTP4VCNZOInvariant
                                A ( B ` G ) ( C ` G )
                                n ( o - 1 ) ( i + 2 ) E F G
                            )
                          )
                        )
                      )
                    )
                )
              )
              /\
              (
                -. ( i + 1 ) < ( C ` G )
                ->
                ( NTP4VCPairSpec A n o D E F G )
              )
            )
          )
  ) $.
$}

${
  $d i j k v A B C $.

  shearsort-aux-up-definition $a |- (
    NTP4VCAuxUp A B C
  ) <->
  A. v e. ZZ
    A. i e. ZZ
      A. j e. ZZ
        (
          (
            (
              0 <_ i
              /\
              i < B
            )
            /\
            (
              (
                0 <
                (
                  # `
                  { k e. ( ( i + 1 ) ..^ B ) |
                    ( A ` <. k , j >. ) <_ v
                  }
                )
                /\
                (
                  0 <_ j
                  /\
                  j < C
                )
              )
              /\
              v < ( A ` <. i , j >. )
            )
          )
          ->
          (
            (
              0 <_ ( B - i )
              /\
              ( B - ( i + 1 ) ) < ( B - i )
            )
            /\
            (
              (
                0 <_ ( i + 1 )
                /\
                ( i + 1 ) < B
              )
              /\
              (
                (
                  0 <
                  (
                    # `
                    { k e. ( ( ( i + 1 ) + 1 ) ..^ B ) |
                      ( A ` <. k , j >. ) <_ v
                    }
                  )
                  /\
                  (
                    0 <_ j
                    /\
                    j < C
                  )
                )
                /\
                v < ( A ` <. ( i + 1 ) , j >. )
              )
            )
          )
        ) $.
$}

${
  $d i j k v A B C $.

  shearsort-aux-down-definition $a |- (
    NTP4VCAuxDown A B C
  ) <->
  A. v e. ZZ
    A. i e. ZZ
      A. j e. ZZ
        (
          (
            (
              0 <_ i
              /\
              i < B
            )
            /\
            (
              (
                0 <
                (
                  # `
                  { k e. ( 0 ..^ i ) |
                    v < ( A ` <. k , j >. )
                  }
                )
                /\
                (
                  0 <_ j
                  /\
                  j < C
                )
              )
              /\
              ( A ` <. i , j >. ) <_ v
            )
          )
          ->
          (
            (
              0 <_ i
              /\
              ( i - 1 ) < i
            )
            /\
            (
              (
                0 <_ ( i - 1 )
                /\
                ( i - 1 ) < B
              )
              /\
              (
                (
                  0 <
                  (
                    # `
                    { k e. ( 0 ..^ ( i - 1 ) ) |
                      v < ( A ` <. k , j >. )
                    }
                  )
                  /\
                  (
                    0 <_ j
                    /\
                    j < C
                  )
                )
                /\
                ( A ` <. ( i - 1 ) , j >. ) <_ v
              )
            )
          )
        ) $.
$}

shearsort-final-definition $a |- (
  NTP4VCFinal A B C
) <->
(
  ( NTP4VCCrossSorted A B C )
  /\
  ( NTP4VCRowSnake A B C )
) $.

${
  $d m A B C D E F G H I J K $.

  shearsort-column-phase-definition $a |- (
    NTP4VCColumnPhase A B C D E F G H I J K
  ) <->
  (
    (
      G = H
      ->
      ( NTP4VCBounds B C D 1 J K )
    )
    /\
    (
      (
        G = H
        ->
        ( NTP4VCCrossSorted B J K )
      )
      ->
      A. m e. ( ZZ ^m ( ZZ X. ZZ ) )
        (
          (
            ( NTP4VCColumnPermuted m B J K )
            /\
            ( NTP4VCColumnSorted m J K )
          )
          ->
          (
            ( NTP4VCAuxUp m J K )
            /\
            (
              ( NTP4VCAuxDown m J K )
              /\
              (
                ( NTP4VCBounds m E F I J K )
                /\
                (
                  ( NTP4VCLogBound I ( G + 1 ) J )
                  /\
                  (
                    (
                      H < ( G + 1 )
                      ->
                      ( NTP4VCRowSnake m J K )
                    )
                    /\
                    ( NTP4VCOccPreserved A m J K )
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
  $d o q r v z A B C D E F G H I J $.

  shearsort-projection-phase-definition $a |- (
    NTP4VCProjectionPhase A B C D E F G H I J
  ) <->
  A. q e. ( ( ZZ X. ZZ ) ^m ZZ )
    (
      A. v e. ZZ
        (
          NTP4VCPairSpec
            C
            ( 1st ` ( q ` v ) )
            ( 2nd ` ( q ` v ) )
            H I J v
        )
      ->
      A. v e. ZZ
        (
          (
            NTP4VCPairSpec
              C
              ( 1st ` ( q ` v ) )
              ( 2nd ` ( q ` v ) )
              H I J v
          )
          ->
          (
            A. r e. ZZ
              (
                r = ( 1st ` ( q ` v ) )
                ->
                r = ( 1st ` ( q ` v ) )
              )
            /\
            A. z e. ( ZZ ^m ZZ )
              (
                A. v e. ZZ
                  ( z ` v ) = ( 1st ` ( q ` v ) )
                ->
                A. v e. ZZ
                  (
                    (
                      NTP4VCPairSpec
                        C
                        ( 1st ` ( q ` v ) )
                        ( 2nd ` ( q ` v ) )
                        H I J v
                    )
                    ->
                    (
                      A. r e. ZZ
                        (
                          r = ( 2nd ` ( q ` v ) )
                          ->
                          r = ( 2nd ` ( q ` v ) )
                        )
                      /\
                      A. o e. ( ZZ ^m ZZ )
                        (
                          A. v e. ZZ
                            ( o ` v ) = ( 2nd ` ( q ` v ) )
                          ->
                          (
                            NTP4VCColumnPhase
                              A B D E z o F G H I J
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
  $d v A B C D E F G H I $.

  shearsort-nzo-phase-definition $a |- (
    NTP4VCNZOPhase A B C D E F G H I
  ) <->
  (
    A. v e. ZZ
      ( NTP4VCNZOVC B C D G H I v )
    /\
    (
      NTP4VCProjectionPhase
        A B B C D E F G H I
    )
  ) $.
$}

${
  $d m A B C D E F G H I $.

  shearsort-loop-body-definition $a |- (
    NTP4VCLoopBody A B C D E F G H I
  ) <->
  A. m e. ( ZZ ^m ( ZZ X. ZZ ) )
    (
      (
        ( NTP4VCRowPermuted m B H I )
        /\
        ( NTP4VCRowSnake m H I )
      )
      ->
      (
        2 =/= 0
        /\
        (
          NTP4VCNZOPhase
            A m C D F G
            ( NTP4VCTDiv2 ( E + 1 ) )
            H I
        )
      )
    ) $.
$}

shearsort-loop-invariant-definition $a |- (
  NTP4VCLoopInvariant A B C D E F G H I
) <->
(
  (
    0 <_ F
    /\
    F <_ G
  )
  /\
  (
    ( NTP4VCBounds B C D E H I )
    /\
    (
      ( NTP4VCLogBound E F H )
      /\
      (
        (
          G < F
          ->
          ( NTP4VCRowSnake B H I )
        )
        /\
        ( NTP4VCOccPreserved A B H I )
      )
    )
  )
) $.

shearsort-post-loop-definition $a |- (
  NTP4VCPostLoop A B C D E F G H
) <->
(
  ( NTP4VCBounds B C D E G H )
  /\
  (
    ( NTP4VCLogBound E ( F + 1 ) G )
    /\
    (
      (
        F < ( F + 1 )
        ->
        ( NTP4VCRowSnake B G H )
      )
      /\
      ( NTP4VCOccPreserved A B G H )
    )
  )
) $.

shearsort-completion-definition $a |- (
  NTP4VCCompletion A B C D
) <->
(
  ( NTP4VCCrossSorted B C D )
  ->
  (
    ( NTP4VCFinal B C D )
    /\
    ( NTP4VCOccPreserved A B C D )
  )
) $.

shearsort-initial-definition $a |- (
  NTP4VCInitial A B C D
) <->
(
  (
    NTP4VCBounds
      A ( NTP4VCConst 0 ) ( NTP4VCConst C ) C C D
  )
  /\
  (
    ( NTP4VCLogBound C 0 C )
    /\
    (
      B < 0
      ->
      ( NTP4VCRowSnake A C D )
    )
  )
) $.

${
  $d i k l m o p z A B C $.

  shearsort-main-definition $a |- (
    NTP4VCMain A B C
  ) <->
  (
    (
      B =/= 0
      ->
      (
        (
          (
            0 <_ 0
            /\
            0 <_ ( B - 1 )
          )
          /\
          (
            ( ( B - 1 ) x. ( NTP4VCPow2 0 ) ) < B
            /\
            B <_
              ( ( NTP4VCPow2 0 ) x. ( ( B - 1 ) + 1 ) )
          )
        )
        /\
        A. p e. ZZ
          A. l e. ZZ
            (
              (
                (
                  0 <_ l
                  /\
                  0 <_ p
                )
                /\
                (
                  (
                    l =/= 0
                    ->
                    ( NTP4VCPow2 ( l - 1 ) ) <_ B
                  )
                  /\
                  (
                    ( p x. ( NTP4VCPow2 l ) ) < B
                    /\
                    B <_
                      ( ( NTP4VCPow2 l ) x. ( p + 1 ) )
                  )
                )
              )
              ->
              (
                (
                  p =/= 0
                  ->
                  (
                    2 =/= 0
                    /\
                    (
                      (
                        0 <_ p
                        /\
                        ( NTP4VCTDiv2 p ) < p
                      )
                      /\
                      (
                        (
                          0 <_ ( l + 1 )
                          /\
                          0 <_ ( NTP4VCTDiv2 p )
                        )
                        /\
                        (
                          (
                            ( l + 1 ) =/= 0
                            ->
                            (
                              NTP4VCPow2
                                ( ( l + 1 ) - 1 )
                            ) <_ B
                          )
                          /\
                          (
                            (
                              ( NTP4VCTDiv2 p )
                              x.
                              ( NTP4VCPow2 ( l + 1 ) )
                            ) < B
                            /\
                            B <_
                            (
                              ( NTP4VCPow2 ( l + 1 ) )
                              x.
                              ( ( NTP4VCTDiv2 p ) + 1 )
                            )
                          )
                        )
                      )
                    )
                  )
                )
                /\
                (
                  p = 0
                  ->
                  (
                    A. o e. ( ZZ ^m ZZ )
                      A. z e. ( ZZ ^m ZZ )
                        A. m e. ( ZZ ^m ( ZZ X. ZZ ) )
                          (
                            ( NTP4VCBounds m z o 1 B C )
                            ->
                            ( NTP4VCCrossSorted m B C )
                          )
                    /\
                    (
                      0 <_ ( l + 1 )
                      ->
                      (
                        ( NTP4VCInitial A l B C )
                        /\
                        A. o e. ( ZZ ^m ZZ )
                          A. z e. ( ZZ ^m ZZ )
                            A. k e. ZZ
                              A. m e. ( ZZ ^m ( ZZ X. ZZ ) )
                                (
                                  A. i e. ZZ
                                    (
                                      (
                                        NTP4VCLoopInvariant
                                          A m z o k i l B C
                                      )
                                      ->
                                      (
                                        NTP4VCLoopBody
                                          A m z o k i l B C
                                      )
                                    )
                                  /\
                                  (
                                    (
                                      NTP4VCPostLoop
                                        A m z o k l B C
                                    )
                                    ->
                                    (
                                      ( NTP4VCBounds m z o 1 B C )
                                      /\
                                      ( NTP4VCCompletion A m B C )
                                    )
                                  )
                                )
                      )
                    )
                    /\
                    (
                      ( l + 1 ) < 0
                      ->
                      (
                        (
                          NTP4VCBounds
                            A
                            ( NTP4VCConst 0 )
                            ( NTP4VCConst B )
                            1 B C
                        )
                        /\
                        (
                          ( NTP4VCCrossSorted A B C )
                          ->
                          ( NTP4VCFinal A B C )
                        )
                      )
                    )
                  )
                )
              )
            )
      )
    )
    /\
    (
      B = 0
      ->
      ( NTP4VCFinal A B C )
    )
  ) $.
$}

${
  $d a b c $.

  ntp4vc-pearl-verifythis-2021-shearsort-shear-sort-vc $a |-
    A. b e. NN0
      A. c e. NN0
        A. a e. ( ZZ ^m ( ZZ X. ZZ ) )
          ( NTP4VCMain a b c )
  $.
$}
