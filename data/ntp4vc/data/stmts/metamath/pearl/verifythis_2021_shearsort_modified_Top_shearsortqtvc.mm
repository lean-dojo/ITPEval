$(
  Statement-only formalization of the NTP4VC corpus artifact
  pearl/verifythis_2021_shearsort_modified_Top_shearsortqtvc: the complete
  verification condition for modified ShearSort, including alternating row
  sorting, column sorting to a fixed point, inversion decrease, snake order,
  and preservation of matrix-entry multiplicities. This file contains no
  proof.
$)

$[ lib/set.mm $]

$(
  NTP4VCMatrix represents the source matrix type by two nonnegative integer
  dimensions and an arbitrary total integer-valued function on integer index
  pairs. Thus all source lookups, including distinct out-of-bounds lookups,
  remain present. Occurrence counts and inversion counts use exact finite
  half-open integer intervals.

  NTP4VCTDiv2 is signed division by two truncated toward zero, and
  NTP4VCCMod2 is its associated signed remainder. This follows the pinned
  Why3 source and the agreeing Lean and Isabelle exports; the Rocq export
  uses quotient in the parity tests.

  The biconditional definitions only factor the generated verification
  condition. Expanding them recovers both matrix parameters, all integer,
  Boolean, and intermediate-matrix quantifiers, every loop invariant and
  branch, the inversion-decrease conditions, and the final snake-order and
  multiplicity conclusions. Boolean values use SetMM's set { 0, 1 }, with 1
  true and 0 false. Every auxiliary $a is syntax or a faithful definition. The
  final $a is Metamath's native unproved statement encoding; there is no $p
  declaration.
$)

$c
  NTP4VCMatrix NTP4VCRows NTP4VCColumns NTP4VCElts NTP4VCEntry
  NTP4VCLast NTP4VCTDiv2 NTP4VCCMod2 NTP4VCParity
  NTP4VCMocc NTP4VCLt NTP4VCSnakeOrder NTP4VCInversions
  NTP4VCSortedRow NTP4VCSortedColumn NTP4VCSameShape NTP4VCMoccEq
  NTP4VCPrefixRows NTP4VCRowFrame NTP4VCRowPost
  NTP4VCRowInvariant NTP4VCRowStep
  NTP4VCPrefixColumns NTP4VCAllSame NTP4VCColumnFrame
  NTP4VCColumnSame NTP4VCColumnPost NTP4VCColumnInvariant
  NTP4VCColumnUpdate NTP4VCColumnStep NTP4VCOrderedSquare
  NTP4VCColumnFinal NTP4VCColumnBase NTP4VCColumnLoop
  NTP4VCColumnPhase NTP4VCMain
$.

ntp4vc-matrix-syntax
  $a class NTP4VCMatrix $.
ntp4vc-rows-syntax
  $a class ( NTP4VCRows A ) $.
ntp4vc-columns-syntax
  $a class ( NTP4VCColumns A ) $.
ntp4vc-elts-syntax
  $a class ( NTP4VCElts A ) $.
ntp4vc-entry-syntax
  $a class ( NTP4VCEntry A B C ) $.
ntp4vc-last-syntax
  $a class ( NTP4VCLast A ) $.
ntp4vc-tdiv2-syntax
  $a class ( NTP4VCTDiv2 A ) $.
ntp4vc-cmod2-syntax
  $a class ( NTP4VCCMod2 A ) $.
ntp4vc-parity-syntax
  $a class ( NTP4VCParity A ) $.
ntp4vc-mocc-syntax
  $a class ( NTP4VCMocc A B ) $.
ntp4vc-inversions-syntax
  $a class ( NTP4VCInversions A ) $.

ntp4vc-lt-syntax
  $a wff ( NTP4VCLt A B C D ) $.
ntp4vc-snake-order-syntax
  $a wff ( NTP4VCSnakeOrder A ) $.
ntp4vc-sorted-row-syntax
  $a wff ( NTP4VCSortedRow A B C ) $.
ntp4vc-sorted-column-syntax
  $a wff ( NTP4VCSortedColumn A B ) $.
ntp4vc-same-shape-syntax
  $a wff ( NTP4VCSameShape A B ) $.
ntp4vc-mocc-eq-syntax
  $a wff ( NTP4VCMoccEq A B ) $.
ntp4vc-prefix-rows-syntax
  $a wff ( NTP4VCPrefixRows A B ) $.
ntp4vc-row-frame-syntax
  $a wff ( NTP4VCRowFrame A B C ) $.
ntp4vc-row-post-syntax
  $a wff ( NTP4VCRowPost A B C ) $.
ntp4vc-row-invariant-syntax
  $a wff ( NTP4VCRowInvariant A B C D ) $.
ntp4vc-row-step-syntax
  $a wff ( NTP4VCRowStep A B C D ) $.
ntp4vc-prefix-columns-syntax
  $a wff ( NTP4VCPrefixColumns A B ) $.
ntp4vc-all-same-syntax
  $a wff ( NTP4VCAllSame A B ) $.
ntp4vc-column-frame-syntax
  $a wff ( NTP4VCColumnFrame A B C ) $.
ntp4vc-column-same-syntax
  $a wff ( NTP4VCColumnSame A B C ) $.
ntp4vc-column-post-syntax
  $a wff ( NTP4VCColumnPost A B C D ) $.
ntp4vc-column-invariant-syntax
  $a wff ( NTP4VCColumnInvariant A B C D E ) $.
ntp4vc-column-update-syntax
  $a wff ( NTP4VCColumnUpdate A B C D E F ) $.
ntp4vc-column-step-syntax
  $a wff ( NTP4VCColumnStep A B C D E ) $.
ntp4vc-ordered-square-syntax
  $a wff ( NTP4VCOrderedSquare A B ) $.
ntp4vc-column-final-syntax
  $a wff ( NTP4VCColumnFinal A B C D E ) $.
ntp4vc-column-base-syntax
  $a wff ( NTP4VCColumnBase A B ) $.
ntp4vc-column-loop-syntax
  $a wff ( NTP4VCColumnLoop A B C ) $.
ntp4vc-column-phase-syntax
  $a wff ( NTP4VCColumnPhase A B C ) $.
ntp4vc-main-syntax
  $a wff ( NTP4VCMain A B ) $.

ntp4vc-matrix-definition $a |- NTP4VCMatrix =
  (
    ( NN0 X. NN0 )
    X.
    ( ZZ ^m ( ZZ X. ZZ ) )
  )
$.

ntp4vc-rows-definition $a |- (
  NTP4VCRows A
) = (
  1st ` ( 1st ` A )
) $.

ntp4vc-columns-definition $a |- (
  NTP4VCColumns A
) = (
  2nd ` ( 1st ` A )
) $.

ntp4vc-elts-definition $a |- (
  NTP4VCElts A
) = (
  2nd ` A
) $.

ntp4vc-entry-definition $a |- (
  NTP4VCEntry A B C
) = (
  ( NTP4VCElts A ) ` <. B , C >.
) $.

ntp4vc-last-definition $a |- (
  NTP4VCLast A
) = (
  ( NTP4VCColumns A ) - 1
) $.

ntp4vc-tdiv2-definition $a |- (
  NTP4VCTDiv2 A
) = if (
  A < 0 ,
  ( |^ ` ( A / 2 ) ) ,
  ( |_ ` ( A / 2 ) )
) $.

ntp4vc-cmod2-definition $a |- (
  NTP4VCCMod2 A
) = (
  A - ( 2 x. ( NTP4VCTDiv2 A ) )
) $.

ntp4vc-parity-definition $a |- (
  NTP4VCParity A
) = if (
  ( NTP4VCCMod2 A ) = 0 ,
  1 ,
  0
) $.

${
  $d i j A B $.

  ntp4vc-mocc-definition $a |- (
    NTP4VCMocc A B
  ) =
  sum_ i e. ( 0 ..^ ( NTP4VCRows B ) )
    (
      # `
      { j e. ( 0 ..^ ( NTP4VCColumns B ) ) |
        ( NTP4VCEntry B i j ) = A
      }
    ) $.
$}

ntp4vc-lt-definition $a |- (
  NTP4VCLt A B C D
) <->
(
  A < C
  \/
  (
    A = C
    /\
    (
      (
        ( NTP4VCCMod2 A ) = 0
        /\
        B < D
      )
      \/
      (
        -. ( NTP4VCCMod2 A ) = 0
        /\
        D < B
      )
    )
  )
) $.

${
  $d i j k l A $.

  ntp4vc-snake-order-definition $a |- (
    NTP4VCSnakeOrder A
  ) <->
  A. i e. ZZ
    A. j e. ZZ
      A. k e. ZZ
        A. l e. ZZ
          (
            (
              0 <_ i
              /\
              i < ( NTP4VCRows A )
            )
            ->
            (
              (
                0 <_ j
                /\
                j < ( NTP4VCColumns A )
              )
              ->
              (
                (
                  0 <_ k
                  /\
                  k < ( NTP4VCRows A )
                )
                ->
                (
                  (
                    0 <_ l
                    /\
                    l < ( NTP4VCColumns A )
                  )
                  ->
                  (
                    ( NTP4VCLt i j k l )
                    ->
                    (
                      ( NTP4VCEntry A i j )
                      <_
                      ( NTP4VCEntry A k l )
                    )
                  )
                )
              )
            )
          ) $.
$}

${
  $d i j k l A $.

  ntp4vc-inversions-definition $a |- (
    NTP4VCInversions A
  ) =
  sum_ i e. ( 0 ..^ ( NTP4VCRows A ) )
    sum_ j e. ( 0 ..^ ( NTP4VCColumns A ) )
      sum_ k e. ( 0 ..^ ( NTP4VCRows A ) )
        (
          # `
          { l e. ( 0 ..^ ( NTP4VCColumns A ) ) |
            (
              ( NTP4VCLt i j k l )
              /\
              (
                ( NTP4VCEntry A k l )
                <
                ( NTP4VCEntry A i j )
              )
            )
          }
        ) $.
$}

${
  $d j l A B C $.

  ntp4vc-sorted-row-definition $a |- (
    NTP4VCSortedRow A B C
  ) <->
  (
    C e. { 0 , 1 }
    /\
    (
      (
        0 <_ B
        /\
        B < ( NTP4VCRows A )
      )
      /\
      (
        (
          C = 1
          ->
          A. j e. ZZ
            A. l e. ZZ
              (
                (
                  (
                    0 <_ j
                    /\
                    j <_ l
                  )
                  /\
                  l < ( NTP4VCColumns A )
                )
                ->
                (
                  ( NTP4VCEntry A B j )
                  <_
                  ( NTP4VCEntry A B l )
                )
              )
        )
        /\
        (
          C = 0
          ->
          A. j e. ZZ
            A. l e. ZZ
              (
                (
                  (
                    0 <_ j
                    /\
                    j <_ l
                  )
                  /\
                  l < ( NTP4VCColumns A )
                )
                ->
                (
                  ( NTP4VCEntry A B l )
                  <_
                  ( NTP4VCEntry A B j )
                )
              )
        )
      )
    )
  ) $.
$}

${
  $d i k A B $.

  ntp4vc-sorted-column-definition $a |- (
    NTP4VCSortedColumn A B
  ) <->
  (
    (
      0 <_ B
      /\
      B < ( NTP4VCColumns A )
    )
    /\
    A. i e. ZZ
      A. k e. ZZ
        (
          (
            (
              0 <_ i
              /\
              i <_ k
            )
            /\
            k < ( NTP4VCRows A )
          )
          ->
          (
            ( NTP4VCEntry A i B )
            <_
            ( NTP4VCEntry A k B )
          )
        )
  ) $.
$}

ntp4vc-same-shape-definition $a |- (
  NTP4VCSameShape A B
) <->
(
  ( NTP4VCRows A ) = ( NTP4VCRows B )
  /\
  ( NTP4VCColumns A ) = ( NTP4VCColumns B )
) $.

${
  $d x A B $.

  ntp4vc-mocc-eq-definition $a |- (
    NTP4VCMoccEq A B
  ) <->
  A. x e. ZZ
    (
      ( NTP4VCMocc x A )
      =
      ( NTP4VCMocc x B )
    ) $.
$}

${
  $d k A B $.

  ntp4vc-prefix-rows-definition $a |- (
    NTP4VCPrefixRows A B
  ) <->
  A. k e. ZZ
    (
      (
        0 <_ k
        /\
        k < B
      )
      ->
      (
        NTP4VCSortedRow
          A
          k
          ( NTP4VCParity k )
      )
    ) $.
$}

${
  $d i j A B C $.

  ntp4vc-row-frame-definition $a |- (
    NTP4VCRowFrame A B C
  ) <->
  A. i e. ZZ
    A. j e. ZZ
      (
        (
          0 <_ i
          /\
          i < ( NTP4VCRows A )
        )
        ->
        (
          (
            0 <_ j
            /\
            j < ( NTP4VCColumns A )
          )
          ->
          (
            -. i = C
            ->
            (
              ( NTP4VCEntry A i j )
              =
              ( NTP4VCEntry B i j )
            )
          )
        )
      ) $.
$}

ntp4vc-row-post-definition $a |- (
  NTP4VCRowPost A B C
) <->
(
  ( NTP4VCRowFrame A B C )
  /\
  (
    ( NTP4VCMoccEq A B )
    /\
    (
      (
        NTP4VCSortedRow
          A
          C
          ( NTP4VCParity C )
      )
      /\
      (
        ( NTP4VCInversions A )
        <_
        ( NTP4VCInversions B )
      )
    )
  )
) $.

ntp4vc-row-invariant-definition $a |- (
  NTP4VCRowInvariant A B C D
) <->
(
  ( NTP4VCPrefixRows A D )
  /\
  (
    ( NTP4VCMoccEq A B )
    /\
    (
      ( NTP4VCInversions A )
      <_
      ( NTP4VCInversions C )
    )
  )
) $.

${
  $d m A B C D $.

  ntp4vc-row-step-definition $a |- (
    NTP4VCRowStep A B C D
  ) <->
  (
    2 =/= 0
    /\
    (
      (
        0 <_ D
        /\
        D < ( NTP4VCRows A )
      )
      /\
      A. m e. NTP4VCMatrix
        (
          ( NTP4VCSameShape m A )
          ->
          (
            ( NTP4VCRowPost m A D )
            ->
            (
              NTP4VCRowInvariant
                m
                B
                C
                ( D + 1 )
            )
          )
        )
    )
  ) $.
$}

${
  $d l A B $.

  ntp4vc-prefix-columns-definition $a |- (
    NTP4VCPrefixColumns A B
  ) <->
  A. l e. ZZ
    (
      (
        0 <_ l
        /\
        l < B
      )
      ->
      ( NTP4VCSortedColumn A l )
    ) $.
$}

${
  $d i j A B $.

  ntp4vc-all-same-definition $a |- (
    NTP4VCAllSame A B
  ) <->
  A. i e. ZZ
    A. j e. ZZ
      (
        (
          0 <_ i
          /\
          i < ( NTP4VCRows A )
        )
        ->
        (
          (
            0 <_ j
            /\
            j < ( NTP4VCColumns A )
          )
          ->
          (
            ( NTP4VCEntry A i j )
            =
            ( NTP4VCEntry B i j )
          )
        )
      ) $.
$}

${
  $d i j A B C $.

  ntp4vc-column-frame-definition $a |- (
    NTP4VCColumnFrame A B C
  ) <->
  A. i e. ZZ
    A. j e. ZZ
      (
        (
          0 <_ i
          /\
          i < ( NTP4VCRows A )
        )
        ->
        (
          (
            0 <_ j
            /\
            j < ( NTP4VCColumns A )
          )
          ->
          (
            -. j = C
            ->
            (
              ( NTP4VCEntry A i j )
              =
              ( NTP4VCEntry B i j )
            )
          )
        )
      ) $.
$}

${
  $d i A B C $.

  ntp4vc-column-same-definition $a |- (
    NTP4VCColumnSame A B C
  ) <->
  A. i e. ZZ
    (
      (
        0 <_ i
        /\
        i < ( NTP4VCRows A )
      )
      ->
      (
        ( NTP4VCEntry A i C )
        =
        ( NTP4VCEntry B i C )
      )
    ) $.
$}

ntp4vc-column-post-definition $a |- (
  NTP4VCColumnPost A B C D
) <->
(
  D e. { 0 , 1 }
  /\
  (
    ( NTP4VCColumnFrame A B C )
    /\
    (
      ( NTP4VCMoccEq A B )
      /\
      (
        (
          D = 1
          ->
          ( NTP4VCColumnSame A B C )
        )
        /\
        (
          ( NTP4VCSortedColumn A C )
          /\
          (
            (
              ( NTP4VCInversions A )
              <_
              ( NTP4VCInversions B )
            )
            /\
            (
              D = 0
              ->
              (
                ( NTP4VCInversions A )
                <
                ( NTP4VCInversions B )
              )
            )
          )
        )
      )
    )
  )
) $.

ntp4vc-column-invariant-definition $a |- (
  NTP4VCColumnInvariant A B C D E
) <->
(
  A e. { 0 , 1 }
  /\
  (
    (
      A = 1
      ->
      ( NTP4VCAllSame B C )
    )
    /\
    (
      ( NTP4VCPrefixColumns B E )
      /\
      (
        ( NTP4VCMoccEq B D )
        /\
        (
          (
            ( NTP4VCInversions B )
            <_
            ( NTP4VCInversions C )
          )
          /\
          (
            A = 0
            ->
            (
              ( NTP4VCInversions B )
              <
              ( NTP4VCInversions C )
            )
          )
        )
      )
    )
  )
) $.

ntp4vc-column-update-definition $a |- (
  NTP4VCColumnUpdate A B C D E F
) <->
(
  (
    B = 0
    ->
    (
      NTP4VCColumnInvariant
        0 C D E F
    )
  )
  /\
  (
    B = 1
    ->
    (
      NTP4VCColumnInvariant
        A C D E F
    )
  )
) $.

${
  $d b m A B C D E $.

  ntp4vc-column-step-definition $a |- (
    NTP4VCColumnStep A B C D E
  ) <->
  (
    (
      0 <_ E
      /\
      E < ( NTP4VCColumns B )
    )
    /\
    A. m e. NTP4VCMatrix
      (
        ( NTP4VCSameShape m B )
        ->
        A. b e. { 0 , 1 }
          (
            ( NTP4VCColumnPost m B E b )
            ->
            (
              NTP4VCColumnUpdate
                A
                b
                m
                C
                D
                ( E + 1 )
            )
          )
      )
  ) $.
$}

${
  $d i j k l A B $.

  ntp4vc-ordered-square-definition $a |- (
    NTP4VCOrderedSquare A B
  ) <->
  A. i e. ZZ
    A. j e. ZZ
      A. k e. ZZ
        A. l e. ZZ
          (
            (
              (
                0 <_ i
                /\
                i < ( NTP4VCColumns B )
              )
              /\
              (
                (
                  0 <_ j
                  /\
                  j < ( NTP4VCColumns B )
                )
                /\
                (
                  (
                    0 <_ k
                    /\
                    k < ( NTP4VCColumns B )
                  )
                  /\
                  (
                    0 <_ l
                    /\
                    l < ( NTP4VCColumns B )
                  )
                )
              )
            )
            ->
            (
              ( NTP4VCLt i j k l )
              ->
              (
                ( NTP4VCEntry A i j )
                <_
                ( NTP4VCEntry A k l )
              )
            )
          ) $.
$}

ntp4vc-column-final-definition $a |- (
  NTP4VCColumnFinal A B C D E
) <->
(
  A e. { 0 , 1 }
  /\
  (
    (
      A = 1
      ->
      (
        ( NTP4VCOrderedSquare B D )
        /\
        (
          ( NTP4VCSnakeOrder B )
          /\
          ( NTP4VCMoccEq B D )
        )
      )
    )
    /\
    (
      A = 0
      ->
      (
        (
          0 <_ ( NTP4VCInversions E )
          /\
          (
            ( NTP4VCInversions B )
            <
            ( NTP4VCInversions E )
          )
        )
        /\
        ( NTP4VCMoccEq B D )
      )
    )
  )
) $.

ntp4vc-column-base-definition $a |- (
  NTP4VCColumnBase A B
) <->
(
  ( NTP4VCPrefixColumns A 0 )
  /\
  (
    ( NTP4VCMoccEq A B )
    /\
    (
      ( NTP4VCInversions A )
      <_
      ( NTP4VCInversions A )
    )
  )
) $.

${
  $d b j m A B C $.

  ntp4vc-column-loop-definition $a |- (
    NTP4VCColumnLoop A B C
  ) <->
  A. b e. { 0 , 1 }
    A. m e. NTP4VCMatrix
      (
        ( NTP4VCSameShape m A )
        ->
        (
          A. j e. ZZ
            (
              (
                (
                  0 <_ j
                  /\
                  j <_ ( NTP4VCLast B )
                )
                /\
                (
                  NTP4VCColumnInvariant
                    b m A B j
                )
              )
              ->
              (
                NTP4VCColumnStep
                  b m A B j
              )
            )
          /\
          (
            (
              NTP4VCColumnInvariant
                b
                m
                A
                B
                ( ( NTP4VCLast B ) + 1 )
            )
            ->
            (
              NTP4VCColumnFinal
                b m A B C
            )
          )
        )
      ) $.
$}

ntp4vc-column-phase-definition $a |- (
  NTP4VCColumnPhase A B C
) <->
(
  (
    0 <_ ( ( NTP4VCLast B ) + 1 )
    ->
    (
      ( NTP4VCColumnBase A B )
      /\
      ( NTP4VCColumnLoop A B C )
    )
  )
  /\
  (
    ( ( NTP4VCLast B ) + 1 ) < 0
    ->
    (
      ( NTP4VCOrderedSquare A B )
      /\
      (
        ( NTP4VCSnakeOrder A )
        /\
        ( NTP4VCMoccEq A B )
      )
    )
  )
) $.

${
  $d i m A B $.

  ntp4vc-main-definition $a |- (
    NTP4VCMain A B
  ) <->
  (
    (
      ( NTP4VCRows A ) = ( NTP4VCColumns A )
      /\
      (
        ( NTP4VCSameShape B A )
        /\
        ( NTP4VCMoccEq B A )
      )
    )
    ->
    (
      (
        0 <_ ( ( NTP4VCLast A ) + 1 )
        ->
        (
          (
            NTP4VCRowInvariant
              B A B 0
          )
          /\
          A. m e. NTP4VCMatrix
            (
              ( NTP4VCSameShape m B )
              ->
              (
                A. i e. ZZ
                  (
                    (
                      (
                        0 <_ i
                        /\
                        i <_ ( NTP4VCLast A )
                      )
                      /\
                      (
                        NTP4VCRowInvariant
                          m A B i
                      )
                    )
                    ->
                    (
                      NTP4VCRowStep
                        m A B i
                    )
                  )
                /\
                (
                  (
                    NTP4VCRowInvariant
                      m
                      A
                      B
                      ( ( NTP4VCLast A ) + 1 )
                  )
                  ->
                  (
                    NTP4VCColumnPhase
                      m A B
                  )
                )
              )
            )
        )
      )
      /\
      (
        ( ( NTP4VCLast A ) + 1 ) < 0
        ->
        (
          NTP4VCColumnPhase
            B A B
        )
      )
    )
  ) $.
$}

${
  $d m n $.

  ntp4vc-pearl-verifythis-2021-shearsort-modified-top-shearsort-vc $a |-
    A. m e. NTP4VCMatrix
      A. n e. NTP4VCMatrix
        ( NTP4VCMain m n )
  $.
$}
