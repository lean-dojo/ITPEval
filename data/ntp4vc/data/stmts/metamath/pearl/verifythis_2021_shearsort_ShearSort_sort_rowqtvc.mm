$(
  Statement-only formalization of the NTP4VC corpus artifact
  pearl/verifythis_2021_shearsort_ShearSort_sort_rowqtvc
  (ntp4vc__metamath__pearl/verifythis_2021_shearsort_ShearSort_sort_rowqtvc):
  the complete verification condition for copying one integer-matrix row,
  sorting it, optionally reversing it, and writing it back with the requested
  order and permutation guarantees while preserving every other row. This
  file contains no proof.
$)

$[ lib/set.mm $]

$(
  Matrices retain nonnegative integer dimensions and an arbitrary total
  integer-pair-indexed entry function. Integer lists are finite words over
  ZZ; their total source lookup returns zero outside the converted natural
  index range. Occurrence equality uses finite half-open integer intervals.

  The biconditional definitions below factor, without discharging, the full
  generated verification condition: list-update laws, read and write loop
  invariants, arbitrary same-shaped intermediate matrices, the abstract sort
  contract, every reversal invariant and swap obligation, both loop exits,
  and both negative-range branches. Booleans are SetMM elements of 2, with
  1 true and 0 false. The inclusive upper bound in the generated swap-frame
  obligation is retained exactly.

  Every $a before the last declaration is syntax or a faithful definition.
  The last $a is the accepted Metamath statement-only encoding; there is no
  $p declaration in this file.
$)

$c
  NTP4VCMatrix NTP4VCRows NTP4VCColumns NTP4VCElts NTP4VCEntry
  NTP4VCToNat NTP4VCAt NTP4VCSet NTP4VCListFun NTP4VCFunUpdate
  NTP4VCNumof NTP4VCPermut NTP4VCListUpdateLaw
  NTP4VCSameShape NTP4VCValidIndex NTP4VCPrefix NTP4VCOtherRows
  NTP4VCRowFun NTP4VCRowSorted NTP4VCRowPermuted NTP4VCPost
  NTP4VCListSorted NTP4VCListPermuted NTP4VCMatrixUpdate
  NTP4VCWriteIteration NTP4VCWriteLoop
  NTP4VCReverseInitial NTP4VCReverseInvariant NTP4VCSwapEffect
  NTP4VCReverseStepPost NTP4VCSwapCase NTP4VCReverseLoop
  NTP4VCAfterSort NTP4VCReadIteration NTP4VCReadLoop NTP4VCMain
$.

ntp4vc-matrix-syntax $a class NTP4VCMatrix $.
ntp4vc-rows-syntax $a class ( NTP4VCRows A ) $.
ntp4vc-columns-syntax $a class ( NTP4VCColumns A ) $.
ntp4vc-elts-syntax $a class ( NTP4VCElts A ) $.
ntp4vc-entry-syntax $a class ( NTP4VCEntry A B C ) $.
ntp4vc-to-nat-syntax $a class ( NTP4VCToNat A ) $.
ntp4vc-at-syntax $a class ( NTP4VCAt A B ) $.
ntp4vc-set-syntax $a class ( NTP4VCSet A B C ) $.
ntp4vc-list-fun-syntax $a class ( NTP4VCListFun A ) $.
ntp4vc-fun-update-syntax $a class ( NTP4VCFunUpdate A B C ) $.
ntp4vc-numof-syntax $a class ( NTP4VCNumof A B C D ) $.
ntp4vc-row-fun-syntax $a class ( NTP4VCRowFun A B ) $.
ntp4vc-matrix-update-syntax
  $a class ( NTP4VCMatrixUpdate A B C D ) $.

ntp4vc-permut-syntax
  $a wff ( NTP4VCPermut A B C D ) $.
ntp4vc-list-update-law-syntax
  $a wff ( NTP4VCListUpdateLaw A B C ) $.
ntp4vc-same-shape-syntax
  $a wff ( NTP4VCSameShape A B ) $.
ntp4vc-valid-index-syntax
  $a wff ( NTP4VCValidIndex A B C ) $.
ntp4vc-prefix-syntax
  $a wff ( NTP4VCPrefix A B C D ) $.
ntp4vc-other-rows-syntax
  $a wff ( NTP4VCOtherRows A B C ) $.
ntp4vc-row-sorted-syntax
  $a wff ( NTP4VCRowSorted A B C ) $.
ntp4vc-row-permuted-syntax
  $a wff ( NTP4VCRowPermuted A B C ) $.
ntp4vc-post-syntax
  $a wff ( NTP4VCPost A B C D ) $.
ntp4vc-list-sorted-syntax
  $a wff ( NTP4VCListSorted A ) $.
ntp4vc-list-permuted-syntax
  $a wff ( NTP4VCListPermuted A B ) $.
ntp4vc-write-iteration-syntax
  $a wff ( NTP4VCWriteIteration A B C D E F ) $.
ntp4vc-write-loop-syntax
  $a wff ( NTP4VCWriteLoop A B C D ) $.
ntp4vc-reverse-initial-syntax
  $a wff ( NTP4VCReverseInitial A ) $.
ntp4vc-reverse-invariant-syntax
  $a wff ( NTP4VCReverseInvariant A B C D ) $.
ntp4vc-swap-effect-syntax
  $a wff ( NTP4VCSwapEffect A B C D ) $.
ntp4vc-reverse-step-post-syntax
  $a wff ( NTP4VCReverseStepPost A B C D ) $.
ntp4vc-swap-case-syntax
  $a wff ( NTP4VCSwapCase A B C D ) $.
ntp4vc-reverse-loop-syntax
  $a wff ( NTP4VCReverseLoop A B C D ) $.
ntp4vc-after-sort-syntax
  $a wff ( NTP4VCAfterSort A B C D ) $.
ntp4vc-read-iteration-syntax
  $a wff ( NTP4VCReadIteration A B C D E ) $.
ntp4vc-read-loop-syntax
  $a wff ( NTP4VCReadLoop A B C D ) $.
ntp4vc-main-syntax
  $a wff ( NTP4VCMain A B C ) $.

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

ntp4vc-to-nat-definition $a |- (
  NTP4VCToNat A
) = if (
  A < 0 ,
  0 ,
  A
) $.

ntp4vc-at-definition $a |- (
  NTP4VCAt A B
) = if (
  ( NTP4VCToNat B ) < ( # ` A ) ,
  ( A ` ( NTP4VCToNat B ) ) ,
  0
) $.

${
  $d k A B C $.

  ntp4vc-set-definition $a |- (
    NTP4VCSet A B C
  ) = (
    k e. ( 0 ..^ ( # ` A ) ) |->
      if (
        k = ( NTP4VCToNat B ) ,
        C ,
        ( A ` k )
      )
  ) $.
$}

${
  $d k A $.

  ntp4vc-list-fun-definition $a |- (
    NTP4VCListFun A
  ) = (
    k e. ZZ |-> ( NTP4VCAt A k )
  ) $.
$}

${
  $d k A B C $.

  ntp4vc-fun-update-definition $a |- (
    NTP4VCFunUpdate A B C
  ) = (
    k e. ZZ |->
      if (
        k = B ,
        C ,
        ( A ` k )
      )
  ) $.
$}

${
  $d k A B C D $.

  ntp4vc-numof-definition $a |- (
    NTP4VCNumof A B C D
  ) = (
    # `
    { k e. ( C ..^ D ) |
      ( A ` k ) = B
    }
  ) $.
$}

${
  $d v A B C D $.

  ntp4vc-permut-definition $a |- (
    NTP4VCPermut A B C D
  ) <->
  A. v e. ZZ
    (
      ( NTP4VCNumof A v C D )
      =
      ( NTP4VCNumof B v C D )
    ) $.
$}

ntp4vc-list-update-law-definition $a |- (
  NTP4VCListUpdateLaw A B C
) <->
(
  ( NTP4VCListFun ( NTP4VCSet A B C ) )
  =
  (
    NTP4VCFunUpdate
      ( NTP4VCListFun A )
      B
      C
  )
) $.

ntp4vc-same-shape-definition $a |- (
  NTP4VCSameShape A B
) <->
(
  ( NTP4VCRows A ) = ( NTP4VCRows B )
  /\
  ( NTP4VCColumns A ) = ( NTP4VCColumns B )
) $.

ntp4vc-valid-index-definition $a |- (
  NTP4VCValidIndex A B C
) <->
(
  (
    0 <_ B
    /\
    B < ( NTP4VCRows A )
  )
  /\
  (
    0 <_ C
    /\
    C < ( NTP4VCColumns A )
  )
) $.

${
  $d k A B C D $.

  ntp4vc-prefix-definition $a |- (
    NTP4VCPrefix A B C D
  ) <->
  A. k e. ZZ
    (
      (
        0 <_ k
        /\
        k < D
      )
      ->
      (
        ( NTP4VCAt A k )
        =
        ( NTP4VCEntry B C k )
      )
    ) $.
$}

${
  $d k l A B C $.

  ntp4vc-other-rows-definition $a |- (
    NTP4VCOtherRows A B C
  ) <->
  A. k e. ZZ
    A. l e. ZZ
      (
        (
          (
            0 <_ k
            /\
            k < ( NTP4VCRows A )
          )
          /\
          (
            (
              0 <_ l
              /\
              l < ( NTP4VCColumns A )
            )
            /\
            -. k = C
          )
        )
        ->
        (
          ( NTP4VCEntry A k l )
          =
          ( NTP4VCEntry B k l )
        )
      ) $.
$}

${
  $d k A B $.

  ntp4vc-row-fun-definition $a |- (
    NTP4VCRowFun A B
  ) = (
    k e. ZZ |->
      ( NTP4VCEntry A B k )
  ) $.
$}

${
  $d j k A B C $.

  ntp4vc-row-sorted-definition $a |- (
    NTP4VCRowSorted A B C
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
          k < ( NTP4VCColumns A )
        )
        ->
        (
          (
            C = 1
            ->
            (
              ( NTP4VCEntry A B j )
              <_
              ( NTP4VCEntry A B k )
            )
          )
          /\
          (
            C = 0
            ->
            (
              ( NTP4VCEntry A B k )
              <_
              ( NTP4VCEntry A B j )
            )
          )
        )
      ) $.
$}

ntp4vc-row-permuted-definition $a |- (
  NTP4VCRowPermuted A B C
) <->
(
  NTP4VCPermut
    ( NTP4VCRowFun A C )
    ( NTP4VCRowFun B C )
    0
    ( NTP4VCColumns A )
) $.

ntp4vc-post-definition $a |- (
  NTP4VCPost A B C D
) <->
(
  ( NTP4VCOtherRows A B C )
  /\
  (
    ( NTP4VCRowSorted A C D )
    /\
    ( NTP4VCRowPermuted A B C )
  )
) $.

${
  $d i j A $.

  ntp4vc-list-sorted-definition $a |- (
    NTP4VCListSorted A
  ) <->
  A. i e. ZZ
    A. j e. ZZ
      (
        (
          (
            0 <_ i
            /\
            i <_ j
          )
          /\
          j < ( # ` A )
        )
        ->
        (
          ( NTP4VCAt A i )
          <_
          ( NTP4VCAt A j )
        )
      ) $.
$}

ntp4vc-list-permuted-definition $a |- (
  NTP4VCListPermuted A B
) <->
(
  NTP4VCPermut
    ( NTP4VCListFun A )
    ( NTP4VCListFun B )
    0
    ( # ` A )
) $.

${
  $d p A B C D $.

  ntp4vc-matrix-update-definition $a |- (
    NTP4VCMatrixUpdate A B C D
  ) = (
    p e. ( ZZ X. ZZ ) |->
      if (
        ( 1st ` p ) = B ,
        if (
          ( 2nd ` p ) = C ,
          D ,
          ( A ` p )
        ) ,
        ( A ` p )
      )
  ) $.
$}

${
  $d j m A B C D E F $.

  ntp4vc-write-iteration-definition $a |- (
    NTP4VCWriteIteration A B C D E F
  ) <->
  A. j e. ZZ
    (
      (
        (
          (
            0 <_ j
            /\
            j <_ E
          )
          /\
          (
            ( NTP4VCPrefix A F C j )
            /\
            ( NTP4VCOtherRows F B C )
          )
        )
        ->
        (
          (
            0 <_ j
            /\
            j < ( # ` A )
          )
          /\
          (
            ( NTP4VCValidIndex F C j )
            /\
            A. m e. NTP4VCMatrix
              (
                (
                  ( NTP4VCSameShape m F )
                  /\
                  (
                    ( NTP4VCElts m )
                    =
                    (
                      NTP4VCMatrixUpdate
                        ( NTP4VCElts F )
                        C
                        j
                        ( NTP4VCAt A j )
                    )
                  )
                )
                ->
                (
                  ( NTP4VCPrefix A m C ( j + 1 ) )
                  /\
                  ( NTP4VCOtherRows m B C )
                )
              )
          )
        )
      )
      /\
      (
        (
          ( NTP4VCPrefix A F C ( E + 1 ) )
          /\
          ( NTP4VCOtherRows F B C )
        )
        ->
        ( NTP4VCPost F B C D )
      )
    ) $.
$}

${
  $d m A B C D $.

  ntp4vc-write-loop-definition $a |- (
    NTP4VCWriteLoop A B C D
  ) <->
  (
    (
      0 <_ ( ( NTP4VCColumns B ) - 1 + 1 )
      ->
      (
        ( NTP4VCPrefix A B C 0 )
        /\
        A. m e. NTP4VCMatrix
          (
            ( NTP4VCSameShape m B )
            ->
            (
              NTP4VCWriteIteration
                A
                B
                C
                D
                ( ( NTP4VCColumns B ) - 1 )
                m
            )
          )
      )
    )
    /\
    (
      ( ( NTP4VCColumns B ) - 1 + 1 ) < 0
      ->
      ( NTP4VCPost B B C D )
    )
  ) $.
$}

${
  $d j A $.

  ntp4vc-reverse-initial-definition $a |- (
    NTP4VCReverseInitial A
  ) <->
  (
    (
      (
        0 <_ 0
        /\
        0 <_ ( ( # ` A ) - 1 + 1 )
      )
      /\
      ( ( # ` A ) - 1 + 1 ) <_ ( # ` A )
    )
    /\
    (
      0 + ( ( # ` A ) - 1 )
      =
      ( ( # ` A ) - 1 )
    )
    /\
    (
      A. j e. ZZ
        (
          (
            (
              0 <_ j
              /\
              j < 0
            )
            \/
            (
              ( ( # ` A ) - 1 ) < j
              /\
              j < ( # ` A )
            )
          )
          ->
          (
            ( NTP4VCAt A j )
            =
            ( NTP4VCAt A ( ( # ` A ) - 1 - j ) )
          )
        )
      /\
      (
        NTP4VCPermut
          ( NTP4VCListFun A )
          ( NTP4VCListFun A )
          0
          ( # ` A )
      )
    )
  ) $.
$}

${
  $d j A B C D $.

  ntp4vc-reverse-invariant-definition $a |- (
    NTP4VCReverseInvariant A B C D
  ) <->
  (
    (
      (
        0 <_ C
        /\
        C <_ ( D + 1 )
      )
      /\
      ( D + 1 ) <_ ( # ` B )
    )
    /\
    (
      C + D
      =
      ( ( # ` B ) - 1 )
    )
    /\
    (
      A. j e. ZZ
        (
          (
            C <_ j
            /\
            j <_ D
          )
          ->
          (
            ( NTP4VCAt B j )
            =
            ( NTP4VCAt A j )
          )
        )
      /\
      (
        A. j e. ZZ
          (
            (
              (
                0 <_ j
                /\
                j < C
              )
              \/
              (
                D < j
                /\
                j < ( # ` B )
              )
            )
            ->
            (
              ( NTP4VCAt B j )
              =
              ( NTP4VCAt A ( ( # ` B ) - 1 - j ) )
            )
          )
        /\
        (
          NTP4VCPermut
            ( NTP4VCListFun A )
            ( NTP4VCListFun B )
            0
            ( # ` B )
        )
      )
    )
  ) $.
$}

${
  $d i A B C D $.

  ntp4vc-swap-effect-definition $a |- (
    NTP4VCSwapEffect A B C D
  ) <->
  (
    (
      (
        0 <_ C
        /\
        C < ( # ` B )
      )
      /\
      (
        0 <_ D
        /\
        D < ( # ` B )
      )
    )
    /\
    (
      A. i e. ZZ
        (
          (
            (
              0 <_ i
              /\
              i <_ ( # ` B )
            )
            /\
            (
              -. i = C
              /\
              -. i = D
            )
          )
          ->
          (
            ( NTP4VCAt B i )
            =
            ( NTP4VCAt A i )
          )
        )
      /\
      (
        ( NTP4VCAt B C ) = ( NTP4VCAt A D )
        /\
        ( NTP4VCAt B D ) = ( NTP4VCAt A C )
      )
    )
  ) $.
$}

ntp4vc-reverse-step-post-definition $a |- (
  NTP4VCReverseStepPost A B C D
) <->
(
  (
    0 <_ ( D - C )
    /\
    ( D - 1 - ( C + 1 ) ) < ( D - C )
  )
  /\
  (
    NTP4VCReverseInvariant
      A
      B
      ( C + 1 )
      ( D - 1 )
  )
) $.

ntp4vc-swap-case-definition $a |- (
  NTP4VCSwapCase A B C D
) <->
(
  (
    0 <_ D
    /\
    D < ( # ` B )
  )
  /\
  (
    (
      0 <_ C
      /\
      C < ( # ` B )
    )
    /\
    (
      0 <_ D
      /\
      D < ( # ` B )
    )
  )
  /\
  (
    (
      ( # ` ( NTP4VCSet B D ( NTP4VCAt B C ) ) )
      =
      ( # ` B )
    )
    ->
    (
      ( NTP4VCListUpdateLaw B D ( NTP4VCAt B C ) )
      ->
      (
        (
          0 <_ C
          /\
          C
          <
          ( # ` ( NTP4VCSet B D ( NTP4VCAt B C ) ) )
        )
        /\
        (
          (
            (
              # `
              (
                NTP4VCSet
                  ( NTP4VCSet B D ( NTP4VCAt B C ) )
                  C
                  ( NTP4VCAt B D )
              )
            )
            =
            ( # ` ( NTP4VCSet B D ( NTP4VCAt B C ) ) )
          )
          ->
          (
            (
              NTP4VCListUpdateLaw
                ( NTP4VCSet B D ( NTP4VCAt B C ) )
                C
                ( NTP4VCAt B D )
            )
            ->
            (
              (
                NTP4VCSwapEffect
                  B
                  (
                    NTP4VCSet
                      ( NTP4VCSet B D ( NTP4VCAt B C ) )
                      C
                      ( NTP4VCAt B D )
                  )
                  C
                  D
              )
              /\
              (
                (
                  NTP4VCPermut
                    (
                      NTP4VCListFun
                      (
                        NTP4VCSet
                          ( NTP4VCSet B D ( NTP4VCAt B C ) )
                          C
                          ( NTP4VCAt B D )
                      )
                    )
                    ( NTP4VCListFun B )
                    0
                    (
                      # `
                      (
                        NTP4VCSet
                          ( NTP4VCSet B D ( NTP4VCAt B C ) )
                          C
                          ( NTP4VCAt B D )
                      )
                    )
                )
                ->
                (
                  NTP4VCReverseStepPost
                    A
                    (
                      NTP4VCSet
                        ( NTP4VCSet B D ( NTP4VCAt B C ) )
                        C
                        ( NTP4VCAt B D )
                    )
                    C
                    D
                )
              )
            )
          )
        )
      )
    )
  )
) $.

${
  $d u v a A B C D $.

  ntp4vc-reverse-loop-definition $a |- (
    NTP4VCReverseLoop A B C D
  ) <->
  (
    ( NTP4VCReverseInitial A )
    /\
    A. v e. ZZ
      A. u e. ZZ
        A. a e. ( Word ZZ )
          (
            (
              ( # ` a ) = ( # ` A )
              /\
              ( NTP4VCReverseInvariant A a u v )
            )
            ->
            (
              (
                u < v
                ->
                ( NTP4VCSwapCase A a u v )
              )
              /\
              (
                -. u < v
                ->
                ( NTP4VCWriteLoop a B C D )
              )
            )
          )
  ) $.
$}

ntp4vc-after-sort-definition $a |- (
  NTP4VCAfterSort A B C D
) <->
(
  (
    D = 0
    ->
    ( NTP4VCReverseLoop A B C D )
  )
  /\
  (
    D = 1
    ->
    ( NTP4VCWriteLoop A B C D )
  )
) $.

${
  $d j a A B C D E $.

  ntp4vc-read-iteration-definition $a |- (
    NTP4VCReadIteration A B C D E
  ) <->
  A. j e. ZZ
    (
      (
        (
          (
            0 <_ j
            /\
            j <_ E
          )
          /\
          ( NTP4VCPrefix A B C j )
        )
        ->
        (
          ( NTP4VCValidIndex B C j )
          /\
          (
            (
              0 <_ j
              /\
              j < ( # ` A )
            )
            /\
            (
              (
                ( # ` ( NTP4VCSet A j ( NTP4VCEntry B C j ) ) )
                =
                ( # ` A )
              )
              ->
              (
                ( NTP4VCListUpdateLaw A j ( NTP4VCEntry B C j ) )
                ->
                (
                  NTP4VCPrefix
                    ( NTP4VCSet A j ( NTP4VCEntry B C j ) )
                    B
                    C
                    ( j + 1 )
                )
              )
            )
          )
        )
      )
      /\
      (
        ( NTP4VCPrefix A B C ( E + 1 ) )
        ->
        A. a e. ( Word ZZ )
          (
            (
              ( # ` a ) = ( # ` A )
              /\
              (
                ( NTP4VCListSorted a )
                /\
                ( NTP4VCListPermuted a A )
              )
            )
            ->
            ( NTP4VCAfterSort a B C D )
          )
      )
    ) $.
$}

${
  $d a A B C D $.

  ntp4vc-read-loop-definition $a |- (
    NTP4VCReadLoop A B C D
  ) <->
  (
    (
      0 <_ ( ( NTP4VCColumns B ) - 1 + 1 )
      ->
      (
        ( NTP4VCPrefix A B C 0 )
        /\
        A. a e. ( Word ZZ )
          (
            ( # ` a ) = ( # ` A )
            ->
            (
              NTP4VCReadIteration
                a
                B
                C
                D
                ( ( NTP4VCColumns B ) - 1 )
            )
          )
      )
    )
    /\
    (
      ( ( NTP4VCColumns B ) - 1 + 1 ) < 0
      ->
      A. a e. ( Word ZZ )
        (
          (
            ( # ` a ) = ( # ` A )
            /\
            (
              ( NTP4VCListSorted a )
              /\
              ( NTP4VCListPermuted a A )
            )
          )
          ->
          ( NTP4VCAfterSort a B C D )
        )
    )
  ) $.
$}

${
  $d i m a A B C $.

  ntp4vc-main-definition $a |- (
    NTP4VCMain A B C
  ) <->
  (
    (
      0 <_ A
      /\
      A < ( NTP4VCRows B )
    )
    ->
    (
      0 <_ ( NTP4VCColumns B )
      /\
      A. a e. ( Word ZZ )
        (
          (
            (
              A. i e. ZZ
                (
                  (
                    0 <_ i
                    /\
                    i < ( NTP4VCColumns B )
                  )
                  ->
                  ( NTP4VCAt a i ) = 0
                )
            )
            /\
            ( # ` a ) = ( NTP4VCColumns B )
          )
          ->
          ( NTP4VCReadLoop a B A C )
        )
    )
  ) $.
$}

ntp4vc-pearl-verifythis-2021-shearsort-sort-row-vc $a |-
  A. i e. ZZ
    A. m e. NTP4VCMatrix
      A. a e. { 0 , 1 }
        ( NTP4VCMain i m a )
$.
