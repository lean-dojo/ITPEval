$(
  Statement-only formalization of the NTP4VC corpus artifact
  pearl/verifythis_2021_shearsort_ShearSort_sort_all_rowsqtvc
  (ntp4vc__metamath__pearl/verifythis_2021_shearsort_ShearSort_sort_all_rowsqtvc):
  the complete verification condition for sorting all rows of an integer
  matrix in alternating ascending and descending order while preserving each
  row's multiset of entries. This file contains no proof.
$)

$[ lib/set.mm $]

$(
  NTP4VCMatrix is exactly the source matrix type: a pair of nonnegative
  integer dimensions together with an arbitrary total function from integer
  index pairs to integers. Thus every source lookup, including an
  out-of-bounds lookup, remains a distinct application on the full integer
  domain.

  NTP4VCNumof counts occurrences on arbitrary finite half-open integer
  intervals, and NTP4VCPermut equates those counts for every integer.
  NTP4VCTDiv2 is signed division by two truncated toward zero, and
  NTP4VCCMod2 is its associated signed remainder. The alternating row-order
  conditional is represented by its equivalent pair of guarded cases.

  The remaining biconditional definitions factor the generated verification
  condition. Expanding them recovers the initial invariants, every integer
  loop-index quantifier, every same-shaped intermediate matrix, the complete
  row-sort contract, invariant preservation, loop exit, and the negative
  range branch. The source let-bound value o1 is replaced only by its defining
  expression rows(m)-1. The Rocq export uses quotient in the parity tests;
  this statement follows the original Why3 source and the agreeing Lean and
  Isabelle exports, which use signed remainder.

  Every $a before the final declaration is syntax or a faithful definition.
  The final $a is Metamath's native unproved statement encoding, and this
  database contains no $p declaration.
$)

$c
  NTP4VCMatrix NTP4VCRows NTP4VCColumns NTP4VCElts NTP4VCEntry
  NTP4VCRow NTP4VCNumof NTP4VCTDiv2 NTP4VCCMod2 NTP4VCPermut
  NTP4VCSameShape NTP4VCRowPermuted NTP4VCPrefixOrdered
  NTP4VCSameExceptRow NTP4VCRowSortedAt NTP4VCSortRowPost
  NTP4VCLoopInvariant NTP4VCLoopStep NTP4VCLoopExit NTP4VCMain
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
ntp4vc-row-syntax
  $a class ( NTP4VCRow A B ) $.
ntp4vc-numof-syntax
  $a class ( NTP4VCNumof A B C D ) $.
ntp4vc-tdiv2-syntax
  $a class ( NTP4VCTDiv2 A ) $.
ntp4vc-cmod2-syntax
  $a class ( NTP4VCCMod2 A ) $.

ntp4vc-permut-syntax
  $a wff ( NTP4VCPermut A B C D ) $.
ntp4vc-same-shape-syntax
  $a wff ( NTP4VCSameShape A B ) $.
ntp4vc-row-permuted-syntax
  $a wff ( NTP4VCRowPermuted A B ) $.
ntp4vc-prefix-ordered-syntax
  $a wff ( NTP4VCPrefixOrdered A B ) $.
ntp4vc-same-except-row-syntax
  $a wff ( NTP4VCSameExceptRow A B C ) $.
ntp4vc-row-sorted-at-syntax
  $a wff ( NTP4VCRowSortedAt A B ) $.
ntp4vc-sort-row-post-syntax
  $a wff ( NTP4VCSortRowPost A B C ) $.
ntp4vc-loop-invariant-syntax
  $a wff ( NTP4VCLoopInvariant A B C D ) $.
ntp4vc-loop-step-syntax
  $a wff ( NTP4VCLoopStep A B C ) $.
ntp4vc-loop-exit-syntax
  $a wff ( NTP4VCLoopExit A B C ) $.
ntp4vc-main-syntax
  $a wff ( NTP4VCMain A ) $.

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

${
  $d j A B $.

  ntp4vc-row-definition $a |- (
    NTP4VCRow A B
  ) = (
    j e. ZZ |->
      ( NTP4VCEntry A B j )
  ) $.
$}

${
  $d i A B C D $.

  ntp4vc-numof-definition $a |- (
    NTP4VCNumof A B C D
  ) = (
    # `
    { i e. ( C ..^ D ) |
      ( A ` i ) = B
    }
  ) $.
$}

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

ntp4vc-same-shape-definition $a |- (
  NTP4VCSameShape A B
) <->
(
  ( NTP4VCRows A ) = ( NTP4VCRows B )
  /\
  ( NTP4VCColumns A ) = ( NTP4VCColumns B )
) $.

${
  $d i A B $.

  ntp4vc-row-permuted-definition $a |- (
    NTP4VCRowPermuted A B
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
        NTP4VCPermut
          ( NTP4VCRow A i )
          ( NTP4VCRow B i )
          0
          ( NTP4VCColumns A )
      )
    ) $.
$}

${
  $d i j k A B $.

  ntp4vc-prefix-ordered-definition $a |- (
    NTP4VCPrefixOrdered A B
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
              k < ( NTP4VCColumns A )
            )
          )
          ->
          (
            (
              ( NTP4VCCMod2 i ) = 0
              ->
              (
                ( NTP4VCEntry A i j )
                <_
                ( NTP4VCEntry A i k )
              )
            )
            /\
            (
              -. ( NTP4VCCMod2 i ) = 0
              ->
              (
                ( NTP4VCEntry A i k )
                <_
                ( NTP4VCEntry A i j )
              )
            )
          )
        ) $.
$}

${
  $d j k A B C $.

  ntp4vc-same-except-row-definition $a |- (
    NTP4VCSameExceptRow A B C
  ) <->
  A. j e. ZZ
    A. k e. ZZ
      (
        (
          (
            (
              0 <_ j
              /\
              j < ( NTP4VCRows A )
            )
            /\
            (
              0 <_ k
              /\
              k < ( NTP4VCColumns A )
            )
          )
          /\
          -. j = C
        )
        ->
        (
          ( NTP4VCEntry A j k )
          =
          ( NTP4VCEntry B j k )
        )
      ) $.
$}

${
  $d j k A B $.

  ntp4vc-row-sorted-at-definition $a |- (
    NTP4VCRowSortedAt A B
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
            ( NTP4VCCMod2 B ) = 0
            ->
            (
              ( NTP4VCEntry A B j )
              <_
              ( NTP4VCEntry A B k )
            )
          )
          /\
          (
            -. ( NTP4VCCMod2 B ) = 0
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

ntp4vc-sort-row-post-definition $a |- (
  NTP4VCSortRowPost A B C
) <->
(
  ( NTP4VCSameExceptRow A B C )
  /\
  (
    ( NTP4VCRowSortedAt A C )
    /\
    (
      NTP4VCPermut
        ( NTP4VCRow A C )
        ( NTP4VCRow B C )
        0
        ( NTP4VCColumns A )
    )
  )
) $.

ntp4vc-loop-invariant-definition $a |- (
  NTP4VCLoopInvariant A B C D
) <->
(
  (
    0 <_ C
    /\
    C <_ D
  )
  /\
  (
    ( NTP4VCRowPermuted B A )
    /\
    ( NTP4VCPrefixOrdered B C )
  )
) $.

${
  $d m A B C $.

  ntp4vc-loop-step-definition $a |- (
    NTP4VCLoopStep A B C
  ) <->
  (
    2 =/= 0
    /\
    (
      (
        0 <_ C
        /\
        C < ( NTP4VCRows B )
      )
      /\
      A. m e. NTP4VCMatrix
        (
          ( NTP4VCSameShape m B )
          ->
          (
            ( NTP4VCSortRowPost m B C )
            ->
            (
              ( NTP4VCRowPermuted m A )
              /\
              ( NTP4VCPrefixOrdered m ( C + 1 ) )
            )
          )
        )
    )
  ) $.
$}

ntp4vc-loop-exit-definition $a |- (
  NTP4VCLoopExit A B C
) <->
(
  (
    ( NTP4VCRowPermuted B A )
    /\
    ( NTP4VCPrefixOrdered B ( C + 1 ) )
  )
  ->
  (
    ( NTP4VCRowPermuted B A )
    /\
    (
      NTP4VCPrefixOrdered
        B
        ( NTP4VCRows B )
    )
  )
) $.

${
  $d i m A $.

  ntp4vc-main-definition $a |- (
    NTP4VCMain A
  ) <->
  (
    (
      0 <_
      (
        ( ( NTP4VCRows A ) - 1 )
        +
        1
      )
      ->
      (
        (
          ( NTP4VCRowPermuted A A )
          /\
          ( NTP4VCPrefixOrdered A 0 )
        )
        /\
        A. m e. NTP4VCMatrix
          (
            ( NTP4VCSameShape m A )
            ->
            (
              A. i e. ZZ
                (
                  (
                    NTP4VCLoopInvariant
                      A
                      m
                      i
                      ( ( NTP4VCRows A ) - 1 )
                  )
                  ->
                  ( NTP4VCLoopStep A m i )
                )
              /\
              (
                NTP4VCLoopExit
                  A
                  m
                  ( ( NTP4VCRows A ) - 1 )
              )
            )
          )
      )
    )
    /\
    (
      (
        (
          ( NTP4VCRows A ) - 1
        )
        +
        1
      )
      <
      0
      ->
      (
        ( NTP4VCRowPermuted A A )
        /\
        (
          NTP4VCPrefixOrdered
            A
            ( NTP4VCRows A )
        )
      )
    )
  ) $.
$}

ntp4vc-pearl-verifythis-2021-shearsort-sort-all-rows-vc $a |-
  A. A e. NTP4VCMatrix
    ( NTP4VCMain A )
$.
