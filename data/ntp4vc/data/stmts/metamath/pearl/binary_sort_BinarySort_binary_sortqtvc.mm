$(
  Statement-only formalization of the NTP4VC corpus artifact
  pearl/binary_sort_BinarySort_binary_sortqtvc: the binary insertion-sort
  verification condition states sorted-prefix and permutation invariants,
  binary-search progress, the element-shift update, and the final sorted
  permutation result for an integer list. This file contains no proof.
$)

$[ lib/set.mm $]

$(
  Integer lists are represented exactly by SetMM words over ZZ, hence by
  arbitrary finite zero-based sequences of integers. NTP4VCToNat is the
  source conversion from integers to naturals, NTP4VCAt is the source
  totalized list lookup with integer default 0, and NTP4VCSlice is the source
  drop-then-take slice.

  NTP4VCPerm compares the occurrence count of every integer in two words.
  For finite integer words this is equivalent in both directions to the
  source List.Perm relation. NTP4VCPermutSub is the source permut_sub':
  equal lengths and equal prefix and suffix slices, with a permutation of the
  selected middle slice. NTP4VCSortedSub is the source pairwise ordering
  condition over the indicated half-open integer interval.

  NTP4VCSet is the exact source List.set operation after integer-to-natural
  conversion. NTP4VCUpdateLaw states the source extensional equality between
  lookup after that list update and integer function update on valid array
  indices.
  NTP4VCShiftedCopy expands the two quantified equations describing the
  right shift of a list segment.

  NTP4VCTDiv2 is truncating integer division by the fixed positive divisor 2,
  exactly the pinned Why3 int.ComputerDivision.div operation. Lean Int.tdiv
  and Isabelle cdiv preserve this operation; the secondary Rocq remainder
  rendering does not override the original goal. NTP4VCBinaryStep expands
  the proposition-valued source conditionals as exhaustive guarded
  disjunctions and substitutes all let-bound values. Every integer and list
  quantifier retains its full source domain. The final declaration is
  Metamath's native unproved $a statement encoding; this database contains
  no $p proof declaration.
$)

$c
  NTP4VCToNat NTP4VCNatSub NTP4VCMin
  NTP4VCSliceStart NTP4VCSliceLen NTP4VCSlice
  NTP4VCAt NTP4VCSet NTP4VCPerm NTP4VCPermutSub NTP4VCSortedSub
  NTP4VCTDiv2 NTP4VCMid NTP4VCSearchInvariant
  NTP4VCUpdateLaw NTP4VCShiftedCopy NTP4VCBinaryStep
$.

ntp4vc-to-nat-syntax $a class ( NTP4VCToNat A ) $.
ntp4vc-nat-sub-syntax $a class ( NTP4VCNatSub A B ) $.
ntp4vc-min-syntax $a class ( NTP4VCMin A B ) $.
ntp4vc-slice-start-syntax $a class ( NTP4VCSliceStart A B ) $.
ntp4vc-slice-len-syntax $a class ( NTP4VCSliceLen A B C ) $.
ntp4vc-slice-syntax $a class ( NTP4VCSlice A B C ) $.
ntp4vc-at-syntax $a class ( NTP4VCAt A B ) $.
ntp4vc-set-syntax $a class ( NTP4VCSet A B C ) $.
ntp4vc-perm-syntax $a wff ( NTP4VCPerm A B ) $.
ntp4vc-permut-sub-syntax
  $a wff ( NTP4VCPermutSub A B C D ) $.
ntp4vc-sorted-sub-syntax
  $a wff ( NTP4VCSortedSub A B C ) $.
ntp4vc-tdiv2-syntax $a class ( NTP4VCTDiv2 A ) $.
ntp4vc-mid-syntax $a class ( NTP4VCMid A B ) $.
ntp4vc-search-invariant-syntax
  $a wff ( NTP4VCSearchInvariant A B C D ) $.
ntp4vc-update-law-syntax
  $a wff ( NTP4VCUpdateLaw A B C ) $.
ntp4vc-shifted-copy-syntax
  $a wff ( NTP4VCShiftedCopy A B C D ) $.
ntp4vc-binary-step-syntax
  $a wff ( NTP4VCBinaryStep A B C D E ) $.

ntp4vc-to-nat-definition $a |- (
  NTP4VCToNat A
) = if ( 0 <_ A , A , 0 ) $.

ntp4vc-nat-sub-definition $a |- (
  NTP4VCNatSub A B
) = if ( B <_ A , ( A - B ) , 0 ) $.

ntp4vc-min-definition $a |- (
  NTP4VCMin A B
) = if ( A <_ B , A , B ) $.

ntp4vc-slice-start-definition $a |- (
  NTP4VCSliceStart A B
) = (
  NTP4VCMin ( NTP4VCToNat B ) ( # ` A )
) $.

ntp4vc-slice-len-definition $a |- (
  NTP4VCSliceLen A B C
) = (
  NTP4VCMin
    ( NTP4VCNatSub ( NTP4VCToNat C ) ( NTP4VCToNat B ) )
    ( ( # ` A ) - ( NTP4VCSliceStart A B ) )
) $.

${
  $d k A B C $.

  ntp4vc-slice-definition $a |- (
    NTP4VCSlice A B C
  ) = (
    k e. ( 0 ..^ ( NTP4VCSliceLen A B C ) ) |->
      ( A ` ( ( NTP4VCSliceStart A B ) + k ) )
  ) $.
$}

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
  $d k v A B $.

  ntp4vc-perm-definition $a |- (
    ( NTP4VCPerm A B )
    <->
    (
      (
        A e. Word ZZ
        /\
        B e. Word ZZ
      )
      /\
      (
        ( # ` A ) = ( # ` B )
        /\
        A. v e. ZZ
          (
            (
              # `
              { k e. ( 0 ..^ ( # ` A ) ) | ( A ` k ) = v }
            )
            =
            (
              # `
              { k e. ( 0 ..^ ( # ` B ) ) | ( B ` k ) = v }
            )
          )
      )
    )
  ) $.
$}

ntp4vc-permut-sub-definition $a |- (
  ( NTP4VCPermutSub A B C D )
  <->
  (
    (
      A e. Word ZZ
      /\
      B e. Word ZZ
    )
    /\
    (
      ( # ` A ) = ( # ` B )
      /\
      (
        ( NTP4VCSlice A 0 C ) = ( NTP4VCSlice B 0 C )
        /\
        (
          ( NTP4VCSlice A D ( # ` A ) )
          =
          ( NTP4VCSlice B D ( # ` B ) )
          /\
          (
            NTP4VCPerm
              ( NTP4VCSlice A C D )
              ( NTP4VCSlice B C D )
          )
        )
      )
    )
  )
) $.

${
  $d i j A B C $.

  ntp4vc-sorted-sub-definition $a |- (
    ( NTP4VCSortedSub A B C )
    <->
    (
      A e. Word ZZ
      /\
      (
        B e. ZZ
        /\
        (
          C e. ZZ
          /\
          A. i e. ZZ
            A. j e. ZZ
              (
                (
                  B <_ i
                  /\
                  (
                    i <_ j
                    /\
                    j < C
                  )
                )
                ->
                ( NTP4VCAt A i ) <_ ( NTP4VCAt A j )
              )
        )
      )
    )
  ) $.
$}

ntp4vc-tdiv2-definition $a |- (
  NTP4VCTDiv2 A
) = if (
  A < 0 ,
  ( |^ ` ( A / 2 ) ) ,
  ( |_ ` ( A / 2 ) )
) $.

ntp4vc-mid-definition $a |- (
  NTP4VCMid A B
) = (
  B + ( NTP4VCTDiv2 ( A - B ) )
) $.

${
  $d i A B C D $.

  ntp4vc-search-invariant-definition $a |- (
    ( NTP4VCSearchInvariant A B C D )
    <->
    (
      (
        0 <_ D
        /\
        (
          D <_ C
          /\
          C <_ B
        )
      )
      /\
      (
        A. i e. ZZ
          (
            (
              0 <_ i
              /\
              i < D
            )
            ->
            ( NTP4VCAt A i ) <_ ( NTP4VCAt A B )
          )
        /\
        A. i e. ZZ
          (
            (
              C <_ i
              /\
              i < B
            )
            ->
            ( NTP4VCAt A B ) < ( NTP4VCAt A i )
          )
      )
    )
  ) $.
$}

${
  $d i A B C $.

  ntp4vc-update-law-definition $a |- (
    ( NTP4VCUpdateLaw A B C )
    <->
    A. i e. ZZ
      (
        (
          (
            0 <_ i
            /\
            i < ( # ` A )
          )
          ->
          (
            ( NTP4VCAt ( NTP4VCSet A B C ) i )
            =
            if (
              i = B ,
              C ,
              ( NTP4VCAt A i )
            )
          )
        )
      )
  ) $.
$}

${
  $d i A B C D $.

  ntp4vc-shifted-copy-definition $a |- (
    ( NTP4VCShiftedCopy A B C D )
    <->
    (
      A. i e. ZZ
        (
          (
            (
              0 <_ i
              /\
              i < ( C + 1 )
            )
            \/
            (
              ( ( C + 1 ) + ( D - C ) ) <_ i
              /\
              i < ( # ` A )
            )
          )
          ->
          ( NTP4VCAt A i ) = ( NTP4VCAt B i )
        )
      /\
      A. i e. ZZ
        (
          (
            ( C + 1 ) <_ i
            /\
            i < ( ( C + 1 ) + ( D - C ) )
          )
          ->
          (
            NTP4VCAt A i
          )
          =
          (
            NTP4VCAt B
              ( ( C + i ) - ( C + 1 ) )
          )
        )
    )
  ) $.
$}

${
  $d i j x A B C D E $.

  ntp4vc-binary-step-definition $a |- (
    ( NTP4VCBinaryStep A B C D E )
    <->
    (
      (
        E < D
        /\
        (
          2 =/= 0
          /\
          (
            (
              0 <_ ( NTP4VCMid D E )
              /\
              ( NTP4VCMid D E ) < ( # ` B )
            )
            /\
            (
              (
                (
                  NTP4VCAt B C
                )
                <
                (
                  NTP4VCAt B ( NTP4VCMid D E )
                )
                /\
                (
                  (
                    0 <_ ( D - E )
                    /\
                    (
                      ( NTP4VCMid D E ) - E
                    )
                    <
                    ( D - E )
                  )
                  /\
                  (
                    NTP4VCSearchInvariant
                      B C ( NTP4VCMid D E ) E
                  )
                )
              )
              \/
              (
                -.
                (
                  NTP4VCAt B C
                )
                <
                (
                  NTP4VCAt B ( NTP4VCMid D E )
                )
                /\
                (
                  (
                    0 <_ ( D - E )
                    /\
                    (
                      D - ( ( NTP4VCMid D E ) + 1 )
                    )
                    <
                    ( D - E )
                  )
                  /\
                  (
                    NTP4VCSearchInvariant
                      B C D ( ( NTP4VCMid D E ) + 1 )
                  )
                )
              )
            )
          )
        )
      )
      \/
      (
        -. E < D
        /\
        (
          (
            (
              0 <_ E
              /\
              (
                0 <_ ( C - E )
                /\
                E + ( C - E ) <_ ( # ` B )
              )
            )
            /\
            (
              0 <_ ( E + 1 )
              /\
              ( ( E + 1 ) + ( C - E ) ) <_ ( # ` B )
            )
          )
          /\
          A. x e. Word ZZ
            (
              ( # ` x ) = ( # ` B )
              ->
              (
                ( NTP4VCShiftedCopy x B E C )
                ->
                (
                  (
                    0 <_ E
                    /\
                    E < ( # ` x )
                  )
                  /\
                  (
                    (
                      # ` ( NTP4VCSet x E ( NTP4VCAt B C ) )
                    )
                    =
                    ( # ` x )
                    ->
                    (
                      ( NTP4VCUpdateLaw x E ( NTP4VCAt B C ) )
                      ->
                      (
                        (
                          NTP4VCSortedSub
                            ( NTP4VCSet x E ( NTP4VCAt B C ) )
                            0
                            ( C + 1 )
                        )
                        /\
                        (
                          NTP4VCPermutSub
                            A
                            ( NTP4VCSet x E ( NTP4VCAt B C ) )
                            0
                            (
                              # `
                              ( NTP4VCSet x E ( NTP4VCAt B C ) )
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
  $d i j k x A $.

  $( Source parameter A=a. The source let-bound o1 is expanded as
     (# ` A) - 1; the let-bound v, mid, o2, and o3 values are expanded in the
     helper definitions above. $)

  ntp4vc-a-list $e |- A e. Word ZZ $.

  ntp4vc-pearl-binary-sort-vc $a |- (
    (
      1 <_ ( ( ( # ` A ) - 1 ) + 1 )
      ->
      (
        (
          (
            NTP4VCSortedSub A 0 1
          )
          /\
          (
            NTP4VCPermutSub A A 0 ( # ` A )
          )
        )
        /\
        A. x e. Word ZZ
          (
            ( # ` x ) = ( # ` A )
            ->
            (
              (
                A. k e. ZZ
                  (
                    (
                      (
                        1 <_ k
                        /\
                        k <_ ( ( # ` A ) - 1 )
                      )
                      /\
                      (
                        ( NTP4VCSortedSub x 0 k )
                        /\
                        (
                          NTP4VCPermutSub A x 0 ( # ` x )
                        )
                      )
                    )
                    ->
                    (
                      (
                        0 <_ k
                        /\
                        k < ( # ` x )
                      )
                      /\
                      (
                        (
                          (
                            0 <_ 0
                            /\
                            (
                              0 <_ k
                              /\
                              k <_ k
                            )
                          )
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
                                  NTP4VCAt x i
                                )
                                <_
                                (
                                  NTP4VCAt x k
                                )
                              )
                            /\
                            A. i e. ZZ
                              (
                                (
                                  k <_ i
                                  /\
                                  i < k
                                )
                                ->
                                (
                                  NTP4VCAt x k
                                )
                                <
                                (
                                  NTP4VCAt x i
                                )
                              )
                          )
                        )
                        /\
                        A. j e. ZZ
                          A. i e. ZZ
                            (
                              ( NTP4VCSearchInvariant x k j i )
                              ->
                              ( NTP4VCBinaryStep A x k j i )
                            )
                      )
                    )
                  )
                /\
                (
                  (
                    ( NTP4VCSortedSub x 0 ( ( ( # ` A ) - 1 ) + 1 ) )
                    /\
                    (
                      NTP4VCPermutSub A x 0 ( # ` x )
                    )
                  )
                  ->
                  (
                    ( NTP4VCSortedSub x 0 ( # ` x ) )
                    /\
                    (
                      NTP4VCPermutSub A x 0 ( # ` x )
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
      ( ( ( # ` A ) - 1 ) + 1 ) < 1
      ->
      (
        ( NTP4VCSortedSub A 0 ( # ` A ) )
        /\
        (
          NTP4VCPermutSub A A 0 ( # ` A )
        )
      )
    )
  ) $.
$}
