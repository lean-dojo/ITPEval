$(
  Statement-only formalization of the NTP4VC corpus artifact
  pearl/sumrange_CumulativeTree_updateqtvc: the cumulative-tree point-update
  verification condition preserves the tree interval, the updated array cell,
  all other array cells, and the cumulative-tree invariant. This file contains
  no proof.
$)

$[ lib/set.mm $]

$(
  SetMM's ZZ is the full unbounded integer domain, and Word ZZ is exactly the
  type of arbitrary finite zero-based integer sequences. NTP4VCToNat,
  NTP4VCAt, NTP4VCSet, NTP4VCNth, and NTP4VCFunUpdate reproduce Int.toNat,
  totalized list lookup with default zero, List.set, integer-indexed lookup,
  and Function.update. NTP4VCSum is finite summation over a half-open
  interval; under the bounds in is_tree_for it is definitionally equivalent
  to the source ArraySum.sum.

  An indexes record is represented by the full product
  ZZ X. ( ZZ X. ZZ ). NTP4VCLeaf and NTP4VCNode are injective disjoint tagged
  constructors. Constructor closure, exhaustiveness, and structural induction
  make T exactly the source type of finite cumulative trees, without a finite
  approximation or non-well-founded values. NTP4VCIndexes, NTP4VCLow,
  NTP4VCHigh, and NTP4VCISum are the source record projections.

  R represents is_tree_for, and its complete leaf and node equations below are
  the source recursive definition. Why3 computer division by positive 2 is
  represented by the floor of the rational quotient; is_tree_for makes the
  endpoints nonnegative, so this agrees with the source integer division.
  NTP4VCFrame and NTP4VCUpdateLaw are biconditional factorizations of the
  source frame quantifier and the nested list-update implications.

  Expanding all definitions recovers every source tree, finite integer-list,
  and integer domain; all three assumptions; the internal universal scope of
  the updated tree; the original implication nesting; and every conjunct of
  the conclusion. The final declaration is Metamath's native unproved $a
  statement encoding; every preceding $a is syntax or a faithful definition
  required to state it, and this database contains no $p proof declaration.
$)

$c
  NTP4VCLeaf NTP4VCNode NTP4VCIndexes
  NTP4VCLow NTP4VCHigh NTP4VCISum
  NTP4VCToNat NTP4VCAt NTP4VCSet NTP4VCNth NTP4VCFunUpdate NTP4VCSum
  NTP4VCIsIndexes NTP4VCIsTree NTP4VCFrame NTP4VCUpdateLaw
$.

ntp4vc-leaf-syntax
  $a class ( NTP4VCLeaf A ) $.
ntp4vc-node-syntax
  $a class ( NTP4VCNode A B C ) $.
ntp4vc-indexes-syntax
  $a class ( NTP4VCIndexes A ) $.
ntp4vc-low-syntax
  $a class ( NTP4VCLow A ) $.
ntp4vc-high-syntax
  $a class ( NTP4VCHigh A ) $.
ntp4vc-isum-syntax
  $a class ( NTP4VCISum A ) $.
ntp4vc-to-nat-syntax
  $a class ( NTP4VCToNat A ) $.
ntp4vc-at-syntax
  $a class ( NTP4VCAt A B ) $.
ntp4vc-set-syntax
  $a class ( NTP4VCSet A B C ) $.
ntp4vc-nth-syntax
  $a class ( NTP4VCNth A ) $.
ntp4vc-fun-update-syntax
  $a class ( NTP4VCFunUpdate A B C ) $.
ntp4vc-sum-syntax
  $a class ( NTP4VCSum A B C ) $.

ntp4vc-is-indexes-syntax
  $a wff ( NTP4VCIsIndexes A B C D ) $.
ntp4vc-is-tree-syntax
  $a wff ( NTP4VCIsTree A B C D E ) $.
ntp4vc-frame-syntax
  $a wff ( NTP4VCFrame A B C ) $.
ntp4vc-update-law-syntax
  $a wff ( NTP4VCUpdateLaw A B C D E ) $.

ntp4vc-leaf-definition $a |- (
  NTP4VCLeaf A
) = <. 0 , A >. $.

ntp4vc-node-definition $a |- (
  NTP4VCNode A B C
) = <. 1 , <. A , <. B , C >. >. >. $.

ntp4vc-indexes-definition $a |- (
  NTP4VCIndexes A
) = if (
  ( 1st ` A ) = 0 ,
  ( 2nd ` A ) ,
  ( 1st ` ( 2nd ` A ) )
) $.

ntp4vc-low-definition $a |- (
  NTP4VCLow A
) = ( 1st ` A ) $.

ntp4vc-high-definition $a |- (
  NTP4VCHigh A
) = ( 1st ` ( 2nd ` A ) ) $.

ntp4vc-isum-definition $a |- (
  NTP4VCISum A
) = ( 2nd ` ( 2nd ` A ) ) $.

ntp4vc-to-nat-definition $a |- (
  NTP4VCToNat A
) = if (
  0 <_ A ,
  A ,
  0
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

  ntp4vc-nth-definition $a |- (
    NTP4VCNth A
  ) = (
    k e. ZZ |->
      ( NTP4VCAt A k )
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
  $d k A B C $.

  ntp4vc-sum-definition $a |- (
    NTP4VCSum A B C
  ) = sum_ k e.
    (
      ( NTP4VCToNat B )
      ..^
      ( NTP4VCToNat C )
    )
    ( NTP4VCAt A k ) $.
$}

ntp4vc-is-indexes-definition $a |- (
  NTP4VCIsIndexes A B C D
) <->
(
  ( NTP4VCLow A ) = C
  /\
  (
    ( NTP4VCHigh A ) = D
    /\
    (
      (
        0 <_ C
        /\
        (
          C < D
          /\
          D <_ ( # ` B )
        )
      )
      /\
      ( NTP4VCISum A ) = ( NTP4VCSum B C D )
    )
  )
) $.

ntp4vc-is-tree-definition $a |- (
  NTP4VCIsTree A B C D E
) <->
<. B , <. C , <. D , E >. >. >. e. A $.

${
  $d k A B C $.

  ntp4vc-frame-definition $a |- (
    NTP4VCFrame A B C
  ) <->
  A. k e. ZZ
    (
      (
        (
          0 <_ k
          /\
          k < ( # ` A )
        )
        /\
        -. k = C
      )
      ->
      ( NTP4VCAt A k ) = ( NTP4VCAt B k )
    ) $.
$}

ntp4vc-update-law-definition $a |- (
  NTP4VCUpdateLaw A B C D E
) <->
(
  (
    # ` ( NTP4VCSet C D E )
  )
  =
  ( # ` C )
  ->
  (
    (
      NTP4VCNth ( NTP4VCSet C D E )
    )
    =
    (
      NTP4VCFunUpdate
        ( NTP4VCNth C )
        D
        E
    )
    ->
    (
      (
        NTP4VCAt
          ( NTP4VCSet C D E )
          D
      )
      =
      E
      /\
      (
        (
          NTP4VCFrame
            ( NTP4VCSet C D E )
            C
            D
        )
        /\
        (
          NTP4VCIsTree
            A B
            ( NTP4VCSet C D E )
            0
            ( # ` ( NTP4VCSet C D E ) )
        )
      )
    )
  )
) $.

${
  $d a i k l r s t u v
     A B C D E F G H I J K L M N O P Q R S T U V W X Y Z $.

  $( Exact finite source tree carrier over the full indexes record product. $)
  ntp4vc-tree-leaf-closure $e |-
    A. i e. ( ZZ X. ( ZZ X. ZZ ) )
      ( NTP4VCLeaf i ) e. T $.

  ntp4vc-tree-node-closure $e |-
    A. i e. ( ZZ X. ( ZZ X. ZZ ) )
      A. l e. T A. r e. T
        ( NTP4VCNode i l r ) e. T $.

  ntp4vc-tree-constructor-exhaustive $e |- A. t e. T
    (
      E. i e. ( ZZ X. ( ZZ X. ZZ ) )
        t = ( NTP4VCLeaf i )
      \/
      E. i e. ( ZZ X. ( ZZ X. ZZ ) )
        E. l e. T E. r e. T
          t = ( NTP4VCNode i l r )
    ) $.

  ntp4vc-tree-structural-induction $e |- A. s e. ~P T
    (
      (
        A. i e. ( ZZ X. ( ZZ X. ZZ ) )
          ( NTP4VCLeaf i ) e. s
        /\
        A. i e. ( ZZ X. ( ZZ X. ZZ ) )
          A. l e. T A. r e. T
            (
              (
                l e. s
                /\
                r e. s
              )
              ->
              ( NTP4VCNode i l r ) e. s
            )
      )
      ->
      s = T
    ) $.

  $( Complete recursive source definition of is_tree_for. $)
  ntp4vc-is-tree-relation $e |- R C_
    (
      T
      X.
      (
        ( Word ZZ )
        X.
        ( ZZ X. ZZ )
      )
    ) $.

  ntp4vc-is-tree-leaf-equation $e |-
    A. i e. ( ZZ X. ( ZZ X. ZZ ) )
      A. a e. Word ZZ A. j e. ZZ A. k e. ZZ
        (
          NTP4VCIsTree R ( NTP4VCLeaf i ) a j k
          <->
          (
            ( NTP4VCIsIndexes i a j k )
            /\
            k = ( j + 1 )
          )
        ) $.

  ntp4vc-is-tree-node-equation $e |-
    A. i e. ( ZZ X. ( ZZ X. ZZ ) )
      A. l e. T A. r e. T
        A. a e. Word ZZ A. j e. ZZ A. k e. ZZ
          (
            NTP4VCIsTree R ( NTP4VCNode i l r ) a j k
            <->
            (
              ( NTP4VCIsIndexes i a j k )
              /\
              (
                j = ( NTP4VCLow ( NTP4VCIndexes l ) )
                /\
                (
                  k = ( NTP4VCHigh ( NTP4VCIndexes r ) )
                  /\
                  (
                    (
                      NTP4VCHigh ( NTP4VCIndexes l )
                    )
                    =
                    (
                      NTP4VCLow ( NTP4VCIndexes r )
                    )
                    /\
                    (
                      (
                        j < ( NTP4VCHigh ( NTP4VCIndexes l ) )
                        /\
                        ( NTP4VCHigh ( NTP4VCIndexes l ) ) < k
                      )
                      /\
                      (
                        (
                          NTP4VCHigh ( NTP4VCIndexes l )
                        )
                        =
                        (
                          |_ `
                          (
                            ( j + k )
                            /
                            2
                          )
                        )
                        /\
                        (
                          (
                            NTP4VCIsTree
                              R l a j
                              ( NTP4VCHigh ( NTP4VCIndexes l ) )
                          )
                          /\
                          (
                            NTP4VCIsTree
                              R r a
                              ( NTP4VCHigh ( NTP4VCIndexes l ) )
                              k
                          )
                        )
                      )
                    )
                  )
                )
              )
            )
          ) $.

  $( Source theorem parameters A=t, B=a, C=i, and D=v. $)
  ntp4vc-t-tree $e |- A e. T $.
  ntp4vc-a-list $e |- B e. Word ZZ $.
  ntp4vc-i-integer $e |- C e. ZZ $.
  ntp4vc-v-integer $e |- D e. ZZ $.

  $( Source facts fact0 through fact2. $)
  ntp4vc-fact0 $e |- 0 <_ C $.

  ntp4vc-fact1 $e |- C < ( # ` B ) $.

  ntp4vc-fact2 $e |-
    NTP4VCIsTree R A B 0 ( # ` B ) $.

  ntp4vc-pearl-sumrange-cumulative-tree-update-vc $a |- (
    NTP4VCIsTree
      R A B
      ( NTP4VCLow ( NTP4VCIndexes A ) )
      ( NTP4VCHigh ( NTP4VCIndexes A ) )
    /\
    (
      ( NTP4VCLow ( NTP4VCIndexes A ) ) <_ C
      /\
      (
        C < ( NTP4VCHigh ( NTP4VCIndexes A ) )
        /\
        A. u e. T
          (
            (
              ( NTP4VCLow ( NTP4VCIndexes u ) )
              =
              ( NTP4VCLow ( NTP4VCIndexes A ) )
              /\
              (
                ( NTP4VCHigh ( NTP4VCIndexes u ) )
                =
                ( NTP4VCHigh ( NTP4VCIndexes A ) )
                /\
                (
                  NTP4VCIsTree
                    R u
                    ( NTP4VCSet B C D )
                    ( NTP4VCLow ( NTP4VCIndexes u ) )
                    ( NTP4VCHigh ( NTP4VCIndexes u ) )
                )
              )
            )
            ->
            (
              (
                0 <_ C
                /\
                C < ( # ` B )
              )
              /\
              ( NTP4VCUpdateLaw R u B C D )
            )
          )
      )
    )
  ) $.
$}
