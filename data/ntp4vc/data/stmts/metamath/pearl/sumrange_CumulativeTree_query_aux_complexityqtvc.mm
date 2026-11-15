$(
  Statement-only formalization of the NTP4VC corpus artifact
  pearl/sumrange_CumulativeTree_query_aux_complexityqtvc: the cumulative-tree
  range-query verification condition preserves subtree range-sum
  specifications while bounding the instrumented query cost by the tree
  depth across exact-match, one-subtree, and split-query branches. This file
  contains no proof.
$)

$[ lib/set.mm $]

$(
  SetMM's ZZ is the full unbounded integer domain, and Word ZZ is exactly the
  type of arbitrary finite zero-based integer sequences. NTP4VCToNat,
  NTP4VCAt, and NTP4VCSum reproduce Int.toNat, totalized list lookup with
  default zero, and the finite sum over a half-open interval. Every sum use in
  this VC is under the source bounds, where this is definitionally equivalent
  to ArraySum.sum.

  An indexes record is represented by the full product
  ZZ X. ( ZZ X. ZZ ). NTP4VCLeaf and NTP4VCNode are injective disjoint tagged
  constructors. Constructor closure, exhaustiveness, and structural induction
  make T exactly the source type of finite cumulative trees, without a finite
  approximation or extraneous non-well-founded values. NTP4VCIndexes,
  NTP4VCLow, NTP4VCHigh, and NTP4VCISum are the source record projections.

  R and D represent is_tree_for and depth. Their complete leaf and node
  equations below are the source recursive definitions. Why3 computer
  division by the positive integer 2 is represented by the floor of the
  rational quotient. NTP4VCChild expands the repeated source match testing
  whether a tree is an immediate child. NTP4VCBound, NTP4VCReady,
  NTP4VCSingleContinuation, NTP4VCNodeElse, and NTP4VCNodeConclusion are
  biconditional or equality factorizations of the source cost bound,
  recursive-call preconditions, continuation implications, nested branch
  conditional, and node branch.

  The Boolean quantifier ranges over exactly { 0, 1 }, with false encoded by
  0 and true by 1. Proposition-valued conditionals are represented by
  their equivalent guarded true and false implications. Expanding all
  definitions recovers every source tree, list, integer, and Boolean domain;
  every assumption; the original universal scopes of c1 and c2; and the full
  leaf and node conclusions. The final declaration is Metamath's native
  unproved $a statement encoding; every preceding $a is syntax or a faithful
  definition required to state it, and this database contains no $p proof
  declaration.
$)

$c
  NTP4VCLeaf NTP4VCNode NTP4VCIndexes
  NTP4VCLow NTP4VCHigh NTP4VCISum NTP4VCMax
  NTP4VCToNat NTP4VCAt NTP4VCSum
  NTP4VCIsIndexes NTP4VCIsTree NTP4VCChild
  NTP4VCBound NTP4VCReady NTP4VCSingleContinuation
  NTP4VCDirect NTP4VCNodeElse NTP4VCNodeConclusion
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
ntp4vc-max-syntax
  $a class ( NTP4VCMax A B ) $.
ntp4vc-to-nat-syntax
  $a class ( NTP4VCToNat A ) $.
ntp4vc-at-syntax
  $a class ( NTP4VCAt A B ) $.
ntp4vc-sum-syntax
  $a class ( NTP4VCSum A B C ) $.

ntp4vc-is-indexes-syntax
  $a wff ( NTP4VCIsIndexes A B C D ) $.
ntp4vc-is-tree-syntax
  $a wff ( NTP4VCIsTree A B C D E ) $.
ntp4vc-child-syntax
  $a wff ( NTP4VCChild A B ) $.
ntp4vc-bound-syntax
  $a class ( NTP4VCBound A B C D ) $.
ntp4vc-ready-syntax
  $a wff ( NTP4VCReady A B C D E F ) $.
ntp4vc-single-continuation-syntax
  $a wff ( NTP4VCSingleContinuation A B C D E F ) $.
ntp4vc-direct-syntax
  $a wff ( NTP4VCDirect A B C D E F G ) $.
ntp4vc-node-else-syntax
  $a wff ( NTP4VCNodeElse A B C D E F G H I ) $.
ntp4vc-node-conclusion-syntax
  $a wff ( NTP4VCNodeConclusion A B C D E F G H I J ) $.

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

ntp4vc-max-definition $a |- (
  NTP4VCMax A B
) = if (
  A <_ B ,
  B ,
  A
) $.

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
  $d i l r A B $.

  ntp4vc-child-definition $a |- (
    NTP4VCChild A B
  ) <->
  E. i e. ( ZZ X. ( ZZ X. ZZ ) )
    E. l e. _V E. r e. _V
      (
        A = ( NTP4VCNode i l r )
        /\
        (
          l = B
          \/
          r = B
        )
      ) $.
$}

ntp4vc-bound-definition $a |- (
  NTP4VCBound A B C D
) = if (
  (
    C = ( NTP4VCLow ( NTP4VCIndexes B ) )
    /\
    D = ( NTP4VCHigh ( NTP4VCIndexes B ) )
  ) ,
  1 ,
  if (
    (
      C = ( NTP4VCLow ( NTP4VCIndexes B ) )
      \/
      D = ( NTP4VCHigh ( NTP4VCIndexes B ) )
    ) ,
    ( 2 x. ( A ` B ) ) ,
    ( 4 x. ( A ` B ) )
  )
) $.

ntp4vc-ready-definition $a |- (
  NTP4VCReady A B C D E F
) <->
(
  ( NTP4VCChild B C )
  /\
  (
    (
      NTP4VCIsTree
        A C D
        ( NTP4VCLow ( NTP4VCIndexes C ) )
        ( NTP4VCHigh ( NTP4VCIndexes C ) )
    )
    /\
    (
      0 <_ ( NTP4VCLow ( NTP4VCIndexes C ) )
      /\
      (
        ( NTP4VCLow ( NTP4VCIndexes C ) ) <_ E
        /\
        (
          E < F
          /\
          (
            F <_ ( NTP4VCHigh ( NTP4VCIndexes C ) )
            /\
            ( NTP4VCHigh ( NTP4VCIndexes C ) ) <_ ( # ` D )
          )
        )
      )
    )
  )
) $.

${
  $d q A B C D E F $.

  ntp4vc-single-continuation-definition $a |- (
    NTP4VCSingleContinuation A B C D E F
  ) <->
  A. q e. ZZ
    (
      (
        q - ( F + 1 )
      )
      <_
      ( NTP4VCBound A B D E )
      ->
      (
        q - F
      )
      <_
      ( NTP4VCBound A C D E )
    ) $.
$}

ntp4vc-direct-definition $a |- (
  NTP4VCDirect A B C D E F G
) <->
(
  (
    ( F + 1 ) - F
  )
  <_
  ( NTP4VCBound A B D E )
  /\
  ( NTP4VCISum G ) = ( NTP4VCSum C D E )
) $.

${
  $d q s A B C D E F G H I $.

  ntp4vc-node-else-definition $a |- (
    NTP4VCNodeElse A B C D E F G H I
  ) <->
  (
    (
      F <_ ( NTP4VCHigh ( NTP4VCIndexes H ) )
      ->
      (
        ( NTP4VCReady A C H D E F )
        /\
        ( NTP4VCSingleContinuation B H C E F G )
      )
    )
    /\
    (
      -.
      F <_ ( NTP4VCHigh ( NTP4VCIndexes H ) )
      ->
      (
        (
          ( NTP4VCHigh ( NTP4VCIndexes H ) ) <_ E
          ->
          (
            ( NTP4VCReady A C I D E F )
            /\
            ( NTP4VCSingleContinuation B I C E F G )
          )
        )
        /\
        (
          -.
          ( NTP4VCHigh ( NTP4VCIndexes H ) ) <_ E
          ->
          (
            (
              NTP4VCReady
                A C I D
                ( NTP4VCHigh ( NTP4VCIndexes H ) )
                F
            )
            /\
            A. q e. ZZ
              (
                (
                  q - ( G + 1 )
                )
                <_
                (
                  NTP4VCBound
                    B I
                    ( NTP4VCHigh ( NTP4VCIndexes H ) )
                    F
                )
                ->
                (
                  (
                    NTP4VCReady
                      A C H D E
                      ( NTP4VCHigh ( NTP4VCIndexes H ) )
                  )
                  /\
                  A. s e. ZZ
                    (
                      ( s - q )
                      <_
                      (
                        NTP4VCBound
                          B H E
                          ( NTP4VCHigh ( NTP4VCIndexes H ) )
                      )
                      ->
                      (
                        ( s - G )
                        <_
                        ( NTP4VCBound B C E F )
                        /\
                        (
                          (
                            NTP4VCSum
                              D E
                              ( NTP4VCHigh ( NTP4VCIndexes H ) )
                          )
                          +
                          (
                            NTP4VCSum
                              D
                              ( NTP4VCHigh ( NTP4VCIndexes H ) )
                              F
                          )
                        )
                        =
                        ( NTP4VCSum D E F )
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
  $d o A B C D E F G H I J $.

  ntp4vc-node-conclusion-definition $a |- (
    NTP4VCNodeConclusion A B C D E F G H I J
  ) <->
  A. o e. { 0 , 1 }
    (
      o = if (
        E = ( NTP4VCLow H ) ,
        if (
          F = ( NTP4VCHigh H ) ,
          1 ,
          0
        ) ,
        0
      )
      ->
      (
        (
          o = 1
          ->
          ( NTP4VCDirect B C D E F G H )
        )
        /\
        (
          -. o = 1
          ->
          (
            NTP4VCNodeElse
              A B C D E F G I J
          )
        )
      )
    ) $.
$}

${
  $d a c i j l o q r s t
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

  $( Complete recursive source definitions of is_tree_for and depth. $)
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

  ntp4vc-depth-function $e |- D e. ( ZZ ^m T ) $.

  ntp4vc-depth-leaf-equation $e |-
    A. i e. ( ZZ X. ( ZZ X. ZZ ) )
      ( D ` ( NTP4VCLeaf i ) ) = 1 $.

  ntp4vc-depth-node-equation $e |-
    A. i e. ( ZZ X. ( ZZ X. ZZ ) )
      A. l e. T A. r e. T
        (
          D ` ( NTP4VCNode i l r )
        )
        =
        (
          1
          +
          (
            NTP4VCMax
              ( D ` l )
              ( D ` r )
          )
        ) $.

  $( Source theorem parameters t, a, i, j, and c. $)
  ntp4vc-t-tree $e |- A e. T $.
  ntp4vc-a-list $e |- B e. Word ZZ $.
  ntp4vc-i-integer $e |- C e. ZZ $.
  ntp4vc-j-integer $e |- E e. ZZ $.
  ntp4vc-c-integer $e |- F e. ZZ $.

  $( Source facts fact0 through fact5. $)
  ntp4vc-fact0 $e |- (
    NTP4VCIsTree
      R A B
      ( NTP4VCLow ( NTP4VCIndexes A ) )
      ( NTP4VCHigh ( NTP4VCIndexes A ) )
  ) $.

  ntp4vc-fact1 $e |-
    0 <_ ( NTP4VCLow ( NTP4VCIndexes A ) ) $.

  ntp4vc-fact2 $e |-
    ( NTP4VCLow ( NTP4VCIndexes A ) ) <_ C $.

  ntp4vc-fact3 $e |- C < E $.

  ntp4vc-fact4 $e |-
    E <_ ( NTP4VCHigh ( NTP4VCIndexes A ) ) $.

  ntp4vc-fact5 $e |-
    ( NTP4VCHigh ( NTP4VCIndexes A ) ) <_ ( # ` B ) $.

  ntp4vc-pearl-sumrange-cumulative-tree-query-aux-complexity-vc $a |- (
    E. i e. ( ZZ X. ( ZZ X. ZZ ) )
      (
        A = ( NTP4VCLeaf i )
        /\
        ( NTP4VCDirect D A B C E F i )
      )
    \/
    E. i e. ( ZZ X. ( ZZ X. ZZ ) )
      E. l e. T E. r e. T
        (
          A = ( NTP4VCNode i l r )
          /\
          (
            NTP4VCNodeConclusion
              R D A B C E F i l r
          )
        )
  ) $.
$}
