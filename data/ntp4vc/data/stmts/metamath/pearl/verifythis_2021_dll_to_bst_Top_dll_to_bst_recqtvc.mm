$(
  Statement-only formalization of the NTP4VC corpus artifact
  pearl/verifythis_2021_dll_to_bst_Top_dll_to_bst_recqtvc
  (ntp4vc__metamath__pearl/verifythis_2021_dll_to_bst_Top_dll_to_bst_recqtvc):
  the recursive doubly-linked-list-to-binary-search-tree verification
  condition states the exact recursive-call, finite-map update, framing,
  tree-shape, and powers-of-two height obligations over an arbitrary location
  carrier. This file contains no proof.
$)

$[ lib/set.mm $]

$(
  U is the arbitrary inhabited location carrier. NTP4VCFMap U is exactly the
  set of finite partial functions from U to U. W is the abstract source
  implementation type t loc, and F is the arbitrary source projection
  to_fmap from W to those finite maps; it is not replaced by the maps
  themselves. G is the shared inhabitant used by the exported totalized list
  and finite-map lookups, and E is the distinguished null location.

  SetMM Word U is exactly the type of arbitrary finite zero-based U-lists.
  T is exactly the source inductive carrier of finite integer-labelled binary
  trees: NTP4VCEmpty and NTP4VCNode are disjoint injective tagged
  constructors, while closure, exhaustiveness, and structural induction
  exclude missing finite trees and extraneous values. R is the complete
  recursive source tree relation, and K is the complete recursive source
  height function.

  NTP4VCValid and NTP4VCDll reproduce the source definitions.
  NTP4VCMapUpdate is finite-map insertion, NTP4VCTDiv2 is integer division by
  two truncated toward zero, and NTP4VCFrame retains both source frame
  intervals. NTP4VCRecPost is the full recursive-call postcondition.

  The remaining predicates only factor the generated weakest-precondition
  formula. They preserve, in order, both recursive calls, all universally
  quantified returned implementations and values, both map updates, all
  domain and frame conditions, the final Node tree, and every guarded height
  bound. Source let-bindings are substituted definitionally. The lookup
  equality immediately following the second-call head binding is eliminated
  only after retaining its domain-membership premise, under which the
  exported total lookup and option lookup are identical.

  The original Why3 source uses truncating div for nl. The official Rocq
  export's use of remainder at that one position is a secondary-export defect
  and does not override the pinned source or the agreeing Lean and Isabelle
  exports. The final $a declaration is Metamath's native unproved statement
  encoding; every preceding $a is syntax or a faithful definition, and this
  database contains no $p declaration.
$)

$c
  NTP4VCFMap NTP4VCToNat NTP4VCAt NTP4VCLookup NTP4VCMapUpdate
  NTP4VCEmpty NTP4VCNode NTP4VCMax NTP4VCTDiv2
  NTP4VCPow2 NTP4VCHeightBound
  NTP4VCValid NTP4VCDll NTP4VCTree NTP4VCFrame NTP4VCEndpoint
  NTP4VCRecPost NTP4VCBase NTP4VCFinal NTP4VCSecond
  NTP4VCAfterLeft NTP4VCRecursive NTP4VCRecVC
$.

ntp4vc-fmap-syntax
  $a class ( NTP4VCFMap A ) $.
ntp4vc-to-nat-syntax
  $a class ( NTP4VCToNat A ) $.
ntp4vc-at-syntax
  $a class ( NTP4VCAt A B C ) $.
ntp4vc-lookup-syntax
  $a class ( NTP4VCLookup A B C ) $.
ntp4vc-map-update-syntax
  $a class ( NTP4VCMapUpdate A B C ) $.
ntp4vc-empty-syntax
  $a class NTP4VCEmpty $.
ntp4vc-node-syntax
  $a class ( NTP4VCNode A B C ) $.
ntp4vc-max-syntax
  $a class ( NTP4VCMax A B ) $.
ntp4vc-tdiv2-syntax
  $a class ( NTP4VCTDiv2 A ) $.
ntp4vc-pow2-syntax
  $a class ( NTP4VCPow2 A ) $.
ntp4vc-height-bound-syntax
  $a wff ( NTP4VCHeightBound A B ) $.
ntp4vc-valid-syntax
  $a wff ( NTP4VCValid A B C D E ) $.
ntp4vc-dll-syntax
  $a wff ( NTP4VCDll A B C D E F G H ) $.
ntp4vc-tree-syntax
  $a wff ( NTP4VCTree A B C D E F G H ) $.
ntp4vc-frame-syntax
  $a wff ( NTP4VCFrame A B C D E F ) $.
ntp4vc-endpoint-syntax
  $a class ( NTP4VCEndpoint A B C D ) $.
ntp4vc-rec-post-syntax
  $a wff (
    NTP4VCRecPost A B C D E F G H I J K L M
  ) $.
ntp4vc-base-syntax
  $a wff (
    NTP4VCBase A B C D E F G H I J K
  ) $.
ntp4vc-final-syntax
  $a wff (
    NTP4VCFinal A B C D E F G H I J K L M N O
  ) $.
ntp4vc-second-syntax
  $a wff (
    NTP4VCSecond A B C D E F G H I J K L M N O P Q
  ) $.
ntp4vc-after-left-syntax
  $a wff (
    NTP4VCAfterLeft A B C D E F G H I J K L M N O P Q R
  ) $.
ntp4vc-recursive-syntax
  $a wff (
    NTP4VCRecursive A B C D E F G H I J K L M N
  ) $.
ntp4vc-rec-vc-syntax
  $a wff (
    NTP4VCRecVC A B C D E F G H I J K L M N
  ) $.

${
  $d f A $.
  ntp4vc-fmap-definition $a |- (
    NTP4VCFMap A
  ) = {
    f e. _V |
      (
        Fun f
        /\
        (
          (
            dom f e. Fin
            /\
            dom f C_ A
          )
          /\
          ran f C_ A
        )
      )
  } $.
$}

ntp4vc-to-nat-definition $a |- (
  NTP4VCToNat A
) = if (
  0 <_ A ,
  A ,
  0
) $.

ntp4vc-at-definition $a |- (
  NTP4VCAt A B C
) = if (
  ( NTP4VCToNat B ) < ( # ` A ) ,
  ( A ` ( NTP4VCToNat B ) ) ,
  C
) $.

ntp4vc-lookup-definition $a |- (
  NTP4VCLookup A B C
) = if (
  B e. dom A ,
  ( A ` B ) ,
  C
) $.

${
  $d k A B C $.
  ntp4vc-map-update-definition $a |- (
    NTP4VCMapUpdate A B C
  ) = (
    k e. ( dom A u. { B } ) |->
      if (
        k = B ,
        C ,
        ( A ` k )
      )
  ) $.
$}

ntp4vc-empty-definition $a |- (
  NTP4VCEmpty
) = <. 0 , (/) >. $.

ntp4vc-node-definition $a |- (
  NTP4VCNode A B C
) = <. 1 , <. A , <. B , C >. >. >. $.

ntp4vc-max-definition $a |- (
  NTP4VCMax A B
) = if (
  A <_ B ,
  B ,
  A
) $.

ntp4vc-tdiv2-definition $a |- (
  NTP4VCTDiv2 A
) = if (
  A < 0 ,
  ( |^ ` ( A / 2 ) ) ,
  ( |_ ` ( A / 2 ) )
) $.

ntp4vc-pow2-definition $a |- (
  NTP4VCPow2 A
) = (
  2 ^ ( NTP4VCToNat A )
) $.

ntp4vc-height-bound-definition $a |- (
  ( NTP4VCHeightBound A B )
  <->
  (
    0 < A
    ->
    (
      ( NTP4VCPow2 ( B - 1 ) ) <_ A
      /\
      A < ( NTP4VCPow2 B )
    )
  )
) $.

${
  $d i j A B C D E $.

  ntp4vc-valid-definition $a |- (
    NTP4VCValid A B C D E
  ) <->
  A. i e. ZZ
    (
      (
        0 <_ i
        /\
        i < ( # ` C )
      )
      ->
      (
        (
          ( NTP4VCAt C i D ) =/= E
          /\
          ( NTP4VCAt C i D ) e. dom A
        )
        /\
        (
          ( NTP4VCAt C i D ) e. dom B
          /\
          A. j e. ZZ
            (
              (
                i < j
                /\
                j < ( # ` C )
              )
              ->
              ( NTP4VCAt C i D ) =/= ( NTP4VCAt C j D )
            )
        )
      )
    ) $.
$}

${
  $d i A B C D E F G H $.

  ntp4vc-dll-definition $a |- (
    NTP4VCDll A B C D E F G H
  ) <->
  (
    (
      NTP4VCValid A B C G H
      /\
      (
        0 <_ E
        /\
        (
          E <_ F
          /\
          F <_ ( # ` C )
        )
      )
    )
    /\
    (
      D
      =
      if (
        E = ( # ` C ) ,
        H ,
        ( NTP4VCAt C E G )
      )
      /\
      (
        A. i e. ZZ
          (
            (
              E <_ i
              /\
              i < ( F - 1 )
            )
            ->
            (
              NTP4VCLookup
                B
                ( NTP4VCAt C i G )
                G
            )
            =
            ( NTP4VCAt C ( i + 1 ) G )
          )
        /\
        (
          A. i e. ZZ
            (
              (
                E < i
                /\
                i < F
              )
              ->
              (
                NTP4VCLookup
                  A
                  ( NTP4VCAt C i G )
                  G
              )
              =
              ( NTP4VCAt C ( i - 1 ) G )
            )
          /\
          (
            (
              E < F
              ->
              (
                NTP4VCLookup
                  B
                  ( NTP4VCAt C ( F - 1 ) G )
                  G
              )
              =
              if (
                F = ( # ` C ) ,
                H ,
                ( NTP4VCAt C F G )
              )
            )
            /\
            (
              E < F
              ->
              (
                NTP4VCLookup
                  A
                  ( NTP4VCAt C E G )
                  G
              )
              =
              if (
                E = 0 ,
                H ,
                ( NTP4VCAt C ( E - 1 ) G )
              )
            )
          )
        )
      )
    )
  ) $.
$}

ntp4vc-tree-definition $a |- (
  ( NTP4VCTree A B C D E F G H )
  <->
  <. B , <. C , <. D , <. E , <. F , <. G , H >. >. >. >. >. >.
    e. A
) $.

${
  $d i A B C D E F $.

  ntp4vc-frame-definition $a |- (
    NTP4VCFrame A B C D E F
  ) <->
  (
    A. i e. ZZ
      (
        (
          0 <_ i
          /\
          i < D
        )
        ->
        (
          NTP4VCLookup
            A
            ( NTP4VCAt C i F )
            F
        )
        =
        (
          NTP4VCLookup
            B
            ( NTP4VCAt C i F )
            F
        )
      )
    /\
    A. i e. ZZ
      (
        (
          E <_ i
          /\
          i < ( # ` C )
        )
        ->
        (
          NTP4VCLookup
            A
            ( NTP4VCAt C i F )
            F
        )
        =
        (
          NTP4VCLookup
            B
            ( NTP4VCAt C i F )
            F
        )
      )
  ) $.
$}

ntp4vc-endpoint-definition $a |- (
  NTP4VCEndpoint A B C D
) = if (
  B = ( # ` A ) ,
  D ,
  ( NTP4VCAt A B C )
) $.

ntp4vc-rec-post-definition $a |- (
  NTP4VCRecPost A B C D E F G H I J K L M
) <->
(
  (
    NTP4VCTree
      A
      ( B ` F )
      ( B ` G )
      E
      H
      I
      J
      ( J + K )
    /\
    dom ( B ` F ) = dom ( B ` C )
  )
  /\
  (
    (
      dom ( B ` G ) = dom ( B ` D )
      /\
      (
        NTP4VCFrame
          ( B ` F )
          ( B ` C )
          E
          J
          ( J + K )
          L
        /\
        NTP4VCFrame
          ( B ` G )
          ( B ` D )
          E
          J
          ( J + K )
          L
      )
    )
    /\
    NTP4VCHeightBound K ( M ` I )
  )
) $.

ntp4vc-base-definition $a |- (
  NTP4VCBase A B C D E F G H I J K
) <->
(
  F = ( NTP4VCEndpoint E ( G + H ) I J )
  /\
  (
    NTP4VCTree
      A
      ( B ` C )
      ( B ` D )
      E
      J
      NTP4VCEmpty
      G
      ( G + H )
    /\
    (
      dom ( B ` C ) = dom ( B ` C )
      /\
      (
        dom ( B ` D ) = dom ( B ` D )
        /\
        NTP4VCHeightBound H ( K ` NTP4VCEmpty )
      )
    )
  )
) $.

ntp4vc-final-definition $a |- (
  NTP4VCFinal A B C D E F G H I J K L M N O
) <->
(
  (
    NTP4VCEndpoint
      E
      ( ( ( J + L ) + 1 ) + ( ( K - L ) - 1 ) )
      M
      N
  )
  =
  ( NTP4VCEndpoint E ( J + K ) M N )
  /\
  NTP4VCRecPost
    A B C D E F G
    ( NTP4VCEndpoint E ( J + L ) M N )
    ( NTP4VCNode H ( J + L ) I )
    J K M O
) $.

${
  $d o p q r t A B C D E F G H I J K L M N O P Q $.

  ntp4vc-second-definition $a |- (
    NTP4VCSecond A B C D E F G H I J K L M N O P Q
  ) <->
  (
    ( NTP4VCEndpoint E ( I + K ) L M ) e. dom ( B ` G )
    /\
    (
      (
        (
          0 <_ J
          /\
          ( ( J - K ) - 1 ) < J
        )
        /\
        NTP4VCDll
          ( B ` F )
          ( B ` G )
          E
          (
            NTP4VCLookup
              ( B ` G )
              ( NTP4VCEndpoint E ( I + K ) L M )
              L
          )
          ( ( I + K ) + 1 )
          (
            ( ( I + K ) + 1 )
            +
            ( ( J - K ) - 1 )
          )
          L
          M
      )
      /\
      A. q e. O
        A. p e. O
          A. o e. Q
            A. r e. P
              (
                NTP4VCRecPost
                  A B F G E p q o r
                  ( ( I + K ) + 1 )
                  ( ( J - K ) - 1 )
                  L N
                ->
                (
                  (
                    NTP4VCEndpoint E ( I + K ) L M
                  ) e. dom ( B ` q )
                  /\
                  A. t e. O
                    (
                      ( B ` t )
                      =
                      (
                        NTP4VCMapUpdate
                          ( B ` q )
                          ( NTP4VCEndpoint E ( I + K ) L M )
                          o
                      )
                      ->
                      NTP4VCFinal
                        A B C D E p t H r I J K L M N
                    )
                )
              )
    )
  ) $.
$}

${
  $d p A B C D E F G H I J K L M N O P Q R $.

  ntp4vc-after-left-definition $a |- (
    NTP4VCAfterLeft A B C D E F G H I J K L M N O P Q R
  ) <->
  (
    ( NTP4VCEndpoint E ( J + L ) M N ) e. dom ( B ` F )
    /\
    A. p e. P
      (
        ( B ` p )
        =
        (
          NTP4VCMapUpdate
            ( B ` F )
            ( NTP4VCEndpoint E ( J + L ) M N )
            H
        )
        ->
        NTP4VCSecond
          A B C D E p G I J K L M N O P Q R
      )
  ) $.
$}

${
  $d o p q r A B C D E F G H I J K L M N $.

  ntp4vc-recursive-definition $a |- (
    NTP4VCRecursive A B C D E F G H I J K L M N
  ) <->
  (
    2 =/= 0
    /\
    (
      (
        (
          0 <_ H
          /\
          ( NTP4VCTDiv2 H ) < H
        )
        /\
        NTP4VCDll
          ( B ` C )
          ( B ` D )
          E
          F
          G
          ( G + ( NTP4VCTDiv2 H ) )
          I
          J
      )
      /\
      A. q e. L
        A. p e. L
          A. o e. N
            A. r e. M
              (
                NTP4VCRecPost
                  A B C D E p q o r
                  G
                  ( NTP4VCTDiv2 H )
                  I
                  K
                ->
                NTP4VCAfterLeft
                  A B C D E p q o r G H
                  ( NTP4VCTDiv2 H )
                  I J K L M N
              )
    )
  ) $.
$}

ntp4vc-rec-vc-definition $a |- (
  NTP4VCRecVC A B C D E F G H I J K L M N
) <->
(
  (
    H = 0
    /\
    NTP4VCBase A B C D E F G H I J K
  )
  \/
  (
    H =/= 0
    /\
    NTP4VCRecursive A B C D E F G H I J K L M N
  )
) $.

${
  $d
    a b f i j l o p q r s t x
    A B C D E F G H I J K L M N O P Q R S T U V W X Y Z
  $.

  $( Arbitrary inhabited source carrier and abstract implementation type. $)
  ntp4vc-location-carrier-nonempty $e |- U =/= (/) $.
  ntp4vc-default-location $e |- G e. U $.
  ntp4vc-null-location $e |- E e. U $.
  ntp4vc-implementation-carrier-nonempty $e |- W =/= (/) $.

  ntp4vc-to-fmap-function $e |- F e. ( ( NTP4VCFMap U ) ^m W ) $.
  ntp4vc-old-prev-implementation $e |- C e. W $.
  ntp4vc-old-next-implementation $e |- D e. W $.
  ntp4vc-source-list $e |- A e. Word U $.
  ntp4vc-source-head $e |- B e. U $.
  ntp4vc-source-start $e |- I e. ZZ $.
  ntp4vc-source-length $e |- J e. ZZ $.

  $( Exact finite integer-labelled binary tree datatype. $)
  ntp4vc-tree-empty-closure $e |- NTP4VCEmpty e. T $.

  ntp4vc-tree-node-closure $e |- A. l e. T A. x e. ZZ A. r e. T
    ( NTP4VCNode l x r ) e. T $.

  ntp4vc-tree-constructor-exhaustive $e |- A. t e. T
    (
      t = NTP4VCEmpty
      \/
      E. l e. T E. x e. ZZ E. r e. T
        t = ( NTP4VCNode l x r )
    ) $.

  ntp4vc-tree-structural-induction $e |- A. s e. ~P T
    (
      (
        NTP4VCEmpty e. s
        /\
        A. l e. T A. x e. ZZ A. r e. T
          (
            (
              l e. s
              /\
              r e. s
            )
            ->
            ( NTP4VCNode l x r ) e. s
          )
      )
      ->
      s = T
    ) $.

  $( Complete recursive source tree relation. $)
  ntp4vc-tree-relation-type $e |- R C_
    (
      ( NTP4VCFMap U )
      X.
      (
        ( NTP4VCFMap U )
        X.
        (
          ( Word U )
          X.
          (
            U
            X.
            (
              T
              X.
              ( ZZ X. ZZ )
            )
          )
        )
      )
    ) $.

  ntp4vc-tree-empty-equation $e |-
    A. p e. ( NTP4VCFMap U )
      A. q e. ( NTP4VCFMap U )
        A. s e. Word U
          A. o e. U
            A. a e. ZZ
              A. b e. ZZ
                (
                  NTP4VCTree
                    R p q s o NTP4VCEmpty a b
                  <->
                  (
                    (
                      NTP4VCValid p q s G E
                      /\
                      (
                        0 <_ a
                        /\
                        (
                          a <_ b
                          /\
                          b <_ ( # ` s )
                        )
                      )
                    )
                    /\
                    (
                      o = E
                      /\
                      a = b
                    )
                  )
                ) $.

  ntp4vc-tree-node-equation $e |-
    A. p e. ( NTP4VCFMap U )
      A. q e. ( NTP4VCFMap U )
        A. s e. Word U
          A. o e. U
            A. l e. T
              A. x e. ZZ
                A. r e. T
                  A. a e. ZZ
                    A. b e. ZZ
                      (
                        NTP4VCTree
                          R p q s o ( NTP4VCNode l x r ) a b
                        <->
                        (
                          (
                            NTP4VCValid p q s G E
                            /\
                            (
                              0 <_ a
                              /\
                              (
                                a <_ b
                                /\
                                b <_ ( # ` s )
                              )
                            )
                          )
                          /\
                          (
                            (
                              a <_ x
                              /\
                              x < b
                            )
                            /\
                            (
                              o = ( NTP4VCAt s x G )
                              /\
                              (
                                NTP4VCTree
                                  R
                                  p
                                  q
                                  s
                                  ( NTP4VCLookup p o G )
                                  l
                                  a
                                  x
                                /\
                                NTP4VCTree
                                  R
                                  p
                                  q
                                  s
                                  ( NTP4VCLookup q o G )
                                  r
                                  ( x + 1 )
                                  b
                              )
                            )
                          )
                        )
                      ) $.

  $( Complete recursive source height function. $)
  ntp4vc-height-function $e |- K e. ( ZZ ^m T ) $.

  ntp4vc-height-empty $e |- (
    K ` NTP4VCEmpty
  ) = 0 $.

  ntp4vc-height-node $e |- A. l e. T A. x e. ZZ A. r e. T
    (
      K ` ( NTP4VCNode l x r )
    )
    =
    (
      1
      +
      (
        NTP4VCMax
          ( K ` l )
          ( K ` r )
      )
    ) $.

  $( The original source precondition. $)
  ntp4vc-initial-dll $e |- (
    NTP4VCDll
      ( F ` C )
      ( F ` D )
      A
      B
      I
      ( I + J )
      G
      E
  ) $.

  ntp4vc-pearl-verifythis-2021-dll-to-bst-rec-vc $a |- (
    NTP4VCRecVC
      R F C D A B I J G E K W T U
  ) $.
$}
