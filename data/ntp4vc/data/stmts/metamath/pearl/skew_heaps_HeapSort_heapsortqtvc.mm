$(
  Statement-only formalization of the NTP4VC corpus artifact
  pearl/skew_heaps_HeapSort_heapsortqtvc: the skew-heap heapsort verification
  condition states heap construction with occurrence preservation, repeated
  minimum extraction into a sorted array, and preservation of the input
  permutation. This file contains no proof.
$)

$[ lib/set.mm $]

$(
  U is the arbitrary inhabited source carrier elt, D is its chosen default
  element for totalized list lookup, and R is the source total preorder le.
  SetMM words over U are exactly arbitrary finite zero-based source lists.

  T is exactly the source inductive binary-tree carrier: NTP4VCEmpty and
  NTP4VCNode are disjoint injective tagged constructors, while constructor
  closure, exhaustiveness, and structural induction exclude both missing
  finite trees and extraneous non-well-founded values. L, H, O, S, and M
  represent le_root, heap, occ, size, and minimum. Their equations below are
  the complete source definitions, including minimum on every nonempty tree.

  NTP4VCToNat reproduces the source integer-to-natural conversion,
  NTP4VCAt is integer-indexed list lookup with the supplied default outside
  [0, length), and NTP4VCSet and NTP4VCOccRange reproduce List.set and the
  half-open map occurrence count. NTP4VCPerm is bidirectionally equivalent
  to List.Perm for finite words. NTP4VCSortedSub and NTP4VCSorted use R at
  every pair of source integer indices in the specified half-open interval.

  The remaining predicates only factor the original nested verification
  condition. Expanding their biconditional definitions recovers both loop
  initializations, every integer, element, tree, and list quantifier, all heap
  and occurrence invariants, the add and remove-min continuations, the exact
  array update law, and the final sorted-permutation conclusion. Let-bound
  values are replaced by direct substitution. The final declaration is
  Metamath's native unproved $a statement encoding; this database contains no
  $p proof declaration.
$)

$c
  NTP4VCEmpty NTP4VCNode
  NTP4VCToNat NTP4VCAt NTP4VCSet NTP4VCOccRange
  NTP4VCMem NTP4VCPerm NTP4VCSortedSub NTP4VCSorted
  NTP4VCBuildOcc NTP4VCMapUpdate NTP4VCExtractInv
  NTP4VCExtractStep NTP4VCSecondLoop NTP4VCFirstLoop
$.

ntp4vc-empty-syntax $a class NTP4VCEmpty $.
ntp4vc-node-syntax $a class ( NTP4VCNode A B C ) $.
ntp4vc-to-nat-syntax $a class ( NTP4VCToNat A ) $.
ntp4vc-at-syntax $a class ( NTP4VCAt A B C ) $.
ntp4vc-set-syntax $a class ( NTP4VCSet A B C ) $.
ntp4vc-occ-range-syntax
  $a class ( NTP4VCOccRange A B C D E ) $.

ntp4vc-mem-syntax
  $a wff ( NTP4VCMem A B C ) $.
ntp4vc-perm-syntax
  $a wff ( NTP4VCPerm A B C D ) $.
ntp4vc-sorted-sub-syntax
  $a wff ( NTP4VCSortedSub A B C D E F ) $.
ntp4vc-sorted-syntax
  $a wff ( NTP4VCSorted A B C D ) $.
ntp4vc-build-occ-syntax
  $a wff ( NTP4VCBuildOcc A B C D E F ) $.
ntp4vc-map-update-syntax
  $a wff ( NTP4VCMapUpdate A B C D E ) $.
ntp4vc-extract-inv-syntax
  $a wff ( NTP4VCExtractInv A B C D E F G H I J ) $.
ntp4vc-extract-step-syntax
  $a wff (
    NTP4VCExtractStep A B C D E F G H I J K L
  ) $.
ntp4vc-second-loop-syntax
  $a wff ( NTP4VCSecondLoop A B C D E F G H I J ) $.
ntp4vc-first-loop-syntax
  $a wff ( NTP4VCFirstLoop A B C D E F G H I ) $.

ntp4vc-empty-definition $a |- NTP4VCEmpty = <. 0 , (/) >. $.

ntp4vc-node-definition $a |- (
  NTP4VCNode A B C
) = <. 1 , <. A , <. B , C >. >. >. $.

ntp4vc-to-nat-definition $a |- (
  NTP4VCToNat A
) = if ( 0 <_ A , A , 0 ) $.

ntp4vc-at-definition $a |- (
  NTP4VCAt A B C
) = if (
  ( 0 <_ B /\ B < ( # ` A ) ) ,
  ( A ` B ) ,
  C
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
  $d k A B C D E $.

  ntp4vc-occ-range-definition $a |- (
    NTP4VCOccRange A B C D E
  ) = (
    # `
    { k e. ZZ |
      (
        (
          C <_ k
          /\
          k < D
        )
        /\
        ( NTP4VCAt A k E ) = B
      )
    }
  ) $.
$}

ntp4vc-mem-definition $a |- (
  NTP4VCMem A B C
) <-> 0 < ( C ` <. A , B >. ) $.

${
  $d v A B C D $.

  ntp4vc-perm-definition $a |- (
    NTP4VCPerm A B C D
  ) <->
  (
    (
      A e. Word C
      /\
      B e. Word C
    )
    /\
    (
      ( # ` A ) = ( # ` B )
      /\
      A. v e. C
        (
          NTP4VCOccRange A v 0 ( # ` A ) D
        )
        =
        (
          NTP4VCOccRange B v 0 ( # ` B ) D
        )
    )
  ) $.
$}

${
  $d i j A B C D E F $.

  ntp4vc-sorted-sub-definition $a |- (
    NTP4VCSortedSub A B C D E F
  ) <->
  (
    (
      A e. Word D
      /\
      (
        B e. ZZ
        /\
        C e. ZZ
      )
    )
    /\
    A. i e. ZZ A. j e. ZZ
      (
        (
          B <_ i
          /\
          (
            i < j
            /\
            j < C
          )
        )
        ->
        <.
          ( NTP4VCAt A i F ) ,
          ( NTP4VCAt A j F )
        >. e. E
      )
  ) $.
$}

${
  $d i j A B C D $.

  ntp4vc-sorted-definition $a |- (
    NTP4VCSorted A B C D
  ) <->
  (
    A e. Word B
    /\
    A. i e. ZZ A. j e. ZZ
      (
        (
          0 <_ i
          /\
          (
            i < j
            /\
            j < ( # ` A )
          )
        )
        ->
        <.
          ( NTP4VCAt A i D ) ,
          ( NTP4VCAt A j D )
        >. e. C
      )
  ) $.
$}

${
  $d e A B C D E F $.

  ntp4vc-build-occ-definition $a |- (
    NTP4VCBuildOcc A B C D E F
  ) <->
  A. e e. D
    (
      (
        NTP4VCOccRange A e C ( # ` A ) E
      )
      +
      ( F ` <. e , B >. )
    )
    =
    (
      NTP4VCOccRange A e 0 ( # ` A ) E
    ) $.
$}

${
  $d k A B C D E $.

  ntp4vc-map-update-definition $a |- (
    NTP4VCMapUpdate A B C D E
  ) <->
  (
    (
      A e. Word D
      /\
      (
        B e. ZZ
        /\
        C e. D
      )
    )
    /\
    A. k e. ZZ
      (
        NTP4VCAt ( NTP4VCSet A B C ) k E
      )
      =
      if (
        k = B ,
        C ,
        ( NTP4VCAt A k E )
      )
  ) $.
$}

${
  $d e j A B C D E F G H I J $.

  $(
    A=original list, B=current list, C=heap tree, D=loop index,
    E=element carrier, F=default, G=preorder, H=heap predicate,
    I=occurrence function, and J=size function.
  $)
  ntp4vc-extract-inv-definition $a |- (
    NTP4VCExtractInv A B C D E F G H I J
  ) <->
  (
    ( NTP4VCSortedSub B 0 D E G F )
    /\
    (
      (
        C e. H
        /\
        ( J ` C ) = ( ( # ` A ) - D )
      )
      /\
      (
        A. j e. ZZ
          (
            (
              0 <_ j
              /\
              j < D
            )
            ->
            A. e e. E
              (
                ( NTP4VCMem e C I )
                ->
                <. ( NTP4VCAt B j F ) , e >. e. G
              )
          )
        /\
        A. e e. E
          (
            (
              NTP4VCOccRange B e 0 D F
            )
            +
            ( I ` <. e , C >. )
          )
          =
          (
            NTP4VCOccRange A e 0 ( # ` A ) F
          )
      )
    )
  ) $.
$}

${
  $d e o A B C D E F G H I J K L $.

  $(
    A=original list, B=current list, C=current tree, D=loop index,
    E=element carrier, F=default, G=preorder, H=tree carrier,
    I=heap predicate, J=occurrence function, K=size, and L=minimum.
  $)
  ntp4vc-extract-step-definition $a |- (
    NTP4VCExtractStep A B C D E F G H I J K L
  ) <->
  (
    (
      C e. I
      /\
      0 < ( K ` C )
    )
    /\
    (
      (
        0 <_ D
        /\
        D < ( # ` B )
      )
      /\
      (
        (
          # ` ( NTP4VCSet B D ( L ` C ) )
        )
        =
        ( # ` B )
        ->
        (
          ( NTP4VCMapUpdate B D ( L ` C ) E F )
          ->
          (
            (
              C e. I
              /\
              0 < ( K ` C )
            )
            /\
            A. o e. H
              (
                (
                  o e. I
                  /\
                  (
                    (
                      J ` <. ( L ` C ) , o >.
                    )
                    =
                    (
                      ( J ` <. ( L ` C ) , C >. ) - 1
                    )
                    /\
                    (
                      A. e e. E
                        (
                          e =/= ( L ` C )
                          ->
                          (
                            J ` <. e , o >.
                          )
                          =
                          (
                            J ` <. e , C >.
                          )
                        )
                      /\
                      ( K ` o ) = ( ( K ` C ) - 1 )
                    )
                  )
                )
                ->
                (
                  NTP4VCExtractInv
                    A
                    ( NTP4VCSet B D ( L ` C ) )
                    o
                    ( D + 1 )
                    E F G I J K
                )
              )
          )
        )
      )
    )
  ) $.
$}

${
  $d i o t A B C D E F G H I J $.

  $(
    A=input list, B=initial tree, C=element carrier, D=default,
    E=preorder, F=tree carrier, G=heap predicate, H=occurrence function,
    I=size, and J=minimum.
  $)
  ntp4vc-second-loop-definition $a |- (
    NTP4VCSecondLoop A B C D E F G H I J
  ) <->
  (
    (
      0 <_ ( ( ( # ` A ) - 1 ) + 1 )
      ->
      (
        (
          NTP4VCExtractInv A A B 0 C D E G H I
        )
        /\
        A. t e. F A. o e. Word C
          (
            ( # ` o ) = ( # ` A )
            ->
            (
              A. i e. ZZ
                (
                  (
                    (
                      0 <_ i
                      /\
                      i <_ ( ( # ` A ) - 1 )
                    )
                    /\
                    (
                      NTP4VCExtractInv
                        A o t i C D E G H I
                    )
                  )
                  ->
                  (
                    NTP4VCExtractStep
                      A o t i C D E F G H I J
                  )
                )
              /\
              (
                (
                  NTP4VCExtractInv
                    A o t
                    ( ( ( # ` A ) - 1 ) + 1 )
                    C D E G H I
                )
                ->
                (
                  ( NTP4VCSorted o C E D )
                  /\
                  ( NTP4VCPerm A o C D )
                )
              )
            )
          )
      )
    )
    /\
    (
      ( ( ( # ` A ) - 1 ) + 1 ) < 0
      ->
      (
        ( NTP4VCSorted A C E D )
        /\
        ( NTP4VCPerm A A C D )
      )
    )
  ) $.
$}

${
  $d e o t A B C D E F G H I $.

  $(
    A=input list, B=element carrier, C=default, D=preorder,
    E=tree carrier, F=heap predicate, G=occurrence function, H=size,
    and I=minimum.
  $)
  ntp4vc-first-loop-definition $a |- (
    NTP4VCFirstLoop A B C D E F G H I
  ) <->
  (
    (
      0 <_ ( ( ( # ` A ) - 1 ) + 1 )
      ->
      (
        (
          (
            NTP4VCEmpty e. F
            /\
            ( H ` NTP4VCEmpty ) = 0
          )
          /\
          (
            NTP4VCBuildOcc
              A NTP4VCEmpty 0 B C G
          )
        )
        /\
        A. t e. E
          (
            (
              (
                (
                  (
                    0 <_ ( H ` t )
                    /\
                    ( H ` t ) <_ ( ( # ` A ) - 1 )
                  )
                  /\
                  t e. F
                )
                /\
                (
                  NTP4VCBuildOcc
                    A t ( H ` t ) B C G
                )
              )
              ->
              (
                (
                  0 <_ ( H ` t )
                  /\
                  ( H ` t ) < ( # ` A )
                )
                /\
                (
                  t e. F
                  /\
                  A. o e. E
                    (
                      (
                        o e. F
                        /\
                        (
                          (
                            G ` <.
                              ( NTP4VCAt A ( H ` t ) C ) ,
                              o
                            >.
                          )
                          =
                          (
                            (
                              G ` <.
                                ( NTP4VCAt A ( H ` t ) C ) ,
                                t
                              >.
                            )
                            +
                            1
                          )
                          /\
                          (
                            A. e e. B
                              (
                                e =/=
                                  ( NTP4VCAt A ( H ` t ) C )
                                ->
                                (
                                  G ` <. e , o >.
                                )
                                =
                                (
                                  G ` <. e , t >.
                                )
                              )
                            /\
                            ( H ` o ) = ( ( H ` t ) + 1 )
                          )
                        )
                      )
                      ->
                      (
                        (
                          o e. F
                          /\
                          ( H ` o ) = ( ( H ` t ) + 1 )
                        )
                        /\
                        (
                          NTP4VCBuildOcc
                            A o ( ( H ` t ) + 1 ) B C G
                        )
                      )
                    )
                )
              )
            )
            /\
            (
              (
                (
                  t e. F
                  /\
                  ( H ` t )
                    =
                    ( ( ( # ` A ) - 1 ) + 1 )
                )
                /\
                (
                  NTP4VCBuildOcc
                    A t
                    ( ( ( # ` A ) - 1 ) + 1 )
                    B C G
                )
              )
              ->
              (
                NTP4VCSecondLoop
                  A t B C D E F G H I
              )
            )
          )
      )
    )
    /\
    (
      ( ( ( # ` A ) - 1 ) + 1 ) < 0
      ->
      (
        NTP4VCSecondLoop
          A NTP4VCEmpty B C D E F G H I
      )
    )
  ) $.
$}

${
  $d e l r s t x y z
     A B C D E F G H I J K L M N O P Q R S T U V W X Y Z $.

  $( Source carrier elt, chosen inhabitant, and total preorder le. $)
  ntp4vc-element-carrier-nonempty $e |- U =/= (/) $.
  ntp4vc-default-element $e |- D e. U $.
  ntp4vc-le-relation $e |- R C_ ( U X. U ) $.

  ntp4vc-le-reflexive $e |- A. x e. U
    <. x , x >. e. R $.

  ntp4vc-le-transitive $e |- A. x e. U A. y e. U A. z e. U
    (
      (
        <. x , y >. e. R
        /\
        <. y , z >. e. R
      )
      ->
      <. x , z >. e. R
    ) $.

  ntp4vc-le-total $e |- A. x e. U A. y e. U
    (
      <. x , y >. e. R
      \/
      <. y , x >. e. R
    ) $.

  $( Exact finite inductive binary-tree carrier over U. $)
  ntp4vc-tree-empty-closure $e |- NTP4VCEmpty e. T $.

  ntp4vc-tree-node-closure $e |- A. l e. T A. x e. U A. r e. T
    ( NTP4VCNode l x r ) e. T $.

  ntp4vc-tree-constructor-exhaustive $e |- A. t e. T
    (
      t = NTP4VCEmpty
      \/
      E. l e. T E. x e. U E. r e. T
        t = ( NTP4VCNode l x r )
    ) $.

  ntp4vc-tree-structural-induction $e |- A. s e. ~P T
    (
      (
        NTP4VCEmpty e. s
        /\
        A. l e. T A. x e. U A. r e. T
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

  $( Types of the source tree operations used by the VC. $)
  ntp4vc-le-root-relation $e |- L C_ ( U X. T ) $.
  ntp4vc-heap-predicate $e |- H C_ T $.
  ntp4vc-occ-function $e |- O e. ( ZZ ^m ( U X. T ) ) $.
  ntp4vc-size-function $e |- S e. ( ZZ ^m T ) $.
  ntp4vc-minimum-function $e |- M e. ( U ^m T ) $.

  $( le_root equations. $)
  ntp4vc-le-root-empty $e |- A. x e. U
    <. x , NTP4VCEmpty >. e. L $.

  ntp4vc-le-root-node $e |- A. x e. U A. l e. T
    A. y e. U A. r e. T
      (
        <. x , ( NTP4VCNode l y r ) >. e. L
        <->
        <. x , y >. e. R
      ) $.

  $( heap equations. $)
  ntp4vc-heap-empty $e |- NTP4VCEmpty e. H $.

  ntp4vc-heap-node $e |- A. l e. T A. x e. U A. r e. T
    (
      ( NTP4VCNode l x r ) e. H
      <->
      (
        <. x , l >. e. L
        /\
        (
          l e. H
          /\
          (
            <. x , r >. e. L
            /\
            r e. H
          )
        )
      )
    ) $.

  $( Integer-valued occurrence-count equations. $)
  ntp4vc-occ-empty $e |- A. x e. U
    ( O ` <. x , NTP4VCEmpty >. ) = 0 $.

  ntp4vc-occ-node $e |- A. x e. U A. l e. T
    A. y e. U A. r e. T
      (
        O ` <. x , ( NTP4VCNode l y r ) >.
      )
      =
      (
        (
          if ( x = y , 1 , 0 )
          +
          ( O ` <. x , l >. )
        )
        +
        ( O ` <. x , r >. )
      ) $.

  $( Integer-valued size equations. $)
  ntp4vc-size-empty $e |- ( S ` NTP4VCEmpty ) = 0 $.

  ntp4vc-size-node $e |- A. l e. T A. x e. U A. r e. T
    (
      S ` ( NTP4VCNode l x r )
    )
    =
    (
      ( 1 + ( S ` l ) )
      +
      ( S ` r )
    ) $.

  $( minimum is the root element of every nonempty source tree. $)
  ntp4vc-minimum-node $e |- A. l e. T A. x e. U A. r e. T
    (
      M ` ( NTP4VCNode l x r )
    ) = x $.

  $( Source theorem parameter a. $)
  ntp4vc-input-word $e |- A e. Word U $.

  ntp4vc-pearl-skew-heaps-heapsort-vc $a |- (
    NTP4VCFirstLoop A U D R T H O S M
  ) $.
$}
