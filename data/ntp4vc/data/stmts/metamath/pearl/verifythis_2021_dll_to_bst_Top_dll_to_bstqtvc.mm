$(
  Statement-only formalization of the NTP4VC corpus artifact
  pearl/verifythis_2021_dll_to_bst_Top_dll_to_bstqtvc
  (ntp4vc__metamath__pearl/verifythis_2021_dll_to_bst_Top_dll_to_bstqtvc):
  the doubly-linked-list-to-binary-search-tree verification
  condition states the exact list, finite-map, framing, inorder, size, and
  powers-of-two height obligations for an arbitrary location carrier. This
  file contains no proof.
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
  exclude missing finite trees and extraneous values.

  NTP4VCValid and NTP4VCDll reproduce the source definitions, including all
  half-open interval bounds, finite-map domains, distinct list locations,
  internal links, and both boundary links. R is the complete recursive source
  tree relation, characterized in both directions on Empty and Node.
  J, K, and L are the complete recursive source size, height, and inorder
  functions.

  NTP4VCFrame retains both source frame intervals. NTP4VCOutputPackage keeps
  the source universal output scope and makes the complete recursive-call
  postcondition conjunction--tree relation, domain equalities, four frame
  conditions, and guarded height bound--the antecedent of one implication to
  the final tree, size, inorder, and height conclusion. No output witness is
  moved into the parameters. The source let-binding
  n = length s - 0 is simplified by integer subtraction to n = length s, and
  h = height o2 is substituted definitionally. The final $a declaration is
  Metamath's native unproved statement encoding; every preceding $a is
  syntax or a faithful definition, and this database contains no $p
  declaration.
$)

$c
  NTP4VCFMap NTP4VCToNat NTP4VCAt NTP4VCLookup
  NTP4VCEmpty NTP4VCNode NTP4VCMax
  NTP4VCPow2 NTP4VCHeightBound
  NTP4VCValid NTP4VCDll NTP4VCTree NTP4VCFrame
  NTP4VCOutputPackage
$.

ntp4vc-fmap-syntax
  $a class ( NTP4VCFMap A ) $.
ntp4vc-to-nat-syntax
  $a class ( NTP4VCToNat A ) $.
ntp4vc-at-syntax
  $a class ( NTP4VCAt A B C ) $.
ntp4vc-lookup-syntax
  $a class ( NTP4VCLookup A B C ) $.
ntp4vc-empty-syntax
  $a class NTP4VCEmpty $.
ntp4vc-node-syntax
  $a class ( NTP4VCNode A B C ) $.
ntp4vc-max-syntax
  $a class ( NTP4VCMax A B ) $.
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
ntp4vc-output-package-syntax
  $a wff (
    NTP4VCOutputPackage A B C D E F G H I J K L M
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

ntp4vc-output-package-definition $a |- (
  NTP4VCOutputPackage A B C D E F G H I J K L M
) <->
(
  (
    (
      NTP4VCTree
        A
        ( B ` F )
        ( B ` G )
        E
        H
        I
        0
        ( 0 + ( # ` E ) )
      /\
      dom ( B ` F ) = dom ( B ` C )
    )
    /\
    (
      dom ( B ` G ) = dom ( B ` D )
      /\
      (
        NTP4VCFrame
          ( B ` F )
          ( B ` C )
          E
          0
          ( 0 + ( # ` E ) )
          J
        /\
        NTP4VCFrame
          ( B ` G )
          ( B ` D )
          E
          0
          ( 0 + ( # ` E ) )
          J
      )
    )
    /\
    NTP4VCHeightBound
      ( # ` E )
      ( L ` I )
  )
  ->
  (
    (
      NTP4VCTree
        A
        ( B ` F )
        ( B ` G )
        E
        H
        I
        0
        ( # ` E )
      /\
      ( K ` I ) = ( # ` E )
    )
    /\
    (
      ( M ` <. E , I >. ) = E
      /\
      NTP4VCHeightBound
        ( # ` E )
        ( L ` I )
    )
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

  $( Complete recursive source size, height, and inorder functions. $)
  ntp4vc-size-function $e |- J e. ( ZZ ^m T ) $.
  ntp4vc-height-function $e |- K e. ( ZZ ^m T ) $.
  ntp4vc-inorder-function $e |-
    L e. ( ( Word U ) ^m ( ( Word U ) X. T ) ) $.

  ntp4vc-size-empty $e |- (
    J ` NTP4VCEmpty
  ) = 0 $.

  ntp4vc-size-node $e |- A. l e. T A. x e. ZZ A. r e. T
    (
      J ` ( NTP4VCNode l x r )
    )
    =
    (
      (
        1
        +
        ( J ` l )
      )
      +
      ( J ` r )
    ) $.

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

  ntp4vc-inorder-empty $e |- A. s e. Word U
    (
      L ` <. s , NTP4VCEmpty >.
    ) = (/) $.

  ntp4vc-inorder-node $e |-
    A. s e. Word U
      A. l e. T
        A. x e. ZZ
          A. r e. T
            (
              L ` <. s , ( NTP4VCNode l x r ) >.
            )
            =
            (
              ( L ` <. s , l >. )
              ++
              (
                <" ( NTP4VCAt s x G ) ">
                ++
                ( L ` <. s , r >. )
              )
            ) $.

  $( The original source precondition. $)
  ntp4vc-initial-dll $e |- (
    NTP4VCDll
      ( F ` C )
      ( F ` D )
      A
      B
      0
      ( # ` A )
      G
      E
  ) $.

  ntp4vc-pearl-verifythis-2021-dll-to-bst-vc $a |- (
    NTP4VCDll
      ( F ` C )
      ( F ` D )
      A
      B
      0
      ( # ` A )
      G
      E
    /\
    (
      NTP4VCDll
        ( F ` C )
        ( F ` D )
        A
        B
        0
        ( 0 + ( # ` A ) )
        G
        E
      /\
      A. q e. W
        A. p e. W
          A. o e. U
            A. t e. T
              (
                NTP4VCOutputPackage
                  R F C D A p q o t G J K L
              )
    )
  ) $.
$}
