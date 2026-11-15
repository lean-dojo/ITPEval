$(
  Statement-only formalization of the NTP4VC corpus artifact
  pearl/avl/priority_queue_PQueue_minqtvc: the priority-queue minimum
  verification condition states that positive cardinality makes selection
  possible and that any selected optional element exists, has positive bag
  multiplicity, and equals the stored minimum. This file contains no proof.
$)

$[ lib/set.mm $]

$(
  U, V, and Y are respectively the arbitrary source carriers t alpha,
  t3 alpha, and t1. SetMM words over U are exactly arbitrary finite
  zero-based source lists. P is m1, represented by a pair of a U-word and
  an integer height; C is key, D is the total preorder le, Q is the
  specialized aggregate, and K is get_minimum_index.

  Options and splits use disjoint tagged encodings. NTP4VCAt reproduces
  source integer-to-natural conversion and inhabited total list lookup.
  NTP4VCBag counts precisely the indices carrying each element, while
  NTP4VCMinimum is the K-selected element. Lower bounds and strict lower
  bounds expand the source definitions over every integer index.

  The tree carrier, recursive sequence and height functions, balance
  predicate, representation invariant, and injectivity law retain the
  abstract AVL context of t3. The K laws are the source bounds, aggregate,
  strict-prefix, and suffix lower-bound specifications, written directly
  over original list indices.

  The m3 record fields are expanded definitionally: its cardinality is the
  word length, its bag is NTP4VCBag, and its minimum is NTP4VCMinimum.
  Exhaustive option matches are rendered by equality with the tagged option;
  in particular, the result-match antecedent is exactly equality with
  NTP4VCSome result. The result remains internally universally quantified.
  Every element, list, split, option, abstract-tree, and integer quantifier
  retains its full source domain. The final $a declaration is Metamath's
  native unproved statement encoding; this database contains no $p proof
  declaration.
$)

$c
  NTP4VCTreeEmpty NTP4VCTreeNode
  NTP4VCNone NTP4VCSome NTP4VCOption
  NTP4VCSplitMk NTP4VCSplit NTP4VCSplitLeft
  NTP4VCSplitMiddle NTP4VCSplitRight
  NTP4VCOptionSeq NTP4VCRebuild
  NTP4VCSeq NTP4VCHgt NTP4VCNodeModel
  NTP4VCToNat NTP4VCAt NTP4VCTail
  NTP4VCOp NTP4VCLowerBound NTP4VCLowerBoundStrict
  NTP4VCSelected NTP4VCSelectionPossible
  NTP4VCBag NTP4VCMinimum
$.

ntp4vc-tree-empty-syntax $a class NTP4VCTreeEmpty $.
ntp4vc-tree-node-syntax
  $a class ( NTP4VCTreeNode A B C D E ) $.

ntp4vc-none-syntax $a class NTP4VCNone $.
ntp4vc-some-syntax $a class ( NTP4VCSome A ) $.
ntp4vc-option-syntax $a class ( NTP4VCOption A ) $.

ntp4vc-split-mk-syntax
  $a class ( NTP4VCSplitMk A B C ) $.
ntp4vc-split-syntax $a class ( NTP4VCSplit A ) $.
ntp4vc-split-left-syntax
  $a class ( NTP4VCSplitLeft A ) $.
ntp4vc-split-middle-syntax
  $a class ( NTP4VCSplitMiddle A ) $.
ntp4vc-split-right-syntax
  $a class ( NTP4VCSplitRight A ) $.
ntp4vc-option-seq-syntax
  $a class ( NTP4VCOptionSeq A ) $.
ntp4vc-rebuild-syntax $a class ( NTP4VCRebuild A ) $.

ntp4vc-seq-syntax $a class ( NTP4VCSeq A ) $.
ntp4vc-hgt-syntax $a class ( NTP4VCHgt A ) $.
ntp4vc-node-model-syntax
  $a class ( NTP4VCNodeModel A B C ) $.

ntp4vc-to-nat-syntax $a class ( NTP4VCToNat A ) $.
ntp4vc-at-syntax $a class ( NTP4VCAt A B C ) $.
ntp4vc-tail-syntax $a class ( NTP4VCTail A ) $.
ntp4vc-op-syntax $a class ( NTP4VCOp A B C ) $.

ntp4vc-lower-bound-syntax
  $a wff ( NTP4VCLowerBound A B C D E ) $.
ntp4vc-lower-bound-strict-syntax
  $a wff ( NTP4VCLowerBoundStrict A B C D E ) $.
ntp4vc-selected-syntax
  $a wff ( NTP4VCSelected A B C D E ) $.
ntp4vc-selection-possible-syntax
  $a wff ( NTP4VCSelectionPossible A ) $.

ntp4vc-bag-syntax $a class ( NTP4VCBag A B ) $.
ntp4vc-minimum-syntax
  $a class ( NTP4VCMinimum A B C ) $.

ntp4vc-tree-empty-def $a |- NTP4VCTreeEmpty = <. 2 , (/) >. $.

ntp4vc-tree-node-def $a |- ( NTP4VCTreeNode A B C D E ) =
  <. 3 , <. A , <. B , <. C , <. D , E >. >. >. >. >. $.

ntp4vc-none-def $a |- NTP4VCNone = (/) $.

ntp4vc-some-def $a |- ( NTP4VCSome A ) = <. 1 , A >. $.

${
  $d x y A $.

  ntp4vc-option-def $a |- ( NTP4VCOption A ) =
    { x |
      (
        x = NTP4VCNone
        \/
        E. y e. A x = ( NTP4VCSome y )
      )
    } $.
$}

ntp4vc-split-mk-def $a |- ( NTP4VCSplitMk A B C ) =
  <. A , <. B , C >. >. $.

${
  $d l o r x A $.

  ntp4vc-split-def $a |- ( NTP4VCSplit A ) =
    { x |
      E. l e. Word A
        E. o e. ( NTP4VCOption A )
          E. r e. Word A
            x = ( NTP4VCSplitMk l o r )
    } $.
$}

ntp4vc-split-left-def $a |- ( NTP4VCSplitLeft A ) =
  ( 1st ` A ) $.

ntp4vc-split-middle-def $a |- ( NTP4VCSplitMiddle A ) =
  ( 1st ` ( 2nd ` A ) ) $.

ntp4vc-split-right-def $a |- ( NTP4VCSplitRight A ) =
  ( 2nd ` ( 2nd ` A ) ) $.

ntp4vc-option-seq-def $a |- ( NTP4VCOptionSeq A ) =
  if (
    A = NTP4VCNone ,
    (/) ,
    <" ( 2nd ` A ) ">
  ) $.

ntp4vc-rebuild-def $a |- ( NTP4VCRebuild A ) =
  (
    (
      ( NTP4VCSplitLeft A )
      ++
      ( NTP4VCOptionSeq ( NTP4VCSplitMiddle A ) )
    )
    ++
    ( NTP4VCSplitRight A )
  ) $.

ntp4vc-seq-def $a |- ( NTP4VCSeq A ) = ( 1st ` A ) $.

ntp4vc-hgt-def $a |- ( NTP4VCHgt A ) = ( 2nd ` A ) $.

ntp4vc-node-model-def $a |- ( NTP4VCNodeModel A B C ) =
  ( A ++ ( <" B "> ++ C ) ) $.

ntp4vc-to-nat-def $a |- ( NTP4VCToNat A ) =
  if ( 0 <_ A , A , 0 ) $.

ntp4vc-at-def $a |- ( NTP4VCAt A B C ) =
  if (
    ( NTP4VCToNat B ) < ( # ` A ) ,
    ( A ` ( NTP4VCToNat B ) ) ,
    C
  ) $.

${
  $d i A $.

  ntp4vc-tail-def $a |- ( NTP4VCTail A ) =
    (
      i e. ( 0 ..^ ( ( # ` A ) - 1 ) )
      |-> ( A ` ( i + 1 ) )
    ) $.
$}

ntp4vc-op-def $a |- ( NTP4VCOp A B C ) =
  if (
    A = NTP4VCNone ,
    B ,
    if (
      B = NTP4VCNone ,
      A ,
      if (
        (
          <. ( 2nd ` B ) , ( 2nd ` A ) >. e. C
          /\
          -. <. ( 2nd ` A ) , ( 2nd ` B ) >. e. C
        ) ,
        B ,
        A
      )
    )
  ) $.

${
  $d i A B C D E $.

  ntp4vc-lower-bound-def $a |- (
    ( NTP4VCLowerBound A B C D E )
    <->
    A. i e. ZZ
      (
        ( 0 <_ i /\ i < ( # ` B ) )
        ->
        <. A , ( C ` ( NTP4VCAt B i E ) ) >. e. D
      )
  ) $.
$}

${
  $d i A B C D E $.

  ntp4vc-lower-bound-strict-def $a |- (
    ( NTP4VCLowerBoundStrict A B C D E )
    <->
    A. i e. ZZ
      (
        ( 0 <_ i /\ i < ( # ` B ) )
        ->
        (
          <. A , ( C ` ( NTP4VCAt B i E ) ) >. e. D
          /\
          -. <. ( C ` ( NTP4VCAt B i E ) ) , A >. e. D
        )
      )
  ) $.
$}

${
  $d d A B C D E $.

  ntp4vc-selected-def $a |- (
    ( NTP4VCSelected A B C D E )
    <->
    E. d e. B
      (
        ( NTP4VCSplitMiddle A ) = ( NTP4VCSome d )
        /\
        (
          (
            NTP4VCLowerBound
              ( C ` d ) ( NTP4VCSplitRight A ) C D E
          )
          /\
          (
            NTP4VCLowerBoundStrict
              ( C ` d ) ( NTP4VCSplitLeft A ) C D E
          )
        )
      )
  ) $.
$}

ntp4vc-selection-possible-def $a |- (
  ( NTP4VCSelectionPossible A )
  <->
  A =/= (/)
) $.

${
  $d i x A B $.

  ntp4vc-bag-def $a |- ( NTP4VCBag A B ) =
    (
      x e. B |->
        (
          # `
          { i e. ( 0 ..^ ( # ` A ) ) | ( A ` i ) = x }
        )
    ) $.
$}

ntp4vc-minimum-def $a |- ( NTP4VCMinimum A B C ) =
  ( NTP4VCAt A ( B ` A ) C ) $.

${
  $d d e h i l m r s u v w x y z
     A B C D E F G H I J K L M N O P Q R S T U V W X Y Z $.

  ntp4vc-element-carrier-nonempty $e |- U =/= (/) $.
  ntp4vc-abstract-tree-carrier-nonempty $e |- V =/= (/) $.
  ntp4vc-key-carrier-nonempty $e |- Y =/= (/) $.
  ntp4vc-default-element $e |- E e. U $.

  ntp4vc-key-function $e |- C e. ( Y ^m U ) $.
  ntp4vc-le-relation $e |- D C_ ( Y X. Y ) $.
  ntp4vc-le-reflexive $e |- A. x e. Y <. x , x >. e. D $.
  ntp4vc-le-transitive $e |- A. x e. Y A. y e. Y A. z e. Y
    (
      (
        <. x , y >. e. D
        /\
        <. y , z >. e. D
      )
      ->
      <. x , z >. e. D
    ) $.
  ntp4vc-le-total $e |- A. x e. Y A. y e. Y
    (
      <. x , y >. e. D
      \/
      <. y , x >. e. D
    ) $.

  ntp4vc-tree-empty-in-carrier $e |- NTP4VCTreeEmpty e. X $.
  ntp4vc-tree-node-closure $e |- A. l e. X A. d e. U
    A. r e. X A. h e. NN0 A. m e. ( NTP4VCOption Y )
      ( NTP4VCTreeNode l d r h m ) e. X $.
  ntp4vc-tree-exhaustive $e |- A. x e. X
    (
      x = NTP4VCTreeEmpty
      \/
      E. l e. X E. d e. U E. r e. X E. h e. NN0
        E. m e. ( NTP4VCOption Y )
          x = ( NTP4VCTreeNode l d r h m )
    ) $.

  ntp4vc-m1-function $e |- P e. ( ( Word U X. ZZ ) ^m V ) $.
  ntp4vc-repr-function $e |- L e. ( X ^m V ) $.
  ntp4vc-seq-model-function $e |- M e. ( ( Word U ) ^m X ) $.
  ntp4vc-real-height-function $e |- N e. ( ZZ ^m X ) $.
  ntp4vc-balanced-predicate $e |- O C_ X $.

  ntp4vc-seq-model-empty $e |- ( M ` NTP4VCTreeEmpty ) = (/) $.
  ntp4vc-seq-model-node $e |- A. l e. X A. d e. U
    A. r e. X A. h e. NN0 A. m e. ( NTP4VCOption Y )
      (
        M ` ( NTP4VCTreeNode l d r h m )
      )
      =
      ( NTP4VCNodeModel ( M ` l ) d ( M ` r ) ) $.
  ntp4vc-real-height-empty $e |- ( N ` NTP4VCTreeEmpty ) = 0 $.
  ntp4vc-real-height-node $e |- A. l e. X A. d e. U
    A. r e. X A. h e. NN0 A. m e. ( NTP4VCOption Y )
      (
        N ` ( NTP4VCTreeNode l d r h m )
      )
      =
      (
        1 + if ( ( N ` l ) < ( N ` r ) , ( N ` r ) , ( N ` l ) )
      ) $.

  ntp4vc-aggregate-function
    $e |- Q e. ( ( NTP4VCOption Y ) ^m Word U ) $.
  ntp4vc-aggregate-recursion $e |- A. s e. Word U
    (
      ( Q ` s )
      =
      if (
        s = (/) ,
        NTP4VCNone ,
        (
          NTP4VCOp
            ( NTP4VCSome ( C ` ( s ` 0 ) ) )
            ( Q ` ( NTP4VCTail s ) )
            D
        )
      )
    ) $.
  ntp4vc-op-associative $e |-
    A. x e. ( NTP4VCOption Y )
      A. y e. ( NTP4VCOption Y )
        A. z e. ( NTP4VCOption Y )
          (
            NTP4VCOp x ( NTP4VCOp y z D ) D
          )
          =
          (
            NTP4VCOp ( NTP4VCOp x y D ) z D
          ) $.
  ntp4vc-op-neutral $e |- A. x e. ( NTP4VCOption Y )
    (
      ( NTP4VCOp x NTP4VCNone D ) = x
      /\
      x = ( NTP4VCOp NTP4VCNone x D )
    ) $.

  ntp4vc-balancing-positive-natural $e |- B e. NN $.
  ntp4vc-balanced-empty $e |- NTP4VCTreeEmpty e. O $.
  ntp4vc-balanced-node $e |- A. l e. X A. d e. U
    A. r e. X A. h e. NN0 A. m e. ( NTP4VCOption Y )
      (
        ( NTP4VCTreeNode l d r h m ) e. O
        <->
        (
          h = ( N ` ( NTP4VCTreeNode l d r h m ) )
          /\
          (
            m = ( Q ` ( M ` ( NTP4VCTreeNode l d r h m ) ) )
            /\
            (
              (
                -u B <_ ( ( N ` r ) - ( N ` l ) )
                /\
                ( ( N ` r ) - ( N ` l ) ) <_ B
              )
              /\
              ( l e. O /\ r e. O )
            )
          )
        )
      ) $.

  ntp4vc-t-invariant $e |- A. x e. V
    (
      (
        ( L ` x ) e. O
        /\
        ( NTP4VCSeq ( P ` x ) ) = ( M ` ( L ` x ) )
      )
      /\
      ( NTP4VCHgt ( P ` x ) ) = ( N ` ( L ` x ) )
    ) $.
  ntp4vc-t-injective $e |- A. x e. V A. y e. V
    (
      (
        ( L ` x ) = ( L ` y )
        /\
        ( P ` x ) = ( P ` y )
      )
      ->
      x = y
    ) $.

  ntp4vc-minimum-index-function
    $e |- K e. ( ZZ ^m Word U ) $.
  ntp4vc-minimum-index-specifications $e |- A. s e. Word U
    (
      s =/= (/)
      ->
      (
        (
          0 <_ ( K ` s )
          /\
          ( K ` s ) < ( # ` s )
        )
        /\
        (
          ( Q ` s )
          =
          (
            NTP4VCSome
              ( C ` ( NTP4VCAt s ( K ` s ) E ) )
          )
          /\
          (
            A. i e. ZZ
              (
                ( 0 <_ i /\ i < ( K ` s ) )
                ->
                (
                  (
                    <.
                      ( C ` ( NTP4VCAt s ( K ` s ) E ) ) ,
                      ( C ` ( NTP4VCAt s i E ) )
                    >. e. D
                  )
                  /\
                  -.
                  (
                    <.
                      ( C ` ( NTP4VCAt s i E ) ) ,
                      ( C ` ( NTP4VCAt s ( K ` s ) E ) )
                    >. e. D
                  )
                )
              )
            /\
            A. i e. ZZ
              (
                ( ( K ` s ) <_ i /\ i < ( # ` s ) )
                ->
                (
                  <.
                    ( C ` ( NTP4VCAt s ( K ` s ) E ) ) ,
                    ( C ` ( NTP4VCAt s i E ) )
                  >. e. D
                )
              )
          )
        )
      )
    ) $.

  $( Source theorem parameter: A=t5. $)
  ntp4vc-t5-type $e |- A e. V $.

  ntp4vc-fact0 $e |- (
    0 < ( # ` ( NTP4VCSeq ( P ` A ) ) )
  ) $.

  ntp4vc-pearl-priority-queue-min-vc $a |- (
    ( NTP4VCSelectionPossible ( NTP4VCSeq ( P ` A ) ) )
    /\
    A. u e. ( NTP4VCSplit U )
      A. v e. ( NTP4VCOption U )
        (
          (
            (
              ( NTP4VCSelected u U C D E )
              /\
              ( NTP4VCRebuild u ) = ( NTP4VCSeq ( P ` A ) )
            )
            /\
            ( NTP4VCSplitMiddle u ) = v
          )
          ->
          (
            v =/= NTP4VCNone
            /\
            A. w e. U
              (
                v = ( NTP4VCSome w )
                ->
                (
                  0
                  <
                  (
                    (
                      NTP4VCBag
                        ( NTP4VCSeq ( P ` A ) )
                        U
                    )
                    ` w
                  )
                  /\
                  w
                  =
                  (
                    NTP4VCMinimum
                      ( NTP4VCSeq ( P ` A ) )
                      K
                      E
                  )
                )
              )
          )
        )
  ) $.
$}
