$(
  Statement-only formalization of the NTP4VC corpus artifact
  pearl/avl/priority_queue_PQueue_selected_partqtvc: the priority-queue
  selected-part verification condition states that the aggregate comparisons
  choose the current element, the left part, or the right part, and that the
  chosen branch satisfies selection after the corresponding split extension.
  This file contains no proof.
$)

$[ lib/set.mm $]

$(
  U and Y are respectively the arbitrary source carriers t alpha and t1.
  SetMM words over U are exactly arbitrary finite zero-based source lists.
  C is key, D is the source total preorder le, and Q is the specialization
  of agg measure_closure to U. The source predicates eq and lt are expanded
  from their defining bidirectional equalities with D.

  Options, splits, and the three constructors of part_base unit use disjoint
  tagged encodings. NTP4VCAt reproduces integer-to-natural conversion and
  inhabited total list lookup. NTP4VCRebuild, NTP4VCLeftExtend, and
  NTP4VCRightExtend directly expand the source list definitions. Lower bounds,
  strict lower bounds, selection, and selection possibility are expanded
  definitionally over their complete source domains.

  NTP4VCComparison is exactly the internally existential integer witness whose
  positive, negative, and zero cases encode strict order in either direction
  and preorder equivalence. NTP4VCResultGuard is the exhaustive pair of option
  matches in the source antecedent, and NTP4VCResultConclusion is the
  exhaustive match on part_base unit. The result, comparison witnesses, split
  witnesses, elements, lists, and integers retain their original internal
  quantifier scopes.

  The source's first conjunct is an exhaustive match whose every leaf is True,
  so removing it uses only the bidirectional equivalence True /\ P <-> P.
  The polymorphic agg instances at unused types, the unused selector and t2
  values, and the unused positive balancing value are conservatively
  extendible; their nonempty carriers and the source balancing assumption are
  nevertheless retained below. The final $a declaration is Metamath's native
  unproved statement encoding; this database contains no $p proof declaration.
$)

$c
  NTP4VCNone NTP4VCSome NTP4VCOption
  NTP4VCSplitMk NTP4VCSplit NTP4VCSplitLeft
  NTP4VCSplitMiddle NTP4VCSplitRight
  NTP4VCOptionSeq NTP4VCRebuild
  NTP4VCLeftExtend NTP4VCRightExtend
  NTP4VCToNat NTP4VCAt NTP4VCTail NTP4VCOp
  NTP4VCLowerBound NTP4VCLowerBoundStrict
  NTP4VCSelected NTP4VCSelectionPossible
  NTP4VCHere NTP4VCLeft NTP4VCRight NTP4VCPartBase
  NTP4VCComparison NTP4VCResultGuard NTP4VCResultConclusion
$.

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
ntp4vc-left-extend-syntax
  $a class ( NTP4VCLeftExtend A B C ) $.
ntp4vc-right-extend-syntax
  $a class ( NTP4VCRightExtend A B C ) $.

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

ntp4vc-here-syntax $a class NTP4VCHere $.
ntp4vc-left-syntax $a class NTP4VCLeft $.
ntp4vc-right-syntax $a class NTP4VCRight $.
ntp4vc-part-base-syntax $a class NTP4VCPartBase $.

ntp4vc-comparison-syntax
  $a wff ( NTP4VCComparison A B C D ) $.
ntp4vc-result-guard-syntax
  $a wff ( NTP4VCResultGuard A B C D E F G H ) $.
ntp4vc-result-conclusion-syntax
  $a wff ( NTP4VCResultConclusion A B C D E F G H ) $.

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

ntp4vc-left-extend-def $a |- ( NTP4VCLeftExtend A B C ) =
  (
    NTP4VCSplitMk
      ( A ++ ( <" B "> ++ ( NTP4VCSplitLeft C ) ) )
      ( NTP4VCSplitMiddle C )
      ( NTP4VCSplitRight C )
  ) $.

ntp4vc-right-extend-def $a |- ( NTP4VCRightExtend A B C ) =
  (
    NTP4VCSplitMk
      ( NTP4VCSplitLeft A )
      ( NTP4VCSplitMiddle A )
      ( ( NTP4VCSplitRight A ) ++ ( <" B "> ++ C ) )
  ) $.

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

ntp4vc-here-def $a |- NTP4VCHere = <. 2 , 0 >. $.
ntp4vc-left-def $a |- NTP4VCLeft = <. 3 , 0 >. $.
ntp4vc-right-def $a |- NTP4VCRight = <. 4 , 0 >. $.

ntp4vc-part-base-def $a |- NTP4VCPartBase =
  { x |
    (
      x = NTP4VCHere
      \/
      (
        x = NTP4VCLeft
        \/
        x = NTP4VCRight
      )
    )
  } $.

ntp4vc-comparison-def $a |- (
  ( NTP4VCComparison A B C D )
  <->
  (
    (
      0 < C
      <->
      (
        <. A , B >. e. D
        /\
        -. <. B , A >. e. D
      )
    )
    /\
    (
      (
        C < 0
        <->
        (
          <. B , A >. e. D
          /\
          -. <. A , B >. e. D
        )
      )
      /\
      (
        C = 0
        <->
        (
          <. B , A >. e. D
          /\
          <. A , B >. e. D
        )
      )
    )
  )
) $.

${
  $d o p x y A B C D E F G H $.

  ntp4vc-result-guard-def $a |- (
    ( NTP4VCResultGuard A B C D E F G H )
    <->
    (
      (
        ( E ` C ) = NTP4VCNone
        /\
        (
          ( E ` D ) = NTP4VCNone
          /\
          A = NTP4VCHere
        )
      )
      \/
      (
        (
          ( E ` C ) = NTP4VCNone
          /\
          E. x e. H
            (
              ( E ` D ) = ( NTP4VCSome x )
              /\
              E. o e. ZZ
                (
                  ( NTP4VCComparison x ( F ` B ) o G )
                  /\
                  (
                    (
                      o < 0
                      /\
                      A = NTP4VCHere
                    )
                    \/
                    (
                      -. o < 0
                      /\
                      A = NTP4VCLeft
                    )
                  )
                )
            )
        )
        \/
        (
          (
            E. x e. H
              (
                ( E ` C ) = ( NTP4VCSome x )
                /\
                (
                  ( E ` D ) = NTP4VCNone
                  /\
                  E. o e. ZZ
                    (
                      ( NTP4VCComparison x ( F ` B ) o G )
                      /\
                      (
                        (
                          o <_ 0
                          /\
                          A = NTP4VCHere
                        )
                        \/
                        (
                          -. o <_ 0
                          /\
                          A = NTP4VCRight
                        )
                      )
                    )
                )
              )
          )
          \/
          E. x e. H
            E. y e. H
              (
                ( E ` C ) = ( NTP4VCSome x )
                /\
                (
                  ( E ` D ) = ( NTP4VCSome y )
                  /\
                  E. o e. ZZ
                    (
                      ( NTP4VCComparison x ( F ` B ) o G )
                      /\
                      (
                        (
                          o <_ 0
                          /\
                          E. p e. ZZ
                            (
                              (
                                NTP4VCComparison
                                  ( F ` B ) y p G
                              )
                              /\
                              (
                                (
                                  p <_ 0
                                  /\
                                  A = NTP4VCLeft
                                )
                                \/
                                (
                                  -. p <_ 0
                                  /\
                                  A = NTP4VCHere
                                )
                              )
                            )
                        )
                        \/
                        (
                          -. o <_ 0
                          /\
                          E. p e. ZZ
                            (
                              ( NTP4VCComparison x y p G )
                              /\
                              (
                                (
                                  p <_ 0
                                  /\
                                  A = NTP4VCLeft
                                )
                                \/
                                (
                                  -. p <_ 0
                                  /\
                                  A = NTP4VCRight
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
  $d e A B C D E F G H $.

  ntp4vc-result-conclusion-def $a |- (
    ( NTP4VCResultConclusion A B C D E F G H )
    <->
    (
      (
        A = NTP4VCHere
        ->
        (
          NTP4VCSelected
            ( NTP4VCSplitMk D ( NTP4VCSome B ) C )
            E F G H
        )
      )
      /\
      (
        (
          A = NTP4VCLeft
          ->
          (
            ( NTP4VCSelectionPossible D )
            /\
            A. e e. ( NTP4VCSplit E )
              (
                (
                  ( NTP4VCSelected e E F G H )
                  /\
                  ( NTP4VCRebuild e ) = D
                )
                ->
                (
                  NTP4VCSelected
                    ( NTP4VCRightExtend e B C )
                    E F G H
                )
              )
          )
        )
        /\
        (
          A = NTP4VCRight
          ->
          (
            ( NTP4VCSelectionPossible C )
            /\
            A. e e. ( NTP4VCSplit E )
              (
                (
                  ( NTP4VCSelected e E F G H )
                  /\
                  ( NTP4VCRebuild e ) = C
                )
                ->
                (
                  NTP4VCSelected
                    ( NTP4VCLeftExtend D B e )
                    E F G H
                )
              )
          )
        )
      )
    )
  ) $.
$}

${
  $d d l o p r s x y z
     A B C D E F G H I J K L M N O P Q R S T U V W X Y Z $.

  ntp4vc-element-carrier-nonempty $e |- U =/= (/) $.
  ntp4vc-key-carrier-nonempty $e |- Y =/= (/) $.
  ntp4vc-t2-carrier-nonempty $e |- Z =/= (/) $.
  ntp4vc-selector-carrier-nonempty $e |- S =/= (/) $.
  ntp4vc-default-element $e |- H e. U $.

  ntp4vc-balancing-positive-natural $e |- B e. NN $.

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

  $( Source theorem parameters: A=d, E=rseq, and F=lseq. $)
  ntp4vc-d-type $e |- A e. U $.
  ntp4vc-rseq-type $e |- E e. Word U $.
  ntp4vc-lseq-type $e |- F e. Word U $.

  ntp4vc-pearl-priority-queue-selected-part-vc $a |- (
    A. r e. NTP4VCPartBase
      (
        ( NTP4VCResultGuard r A E F Q C D Y )
        ->
        ( NTP4VCResultConclusion r A E F U C D H )
      )
  ) $.
$}
