$(
  Statement-only formalization of the NTP4VC corpus artifact
  pearl/koda_ruskey_KodaRuskey_enumqtvc: the Koda-Ruskey enumeration
  verification condition preserves forest-stack, coloring, inverse, and
  stored-solution invariants through the empty-tree and binary-node
  recursion branches. This file contains no proof.
$)

$[ lib/set.mm $]

$(
  NTP4VCForest is exactly the source inductive carrier forest, with empty
  constructor NTP4VCE and node constructor NTP4VCN. Constructor closure,
  exhaustiveness, and structural induction characterize all and only finite
  well-founded constructor trees. Colors are exactly SetMM's two-element
  carrier 2, with White = 0 and Black = 1. Words over these carriers are the
  source finite lists, and ( 2 ^m ZZ ) is the full source coloring-function
  space.

  The displayed equations completely characterize the source recursive
  functions and predicates size_forest, mem_forest, no_repeated_forest,
  white_forest, valid_coloring, count_forest, mem_stack, size_stack,
  even_forest, final_forest, inverse, any_stack, and count_stack.
  NTP4VCSub is the least relation closed under the three source sub
  constructors. The remaining biconditional definitions expand
  valid_nums_forest, stored_solutions, totalized list lookup, List.set,
  Function.update, and the repeated recursive-call contracts.

  Proposition-valued source matches and conditionals are represented by
  exhaustive constructor implications and guarded then/else implications.
  All integer, forest, list, coloring-function, and internally existential
  constructor witnesses retain their source domains and scopes. The final
  $a declaration is Metamath's native unproved statement encoding; every
  other $a declaration is syntax or a faithful definition, and this database
  contains no $p proof declaration.
$)

$c
  NTP4VCForest NTPVCE NTPVCN
  NTPVCToNat NTPVCAt NTPVCSet NTPVCColoring NTPVCDefaultColoring
  NTPVCSizeForest NTPVCMemForest NTPVCNoRepeated
  NTPVCWhiteForest NTPVCValidColoring NTPVCCountForest
  NTPVCMemStack NTPVCSizeStack NTPVCEvenForest NTPVCFinalForest
  NTPVCInverse NTPVCAnyStack NTPVCCountStack NTPVCSub
  NTPVCValidNums NTPVCEqColoring NTPVCStoredSolutions
  NTPVCUpdateLaw NTPVCTail NTPVCProgress NTPVCStep
  NTPVCContract NTPVCRecurse NTPVCEBranch
  NTPVCWhiteBranch NTPVCBlackBranch NTPVCNodeBranch NTPVCEnumBody
$.

ntpvc-forest-syntax $a class NTP4VCForest $.
ntpvc-e-syntax $a class NTPVCE $.
ntpvc-n-syntax $a class ( NTPVCN A B C ) $.
ntpvc-to-nat-syntax $a class ( NTPVCToNat A ) $.
ntpvc-at-syntax $a class ( NTPVCAt A B C ) $.
ntpvc-set-syntax $a class ( NTPVCSet A B C ) $.
ntpvc-coloring-syntax $a class ( NTPVCColoring A B ) $.
ntpvc-default-coloring-syntax
  $a class ( NTPVCDefaultColoring A ) $.
ntpvc-size-forest-syntax $a class NTPVCSizeForest $.
ntpvc-mem-forest-syntax $a class NTPVCMemForest $.
ntpvc-no-repeated-syntax $a class NTPVCNoRepeated $.
ntpvc-white-forest-syntax $a class NTPVCWhiteForest $.
ntpvc-valid-coloring-syntax $a class NTPVCValidColoring $.
ntpvc-count-forest-syntax $a class NTPVCCountForest $.
ntpvc-mem-stack-syntax $a class NTPVCMemStack $.
ntpvc-size-stack-syntax $a class NTPVCSizeStack $.
ntpvc-even-forest-syntax $a class NTPVCEvenForest $.
ntpvc-final-forest-syntax $a class NTPVCFinalForest $.
ntpvc-inverse-syntax $a class NTPVCInverse $.
ntpvc-any-stack-syntax $a class NTPVCAnyStack $.
ntpvc-count-stack-syntax $a class NTPVCCountStack $.
ntpvc-sub-syntax $a class NTPVCSub $.

ntpvc-valid-nums-syntax
  $a wff ( NTPVCValidNums A B ) $.
ntpvc-eq-coloring-syntax
  $a wff ( NTPVCEqColoring A B C ) $.
ntpvc-stored-solutions-syntax
  $a wff ( NTPVCStoredSolutions A B C D E F ) $.
ntpvc-update-law-syntax
  $a wff ( NTPVCUpdateLaw A B C D E ) $.
ntpvc-tail-syntax $a wff ( NTPVCTail A B ) $.
ntpvc-progress-syntax
  $a wff ( NTPVCProgress A B ) $.
ntpvc-step-syntax
  $a wff ( NTPVCStep A B C D E ) $.
ntpvc-contract-syntax
  $a wff ( NTPVCContract A B C D E F G ) $.
ntpvc-recurse-syntax
  $a wff ( NTPVCRecurse A B C D E F ) $.
ntpvc-e-branch-syntax
  $a wff ( NTPVCEBranch A B C D E F ) $.
ntpvc-white-branch-syntax
  $a wff ( NTPVCWhiteBranch A B C D E F G H I ) $.
ntpvc-black-branch-syntax
  $a wff ( NTPVCBlackBranch A B C D E F G H I ) $.
ntpvc-node-branch-syntax
  $a wff ( NTPVCNodeBranch A B C D E F G H I ) $.
ntpvc-enum-body-syntax
  $a wff ( NTPVCEnumBody A B C D E ) $.

ntpvc-e-definition $a |- NTPVCE = <. 0 , (/) >. $.

ntpvc-n-definition $a |- (
  NTPVCN A B C
) = <. 1 , <. A , <. B , C >. >. $.

ntpvc-to-nat-definition $a |- (
  NTPVCToNat A
) = if (
  0 <_ A ,
  A ,
  0
) $.

ntpvc-at-definition $a |- (
  NTPVCAt A B C
) = if (
  ( NTPVCToNat C ) < ( # ` A ) ,
  ( A ` ( NTPVCToNat C ) ) ,
  B
) $.

${
  $d k A B C $.

  ntpvc-set-definition $a |- (
    NTPVCSet A B C
  ) = (
    k e. ( 0 ..^ ( # ` A ) ) |->
      if (
        k = ( NTPVCToNat B ) ,
        C ,
        ( A ` k )
      )
  ) $.
$}

${
  $d k A B $.

  ntpvc-coloring-definition $a |- (
    NTPVCColoring A B
  ) = (
    k e. ZZ |-> ( NTPVCAt A B k )
  ) $.
$}

${
  $d k A $.

  ntpvc-default-coloring-definition $a |- (
    NTPVCDefaultColoring A
  ) = (
    k e. ZZ |-> A
  ) $.
$}

${
  $d i A B C D E $.

  ntpvc-valid-nums-definition $a |- (
    ( NTPVCValidNums A B )
    <->
    (
      A. i e. ZZ
        (
          <. i , A >. e. NTPVCMemForest
          ->
          (
            0 <_ i
            /\
            i < B
          )
        )
      /\
      A e. NTPVCNoRepeated
    )
  ) $.
$}

${
  $d i A B C $.

  ntpvc-eq-coloring-definition $a |- (
    ( NTPVCEqColoring A B C )
    <->
    A. i e. ZZ
      (
        (
          0 <_ i
          /\
          i < A
        )
        ->
        ( B ` i ) = ( C ` i )
      )
  ) $.
$}

${
  $d i j k A B C D E F $.

  $(
    A=f0, B=bits, C=stack, D=old visited, E=new visited, and
    F is the arbitrary inhabited default color.
  $)
  ntpvc-stored-solutions-definition $a |- (
    ( NTPVCStoredSolutions A B C D E F )
    <->
    (
      (
        ( # ` E ) - ( # ` D )
      ) = (
        NTPVCCountStack ` C
      )
      /\
      (
        A. j e. ZZ
          (
            (
              0 <_ j
              /\
              j < ( # ` D )
            )
            ->
            (
              NTPVCEqColoring
                ( NTPVCSizeForest ` A )
                (
                  NTPVCAt
                    E
                    ( NTPVCDefaultColoring F )
                    j
                )
                (
                  NTPVCAt
                    D
                    ( NTPVCDefaultColoring F )
                    j
                )
            )
          )
        /\
        A. j e. ZZ
          (
            (
              ( # ` D ) <_ j
              /\
              j < ( # ` E )
            )
            ->
            (
              <.
                A ,
                (
                  NTPVCAt
                    E
                    ( NTPVCDefaultColoring F )
                    j
                )
              >. e. NTPVCValidColoring
              /\
              (
                A. i e. ZZ
                  (
                    (
                      (
                        0 <_ i
                        /\
                        i < ( NTPVCSizeForest ` A )
                      )
                      /\
                      -.
                      <. i , C >. e. NTPVCMemStack
                    )
                    ->
                    (
                      (
                        NTPVCAt
                          E
                          ( NTPVCDefaultColoring F )
                          j
                      ) ` i
                    ) = ( B ` i )
                  )
                /\
                A. k e. ZZ
                  (
                    (
                      (
                        ( # ` D ) <_ k
                        /\
                        k < ( # ` E )
                      )
                      /\
                      j =/= k
                    )
                    ->
                    -.
                    (
                      NTPVCEqColoring
                        ( NTPVCSizeForest ` A )
                        (
                          NTPVCAt
                            E
                            ( NTPVCDefaultColoring F )
                            j
                        )
                        (
                          NTPVCAt
                            E
                            ( NTPVCDefaultColoring F )
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
$}

${
  $d k A B C D E $.

  ntpvc-update-law-definition $a |- (
    ( NTPVCUpdateLaw A B C D E )
    <->
    A. k e. ( 0 ..^ ( # ` B ) )
      (
        ( NTPVCAt A C k )
        =
        if (
          k = D ,
          E ,
          ( NTPVCAt B C k )
        )
      )
  ) $.
$}

${
  $d h A B $.

  ntpvc-tail-definition $a |- (
    ( NTPVCTail A B )
    <->
    E. h e. NTP4VCForest
      A = ( <" h "> ++ B )
  ) $.
$}

ntpvc-progress-definition $a |- (
  ( NTPVCProgress A B )
  <->
  (
    (
      0 <_ ( NTPVCSizeStack ` A )
      /\
      ( NTPVCSizeStack ` B ) < ( NTPVCSizeStack ` A )
    )
    \/
    (
      ( NTPVCSizeStack ` A ) = ( NTPVCSizeStack ` B )
      /\
      ( NTPVCTail A B )
    )
  )
) $.

ntpvc-step-definition $a |- (
  ( NTPVCStep A B C D E )
  <->
  (
    ( NTPVCProgress C D )
    /\
    (
      ( NTPVCSizeForest ` A ) = ( # ` B )
      /\
      (
        ( NTPVCValidNums A ( # ` B ) )
        /\
        (
          <.
            D ,
            <. A , ( NTPVCColoring B E ) >.
          >. e. NTPVCSub
          /\
          (
            <. D , ( NTPVCColoring B E ) >. e. NTPVCAnyStack
            /\
            <. A , ( NTPVCColoring B E ) >.
              e. NTPVCValidColoring
          )
        )
      )
    )
  )
) $.

${
  $d i A B C D E F G $.

  $(
    A=f0, B=start bits, C=start stack, D=start visited,
    E=result bits, F=result visited, and G=default color.
  $)
  ntpvc-contract-definition $a |- (
    ( NTPVCContract A B C D E F G )
    <->
    (
      A. i e. ZZ
        (
          -.
          <. i , C >. e. NTPVCMemStack
          ->
          ( NTPVCAt E G i ) = ( NTPVCAt B G i )
        )
      /\
      (
        <.
          C ,
          <.
            ( NTPVCColoring B G ) ,
            ( NTPVCColoring E G )
          >.
        >. e. NTPVCInverse
        /\
        (
          <. A , ( NTPVCColoring E G ) >.
            e. NTPVCValidColoring
          /\
          (
            NTPVCStoredSolutions
              A ( NTPVCColoring E G ) C D F G
          )
        )
      )
    )
  ) $.
$}

${
  $d b v A B C D E F $.

  $(
    A=f0, B=bits, C=old stack, D=new stack, E=visited,
    and F=default color.
  $)
  ntpvc-recurse-definition $a |- (
    ( NTPVCRecurse A B C D E F )
    <->
    A. b e. ( Word 2 )
      A. v e. ( Word ( 2 ^m ZZ ) )
        (
          ( # ` b ) = ( # ` B )
          ->
          (
            ( NTPVCContract A B D E b v F )
            ->
            ( NTPVCContract A B C E b v F )
          )
        )
  ) $.
$}

${
  $d i A B C D E F $.

  $(
    A=f0, B=bits, C=the original stack, D=visited,
    E=the tail after E, and F=default color.
  $)
  ntpvc-e-branch-definition $a |- (
    ( NTPVCEBranch A B C D E F )
    <->
    (
      (
        E = (/)
        ->
        (
          (
            (
              # `
              (
                D ++ <" ( NTPVCColoring B F ) ">
              )
            ) = ( 1 + ( # ` D ) )
            /\
            (
              (
                (
                  D ++ <" ( NTPVCColoring B F ) ">
                ) ` ( # ` D )
              ) = ( NTPVCColoring B F )
              /\
              A. i e. ZZ
                (
                  (
                    0 <_ i
                    /\
                    i < ( # ` D )
                  )
                  ->
                  (
                    (
                      NTPVCAt
                        ( D ++ <" ( NTPVCColoring B F ) "> )
                        ( NTPVCDefaultColoring F )
                        i
                    )
                    =
                    (
                      NTPVCAt
                        D
                        ( NTPVCDefaultColoring F )
                        i
                    )
                  )
                )
            )
          )
          ->
          (
            <.
              C ,
              <.
                ( NTPVCColoring B F ) ,
                ( NTPVCColoring B F )
              >.
            >. e. NTPVCInverse
            /\
            (
              <. A , ( NTPVCColoring B F ) >.
                e. NTPVCValidColoring
              /\
              (
                NTPVCStoredSolutions
                  A
                  ( NTPVCColoring B F )
                  C
                  D
                  ( D ++ <" ( NTPVCColoring B F ) "> )
                  F
              )
            )
          )
        )
      )
      /\
      (
        E =/= (/)
        ->
        (
          ( NTPVCStep A B C E F )
          /\
          (
            E =/= (/)
            /\
            ( NTPVCRecurse A B C E D F )
          )
        )
      )
    )
  ) $.
$}

${
  $d b v p q A B C D E F G H I $.

  $(
    A=f0, B=bits, C=original stack, D=visited, E=node index,
    F=left forest, G=right forest, H=stack tail, I=default color.
  $)
  ntpvc-white-branch-definition $a |- (
    ( NTPVCWhiteBranch A B C D E F G H I )
    <->
    (
      (
        NTPVCStep
          A B C ( <" G "> ++ H ) I
      )
      /\
      A. b e. ( Word 2 )
        A. v e. ( Word ( 2 ^m ZZ ) )
          (
            ( # ` b ) = ( # ` B )
            ->
            (
              (
                NTPVCContract
                  A B ( <" G "> ++ H ) D b v I
              )
              ->
              (
                (
                  0 <_ E
                  /\
                  E < ( # ` b )
                )
                /\
                (
                  (
                    # ` ( NTPVCSet b E 1 )
                  ) = ( # ` b )
                  ->
                  (
                    ( NTPVCUpdateLaw ( NTPVCSet b E 1 ) b I E 1 )
                    ->
                    (
                      (
                        NTPVCStep
                          A
                          ( NTPVCSet b E 1 )
                          C
                          ( <" F "> ++ ( <" G "> ++ H ) )
                          I
                      )
                      /\
                      A. p e. ( Word 2 )
                        A. q e. ( Word ( 2 ^m ZZ ) )
                          (
                            ( # ` p ) =
                              ( # ` ( NTPVCSet b E 1 ) )
                            ->
                            (
                              (
                                NTPVCContract
                                  A
                                  ( NTPVCSet b E 1 )
                                  ( <" F "> ++ ( <" G "> ++ H ) )
                                  v p q I
                              )
                              ->
                              ( NTPVCContract A B C D p q I )
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
  $d b v p q A B C D E F G H I $.

  $(
    Arguments are as for NTPVCWhiteBranch. This is the source else branch,
    which writes White and recurses on the right forest.
  $)
  ntpvc-black-branch-definition $a |- (
    ( NTPVCBlackBranch A B C D E F G H I )
    <->
    (
      (
        NTPVCStep
          A B C ( <" F "> ++ ( <" G "> ++ H ) ) I
      )
      /\
      A. b e. ( Word 2 )
        A. v e. ( Word ( 2 ^m ZZ ) )
          (
            ( # ` b ) = ( # ` B )
            ->
            (
              (
                NTPVCContract
                  A B ( <" F "> ++ ( <" G "> ++ H ) ) D b v I
              )
              ->
              (
                (
                  0 <_ E
                  /\
                  E < ( # ` b )
                )
                /\
                (
                  (
                    # ` ( NTPVCSet b E 0 )
                  ) = ( # ` b )
                  ->
                  (
                    ( NTPVCUpdateLaw ( NTPVCSet b E 0 ) b I E 0 )
                    ->
                    (
                      (
                        NTPVCStep
                          A
                          ( NTPVCSet b E 0 )
                          C
                          ( <" G "> ++ H )
                          I
                      )
                      /\
                      A. p e. ( Word 2 )
                        A. q e. ( Word ( 2 ^m ZZ ) )
                          (
                            ( # ` p ) =
                              ( # ` ( NTPVCSet b E 0 ) )
                            ->
                            (
                              (
                                NTPVCContract
                                  A
                                  ( NTPVCSet b E 0 )
                                  ( <" G "> ++ H )
                                  v p q I
                              )
                              ->
                              ( NTPVCContract A B C D p q I )
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

ntpvc-node-branch-definition $a |- (
  ( NTPVCNodeBranch A B C D E F G H I )
  <->
  (
    (
      0 <_ E
      /\
      E < ( # ` B )
    )
    /\
    (
      (
        ( NTPVCAt B I E ) = 0
        ->
        ( NTPVCWhiteBranch A B C D E F G H I )
      )
      /\
      (
        ( NTPVCAt B I E ) =/= 0
        ->
        ( NTPVCBlackBranch A B C D E F G H I )
      )
    )
  )
) $.

${
  $d i f g t A B C D E $.

  $(
    A=f0, B=bits, C=stack, D=visited, and E=default color.
    The three implications are the exhaustive source match on stack.
  $)
  ntpvc-enum-body-definition $a |- (
    ( NTPVCEnumBody A B C D E )
    <->
    (
      (
        C = (/)
        ->
        (/) =/= (/)
      )
      /\
      (
        A. t e. ( Word NTP4VCForest )
          (
            C = ( <" NTPVCE "> ++ t )
            ->
            ( NTPVCEBranch A B C D t E )
          )
        /\
        A. i e. ZZ
          A. f e. NTP4VCForest
            A. g e. NTP4VCForest
              A. t e. ( Word NTP4VCForest )
                (
                  C = ( <" ( NTPVCN i f g ) "> ++ t )
                  ->
                  (
                    NTPVCNodeBranch
                      A B C D i f g t E
                  )
                )
      )
    )
  ) $.
$}

${
  $d
    b c f g h i j k n p q r s t v x y z
    A B C D E F G H I J K L M N O P Q R S T U V W X Y Z
  $.

  $( Exact source forest datatype. $)
  ntpvc-forest-e-closure $e |- NTPVCE e. NTP4VCForest $.

  ntpvc-forest-n-closure $e |-
    A. i e. ZZ
      A. f e. NTP4VCForest
        A. g e. NTP4VCForest
          ( NTPVCN i f g ) e. NTP4VCForest $.

  ntpvc-forest-exhaustive $e |-
    A. f e. NTP4VCForest
      (
        f = NTPVCE
        \/
        E. i e. ZZ
          E. g e. NTP4VCForest
            E. h e. NTP4VCForest
              f = ( NTPVCN i g h )
      ) $.

  ntpvc-forest-structural-induction $e |-
    A. s e. ~P NTP4VCForest
      (
        (
          NTPVCE e. s
          /\
          A. i e. ZZ
            A. f e. NTP4VCForest
              A. g e. NTP4VCForest
                (
                  (
                    f e. s
                    /\
                    g e. s
                  )
                  ->
                  ( NTPVCN i f g ) e. s
                )
        )
        ->
        s = NTP4VCForest
      ) $.

  $( Complete recursive size_forest definition. $)
  ntpvc-size-forest-function $e |-
    NTPVCSizeForest e. ( ZZ ^m NTP4VCForest ) $.
  ntpvc-size-forest-e $e |-
    ( NTPVCSizeForest ` NTPVCE ) = 0 $.
  ntpvc-size-forest-n $e |-
    A. i e. ZZ
      A. f e. NTP4VCForest
        A. g e. NTP4VCForest
          (
            NTPVCSizeForest ` ( NTPVCN i f g )
          ) = (
            ( 1 + ( NTPVCSizeForest ` f ) )
            +
            ( NTPVCSizeForest ` g )
          ) $.

  $( Complete recursive mem_forest definition. $)
  ntpvc-mem-forest-relation $e |-
    NTPVCMemForest C_ ( ZZ X. NTP4VCForest ) $.
  ntpvc-mem-forest-e $e |-
    A. n e. ZZ
      -. <. n , NTPVCE >. e. NTPVCMemForest $.
  ntpvc-mem-forest-n $e |-
    A. n e. ZZ
      A. i e. ZZ
        A. f e. NTP4VCForest
          A. g e. NTP4VCForest
            (
              <. n , ( NTPVCN i f g ) >. e. NTPVCMemForest
              <->
              (
                i = n
                \/
                (
                  <. n , f >. e. NTPVCMemForest
                  \/
                  <. n , g >. e. NTPVCMemForest
                )
              )
            ) $.

  $( Complete recursive no_repeated_forest definition. $)
  ntpvc-no-repeated-predicate $e |-
    NTPVCNoRepeated C_ NTP4VCForest $.
  ntpvc-no-repeated-e $e |-
    NTPVCE e. NTPVCNoRepeated $.
  ntpvc-no-repeated-n $e |-
    A. i e. ZZ
      A. f e. NTP4VCForest
        A. g e. NTP4VCForest
          (
            ( NTPVCN i f g ) e. NTPVCNoRepeated
            <->
            (
              (
                f e. NTPVCNoRepeated
                /\
                g e. NTPVCNoRepeated
              )
              /\
              (
                (
                  -. <. i , f >. e. NTPVCMemForest
                  /\
                  -. <. i , g >. e. NTPVCMemForest
                )
                /\
                A. n e. ZZ
                  (
                    <. n , f >. e. NTPVCMemForest
                    ->
                    -. <. n , g >. e. NTPVCMemForest
                  )
              )
            )
          ) $.

  $( Complete recursive white_forest definition. $)
  ntpvc-white-forest-relation $e |-
    NTPVCWhiteForest C_
      ( NTP4VCForest X. ( 2 ^m ZZ ) ) $.
  ntpvc-white-forest-e $e |-
    A. c e. ( 2 ^m ZZ )
      <. NTPVCE , c >. e. NTPVCWhiteForest $.
  ntpvc-white-forest-n $e |-
    A. i e. ZZ
      A. f e. NTP4VCForest
        A. g e. NTP4VCForest
          A. c e. ( 2 ^m ZZ )
            (
              <. ( NTPVCN i f g ) , c >. e. NTPVCWhiteForest
              <->
              (
                ( c ` i ) = 0
                /\
                (
                  <. f , c >. e. NTPVCWhiteForest
                  /\
                  <. g , c >. e. NTPVCWhiteForest
                )
              )
            ) $.

  $( Complete recursive valid_coloring definition. $)
  ntpvc-valid-coloring-relation $e |-
    NTPVCValidColoring C_
      ( NTP4VCForest X. ( 2 ^m ZZ ) ) $.
  ntpvc-valid-coloring-e $e |-
    A. c e. ( 2 ^m ZZ )
      <. NTPVCE , c >. e. NTPVCValidColoring $.
  ntpvc-valid-coloring-n $e |-
    A. i e. ZZ
      A. f e. NTP4VCForest
        A. g e. NTP4VCForest
          A. c e. ( 2 ^m ZZ )
            (
              <. ( NTPVCN i f g ) , c >. e. NTPVCValidColoring
              <->
              (
                <. g , c >. e. NTPVCValidColoring
                /\
                (
                  (
                    ( c ` i ) = 0
                    /\
                    <. f , c >. e. NTPVCWhiteForest
                  )
                  \/
                  (
                    ( c ` i ) = 1
                    /\
                    <. f , c >. e. NTPVCValidColoring
                  )
                )
              )
            ) $.

  $( Complete recursive count_forest definition. $)
  ntpvc-count-forest-function $e |-
    NTPVCCountForest e. ( ZZ ^m NTP4VCForest ) $.
  ntpvc-count-forest-e $e |-
    ( NTPVCCountForest ` NTPVCE ) = 1 $.
  ntpvc-count-forest-n $e |-
    A. i e. ZZ
      A. f e. NTP4VCForest
        A. g e. NTP4VCForest
          (
            NTPVCCountForest ` ( NTPVCN i f g )
          ) = (
            (
              1 + ( NTPVCCountForest ` f )
            ) x. (
              NTPVCCountForest ` g
            )
          ) $.

  $( Complete recursive stack operations. $)
  ntpvc-mem-stack-relation $e |-
    NTPVCMemStack C_
      ( ZZ X. ( Word NTP4VCForest ) ) $.
  ntpvc-mem-stack-empty $e |-
    A. n e. ZZ
      -. <. n , (/) >. e. NTPVCMemStack $.
  ntpvc-mem-stack-cons $e |-
    A. n e. ZZ
      A. f e. NTP4VCForest
        A. t e. ( Word NTP4VCForest )
          (
            <. n , ( <" f "> ++ t ) >. e. NTPVCMemStack
            <->
            (
              <. n , f >. e. NTPVCMemForest
              \/
              <. n , t >. e. NTPVCMemStack
            )
          ) $.

  ntpvc-size-stack-function $e |-
    NTPVCSizeStack e.
      ( ZZ ^m ( Word NTP4VCForest ) ) $.
  ntpvc-size-stack-empty $e |-
    ( NTPVCSizeStack ` (/) ) = 0 $.
  ntpvc-size-stack-cons $e |-
    A. f e. NTP4VCForest
      A. t e. ( Word NTP4VCForest )
        (
          NTPVCSizeStack ` ( <" f "> ++ t )
        ) = (
          ( NTPVCSizeForest ` f )
          +
          ( NTPVCSizeStack ` t )
        ) $.

  ntpvc-count-stack-function $e |-
    NTPVCCountStack e.
      ( ZZ ^m ( Word NTP4VCForest ) ) $.
  ntpvc-count-stack-empty $e |-
    ( NTPVCCountStack ` (/) ) = 1 $.
  ntpvc-count-stack-cons $e |-
    A. f e. NTP4VCForest
      A. t e. ( Word NTP4VCForest )
        (
          NTPVCCountStack ` ( <" f "> ++ t )
        ) = (
          ( NTPVCCountForest ` f )
          x.
          ( NTPVCCountStack ` t )
        ) $.

  $( Complete recursive even_forest and final_forest definitions. $)
  ntpvc-even-forest-predicate $e |-
    NTPVCEvenForest C_ NTP4VCForest $.
  ntpvc-even-forest-e $e |-
    -. NTPVCE e. NTPVCEvenForest $.
  ntpvc-even-forest-n $e |-
    A. i e. ZZ
      A. f e. NTP4VCForest
        A. g e. NTP4VCForest
          (
            ( NTPVCN i f g ) e. NTPVCEvenForest
            <->
            (
              -. f e. NTPVCEvenForest
              \/
              g e. NTPVCEvenForest
            )
          ) $.

  ntpvc-final-forest-relation $e |-
    NTPVCFinalForest C_
      ( NTP4VCForest X. ( 2 ^m ZZ ) ) $.
  ntpvc-final-forest-e $e |-
    A. c e. ( 2 ^m ZZ )
      <. NTPVCE , c >. e. NTPVCFinalForest $.
  ntpvc-final-forest-n $e |-
    A. i e. ZZ
      A. f e. NTP4VCForest
        A. g e. NTP4VCForest
          A. c e. ( 2 ^m ZZ )
            (
              <. ( NTPVCN i f g ) , c >. e. NTPVCFinalForest
              <->
              (
                ( c ` i ) = 1
                /\
                (
                  <. f , c >. e. NTPVCFinalForest
                  /\
                  (
                    (
                      -. f e. NTPVCEvenForest
                      ->
                      <. g , c >. e. NTPVCWhiteForest
                    )
                    /\
                    (
                      f e. NTPVCEvenForest
                      ->
                      <. g , c >. e. NTPVCFinalForest
                    )
                  )
                )
              )
            ) $.

  $( Complete recursive inverse and any_stack definitions. $)
  ntpvc-inverse-relation $e |-
    NTPVCInverse C_
      (
        ( Word NTP4VCForest )
        X.
        ( ( 2 ^m ZZ ) X. ( 2 ^m ZZ ) )
      ) $.
  ntpvc-inverse-empty $e |-
    A. c e. ( 2 ^m ZZ )
      A. b e. ( 2 ^m ZZ )
        <. (/) , <. c , b >. >. e. NTPVCInverse $.
  ntpvc-inverse-cons $e |-
    A. f e. NTP4VCForest
      A. t e. ( Word NTP4VCForest )
        A. c e. ( 2 ^m ZZ )
          A. b e. ( 2 ^m ZZ )
            (
              <. ( <" f "> ++ t ) , <. c , b >. >.
                e. NTPVCInverse
              <->
              (
                (
                  (
                    <. f , c >. e. NTPVCWhiteForest
                    /\
                    <. f , b >. e. NTPVCFinalForest
                  )
                  \/
                  (
                    <. f , c >. e. NTPVCFinalForest
                    /\
                    <. f , b >. e. NTPVCWhiteForest
                  )
                )
                /\
                (
                  (
                    f e. NTPVCEvenForest
                    ->
                    A. i e. ZZ
                      (
                        <. i , t >. e. NTPVCMemStack
                        ->
                        ( c ` i ) = ( b ` i )
                      )
                  )
                  /\
                  (
                    -. f e. NTPVCEvenForest
                    ->
                    <. t , <. c , b >. >. e. NTPVCInverse
                  )
                )
              )
            ) $.

  ntpvc-any-stack-relation $e |-
    NTPVCAnyStack C_
      ( ( Word NTP4VCForest ) X. ( 2 ^m ZZ ) ) $.
  ntpvc-any-stack-empty $e |-
    A. c e. ( 2 ^m ZZ )
      <. (/) , c >. e. NTPVCAnyStack $.
  ntpvc-any-stack-cons $e |-
    A. f e. NTP4VCForest
      A. t e. ( Word NTP4VCForest )
        A. c e. ( 2 ^m ZZ )
          (
            <. ( <" f "> ++ t ) , c >. e. NTPVCAnyStack
            <->
            (
              (
                <. f , c >. e. NTPVCWhiteForest
                \/
                <. f , c >. e. NTPVCFinalForest
              )
              /\
              <. t , c >. e. NTPVCAnyStack
            )
          ) $.

  $( Exact least source relation sub. $)
  ntpvc-sub-relation $e |-
    NTPVCSub C_
      (
        ( Word NTP4VCForest )
        X.
        ( NTP4VCForest X. ( 2 ^m ZZ ) )
      ) $.

  ntpvc-sub-reflex $e |-
    A. f e. NTP4VCForest
      A. c e. ( 2 ^m ZZ )
        <. <" f "> , <. f , c >. >. e. NTPVCSub $.

  ntpvc-sub-brother $e |-
    A. t e. ( Word NTP4VCForest )
      A. g e. NTP4VCForest
        A. c e. ( 2 ^m ZZ )
          A. i e. ZZ
            A. f e. NTP4VCForest
              (
                <. t , <. g , c >. >. e. NTPVCSub
                ->
                <. t , <. ( NTPVCN i f g ) , c >. >.
                  e. NTPVCSub
              ) $.

  ntpvc-sub-append $e |-
    A. t e. ( Word NTP4VCForest )
      A. f e. NTP4VCForest
        A. c e. ( 2 ^m ZZ )
          A. i e. ZZ
            A. g e. NTP4VCForest
              (
                (
                  <. t , <. f , c >. >. e. NTPVCSub
                  /\
                  ( c ` i ) = 1
                )
                ->
                <.
                  ( t ++ <" g "> ) ,
                  <. ( NTPVCN i f g ) , c >.
                >. e. NTPVCSub
              ) $.

  ntpvc-sub-induction $e |-
    A. s e. ~P NTPVCSub
      (
        (
          (
            A. f e. NTP4VCForest
              A. c e. ( 2 ^m ZZ )
                <. <" f "> , <. f , c >. >. e. s
          )
          /\
          (
            A. t e. ( Word NTP4VCForest )
              A. g e. NTP4VCForest
                A. c e. ( 2 ^m ZZ )
                  A. i e. ZZ
                    A. f e. NTP4VCForest
                      (
                        <. t , <. g , c >. >. e. s
                        ->
                        <. t , <. ( NTPVCN i f g ) , c >. >.
                          e. s
                      )
          )
          /\
          A. t e. ( Word NTP4VCForest )
            A. f e. NTP4VCForest
              A. c e. ( 2 ^m ZZ )
                A. i e. ZZ
                  A. g e. NTP4VCForest
                    (
                      (
                        <. t , <. f , c >. >. e. s
                        /\
                        ( c ` i ) = 1
                      )
                      ->
                      <.
                        ( t ++ <" g "> ) ,
                        <. ( NTPVCN i f g ) , c >.
                      >. e. s
                    )
        )
        ->
        s = NTPVCSub
      ) $.

  $( Source theorem parameters and assumptions. $)
  ntpvc-f0-type $e |- A e. NTP4VCForest $.
  ntpvc-bits-type $e |- B e. ( Word 2 ) $.
  ntpvc-stack-type $e |- C e. ( Word NTP4VCForest ) $.
  ntpvc-visited-type $e |- D e. ( Word ( 2 ^m ZZ ) ) $.
  ntpvc-default-color-type $e |- E e. 2 $.

  ntpvc-fact0 $e |-
    ( NTPVCSizeForest ` A ) = ( # ` B ) $.
  ntpvc-fact1 $e |-
    ( NTPVCValidNums A ( # ` B ) ) $.
  ntpvc-fact2 $e |-
    <. C , <. A , ( NTPVCColoring B E ) >. >.
      e. NTPVCSub $.
  ntpvc-fact3 $e |- C =/= (/) $.
  ntpvc-fact4 $e |-
    <. C , ( NTPVCColoring B E ) >. e. NTPVCAnyStack $.
  ntpvc-fact5 $e |-
    <. A , ( NTPVCColoring B E ) >.
      e. NTPVCValidColoring $.

  ntpvc-pearl-koda-ruskey-enum-vc $a |-
    ( NTPVCEnumBody A B C D E ) $.
$}
