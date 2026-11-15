$(
  Statement-only formalization of the NTP4VC corpus artifact
  pearl/binomial_heap_BinomialHeap_mergeqtvc: the binomial-heap merge
  verification condition preserves the heap and rank invariants and combines
  the occurrence counts of two input forests. This file contains no proof.
$)

$[ lib/set.mm $]

$(
  U is the arbitrary inhabited source carrier elt, D is its total preorder,
  and T is the source inductive tree carrier. NTP4VCTreeMk is an injective
  tagged encoding of tree.mk; NTP4VCElem, NTP4VCChildren, and NTP4VCRank are
  its projections. Closure, exhaustiveness, and structural induction give T
  exactly the finite well-founded trees whose children are arbitrary finite
  words over T.

  L, H, O, R, B, and I represent le_roots, heaps, occ, has_order,
  binomial_tree, and inv. Their base and constructor equations are the
  complete source recursive definitions over SetMM words and the full integer
  domain ZZ. NTP4VCLink is the source link definition.

  NTP4VCMergeEntry expands the first nested list match. Cases in which either
  input is empty are True in the source and therefore impose no obligation;
  its guarded nonempty cases are exactly the three branches of the nested
  rank comparison. NTP4VCMergeResultAntecedent expands the second nested list
  match, retaining each recursive-result witness at its source-internal
  existential scope. The final assertion retains the result and element
  universal quantifiers. Its final $a declaration is Metamath's native
  unproved statement encoding; this database contains no $p proof declaration.
$)

$c
  NTP4VCTreeMk NTP4VCElem NTP4VCChildren NTP4VCRank NTP4VCLink
  NTP4VCMergeEntry NTP4VCMergeResultAntecedent
$.

ntp4vc-tree-mk-syntax
  $a class ( NTP4VCTreeMk A B C ) $.
ntp4vc-elem-syntax
  $a class ( NTP4VCElem A ) $.
ntp4vc-children-syntax
  $a class ( NTP4VCChildren A ) $.
ntp4vc-rank-syntax
  $a class ( NTP4VCRank A ) $.
ntp4vc-link-syntax
  $a class ( NTP4VCLink A B C ) $.

ntp4vc-merge-entry-syntax
  $a wff ( NTP4VCMergeEntry A B C D E F G H I ) $.
ntp4vc-merge-result-antecedent-syntax
  $a wff (
    NTP4VCMergeResultAntecedent A B C D E F G H I J
  ) $.

ntp4vc-tree-mk-def $a |- (
  NTP4VCTreeMk A B C
) = <. 1 , <. A , <. B , C >. >. >. $.

ntp4vc-elem-def $a |- ( NTP4VCElem A ) =
  ( 1st ` ( 2nd ` A ) ) $.

ntp4vc-children-def $a |- ( NTP4VCChildren A ) =
  ( 1st ` ( 2nd ` ( 2nd ` A ) ) ) $.

ntp4vc-rank-def $a |- ( NTP4VCRank A ) =
  ( 2nd ` ( 2nd ` ( 2nd ` A ) ) ) $.

ntp4vc-link-def $a |- ( NTP4VCLink A B C ) =
  if
  (
    <. ( NTP4VCElem A ) , ( NTP4VCElem B ) >. e. C ,
    (
      NTP4VCTreeMk
        ( NTP4VCElem A )
        ( <" B "> ++ ( NTP4VCChildren A ) )
        ( ( NTP4VCRank A ) + 1 )
    ) ,
    (
      NTP4VCTreeMk
        ( NTP4VCElem B )
        ( <" A "> ++ ( NTP4VCChildren B ) )
        ( ( NTP4VCRank B ) + 1 )
    )
  ) $.

${
  $d o q s x y z A B C D E F G H I $.

  $(
    A=h1, B=h2, C=tree, D=elt, E=le, F=heaps, G=occ,
    H=binomial_tree, and I=inv.
  $)
  ntp4vc-merge-entry-def $a |- (
    ( NTP4VCMergeEntry A B C D E F G H I )
    <->
    A. x e. C A. q e. Word C A. y e. C A. s e. Word C
      (
        (
          B = ( <" x "> ++ q )
          /\
          A = ( <" y "> ++ s )
        )
        ->
        (
          (
            ( NTP4VCRank y ) < ( NTP4VCRank x )
            ->
            (
              s e. F
              /\
              (
                <. ( ( NTP4VCRank y ) + 1 ) , s >. e. I
                /\
                (
                  B e. F
                  /\
                  <. ( ( NTP4VCRank y ) + 1 ) , B >. e. I
                )
              )
            )
          )
          /\
          (
            (
              -.
              ( NTP4VCRank y ) < ( NTP4VCRank x )
              /\
              ( NTP4VCRank x ) < ( NTP4VCRank y )
            )
            ->
            (
              A e. F
              /\
              (
                <. ( ( NTP4VCRank x ) + 1 ) , A >. e. I
                /\
                (
                  q e. F
                  /\
                  <. ( ( NTP4VCRank x ) + 1 ) , q >. e. I
                )
              )
            )
          )
          /\
          (
            (
              -.
              ( NTP4VCRank y ) < ( NTP4VCRank x )
              /\
              -.
              ( NTP4VCRank x ) < ( NTP4VCRank y )
            )
            ->
            (
              (
                s e. F
                /\
                (
                  <. ( ( NTP4VCRank y ) + 1 ) , s >. e. I
                  /\
                  (
                    q e. F
                    /\
                    <. ( ( NTP4VCRank y ) + 1 ) , q >. e. I
                  )
                )
              )
              /\
              A. o e. Word C
                (
                  (
                    o e. F
                    /\
                    (
                      <. ( ( NTP4VCRank y ) + 1 ) , o >. e. I
                      /\
                      A. z e. D
                        (
                          G ` <. z , o >.
                        )
                        =
                        (
                          ( G ` <. z , s >. )
                          +
                          ( G ` <. z , q >. )
                        )
                    )
                  )
                  ->
                  (
                    <" ( NTP4VCLink y x E ) "> e. F
                    /\
                    (
                      ( NTP4VCLink y x E ) e. H
                      /\
                      (
                        o e. F
                        /\
                        <.
                          ( NTP4VCRank ( NTP4VCLink y x E ) ) ,
                          o
                        >. e. I
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
  $d o q s x y z A B C D E F G H I J $.

  $(
    A=result, B=h1, C=h2, D=tree, E=elt, F=le, G=heaps,
    H=occ, I=binomial_tree, and J=inv.
  $)
  ntp4vc-merge-result-antecedent-def $a |- (
    (
      NTP4VCMergeResultAntecedent A B C D E F G H I J
    )
    <->
    (
      (
        C = (/)
        /\
        A = B
      )
      \/
      E. x e. D E. q e. Word D
        (
          C = ( <" x "> ++ q )
          /\
          (
            (
              B = (/)
              /\
              A = C
            )
            \/
            E. y e. D E. s e. Word D
              (
                B = ( <" y "> ++ s )
                /\
                (
                  (
                    ( NTP4VCRank y ) < ( NTP4VCRank x )
                    /\
                    E. o e. Word D
                      (
                        (
                          o e. G
                          /\
                          (
                            <.
                              ( ( NTP4VCRank y ) + 1 ) ,
                              o
                            >. e. J
                            /\
                            A. z e. E
                              (
                                H ` <. z , o >.
                              )
                              =
                              (
                                ( H ` <. z , s >. )
                                +
                                ( H ` <. z , C >. )
                              )
                          )
                        )
                        /\
                        A = ( <" y "> ++ o )
                      )
                  )
                  \/
                  (
                    (
                      -.
                      ( NTP4VCRank y ) < ( NTP4VCRank x )
                      /\
                      ( NTP4VCRank x ) < ( NTP4VCRank y )
                    )
                    /\
                    E. o e. Word D
                      (
                        (
                          o e. G
                          /\
                          (
                            <.
                              ( ( NTP4VCRank x ) + 1 ) ,
                              o
                            >. e. J
                            /\
                            A. z e. E
                              (
                                H ` <. z , o >.
                              )
                              =
                              (
                                ( H ` <. z , B >. )
                                +
                                ( H ` <. z , q >. )
                              )
                          )
                        )
                        /\
                        A = ( <" x "> ++ o )
                      )
                  )
                  \/
                  (
                    (
                      -.
                      ( NTP4VCRank y ) < ( NTP4VCRank x )
                      /\
                      -.
                      ( NTP4VCRank x ) < ( NTP4VCRank y )
                    )
                    /\
                    E. o e. Word D
                      (
                        (
                          o e. G
                          /\
                          (
                            <.
                              ( ( NTP4VCRank y ) + 1 ) ,
                              o
                            >. e. J
                            /\
                            A. z e. E
                              (
                                H ` <. z , o >.
                              )
                              =
                              (
                                ( H ` <. z , s >. )
                                +
                                ( H ` <. z , q >. )
                              )
                          )
                        )
                        /\
                        (
                          A e. G
                          /\
                          (
                            <.
                              (
                                NTP4VCRank
                                  ( NTP4VCLink y x F )
                              ) ,
                              A
                            >. e. J
                            /\
                            A. z e. E
                              (
                                H ` <. z , A >.
                              )
                              =
                              (
                                (
                                  H ` <.
                                    z ,
                                    <" ( NTP4VCLink y x F ) ">
                                  >.
                                )
                                +
                                ( H ` <. z , o >. )
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
  $d c e k m o q r s t u x y z
     A B C D E F G H I J K L M N O P Q R S T U V W X Y Z $.

  $( Source carrier elt and its total preorder le. $)
  ntp4vc-element-carrier-nonempty $e |- U =/= (/) $.
  ntp4vc-le-relation $e |- D C_ ( U X. U ) $.
  ntp4vc-le-reflexive $e |- A. x e. U
    <. x , x >. e. D $.
  ntp4vc-le-transitive $e |- A. x e. U A. y e. U A. z e. U
    (
      (
        <. x , y >. e. D
        /\
        <. y , z >. e. D
      )
      ->
      <. x , z >. e. D
    ) $.
  ntp4vc-le-total $e |- A. x e. U A. y e. U
    (
      <. x , y >. e. D
      \/
      <. y , x >. e. D
    ) $.

  $(
    The source inductive tree type: constructor closure and exhaustiveness,
    plus its structural induction principle over all subsets of T.
  $)
  ntp4vc-tree-constructor-closure $e |- A. e e. U
    A. c e. Word T A. r e. ZZ
      ( NTP4VCTreeMk e c r ) e. T $.

  ntp4vc-tree-constructor-exhaustive $e |- A. t e. T
    E. e e. U E. c e. Word T E. r e. ZZ
      t = ( NTP4VCTreeMk e c r ) $.

  ntp4vc-tree-structural-induction $e |- A. s e. ~P T
    (
      A. e e. U A. c e. Word T A. r e. ZZ
        (
          ran c C_ s
          ->
          ( NTP4VCTreeMk e c r ) e. s
        )
      ->
      s = T
    ) $.

  $( Types of the six source recursive definitions used by the VC. $)
  ntp4vc-le-roots-relation
    $e |- L C_ ( U X. Word T ) $.
  ntp4vc-heaps-predicate
    $e |- H C_ Word T $.
  ntp4vc-occ-function
    $e |- O e. ( ZZ ^m ( U X. Word T ) ) $.
  ntp4vc-has-order-relation
    $e |- R C_ ( ZZ X. Word T ) $.
  ntp4vc-binomial-tree-predicate
    $e |- B C_ T $.
  ntp4vc-inv-relation
    $e |- I C_ ( ZZ X. Word T ) $.

  $( le_roots equations. $)
  ntp4vc-le-roots-empty $e |- A. e e. U
    <. e , (/) >. e. L $.

  ntp4vc-le-roots-cons $e |- A. e e. U A. u e. U
    A. c e. Word T A. r e. ZZ A. q e. Word T
      (
        <.
          e ,
          (
            <" ( NTP4VCTreeMk u c r ) ">
            ++
            q
          )
        >. e. L
        <->
        (
          <. e , u >. e. D
          /\
          <. e , q >. e. L
        )
      ) $.

  $( heaps equations. $)
  ntp4vc-heaps-empty $e |- (/) e. H $.

  ntp4vc-heaps-cons $e |- A. e e. U A. c e. Word T
    A. r e. ZZ A. q e. Word T
      (
        (
          <" ( NTP4VCTreeMk e c r ) ">
          ++
          q
        ) e. H
        <->
        (
          <. e , c >. e. L
          /\
          ( c e. H /\ q e. H )
        )
      ) $.

  $( occ equations, with integer-valued occurrence counts. $)
  ntp4vc-occ-empty $e |- A. x e. U
    ( O ` <. x , (/) >. ) = 0 $.

  ntp4vc-occ-cons $e |- A. x e. U A. e e. U
    A. c e. Word T A. r e. ZZ A. q e. Word T
      (
        O ` <.
          x ,
          (
            <" ( NTP4VCTreeMk e c r ) ">
            ++
            q
          )
        >.
      )
      =
      (
        (
          if ( x = e , 1 , 0 )
          +
          ( O ` <. x , c >. )
        )
        +
        ( O ` <. x , q >. )
      ) $.

  $( has_order equations. $)
  ntp4vc-has-order-empty $e |- A. k e. ZZ
    (
      <. k , (/) >. e. R
      <->
      k = 0
    ) $.

  ntp4vc-has-order-cons $e |- A. k e. ZZ A. e e. U
    A. c e. Word T A. r e. ZZ A. q e. Word T
      (
        <.
          k ,
          (
            <" ( NTP4VCTreeMk e c r ) ">
            ++
            q
          )
        >. e. R
        <->
        (
          r = ( k - 1 )
          /\
          (
            <. ( k - 1 ) , c >. e. R
            /\
            <. ( k - 1 ) , q >. e. R
          )
        )
      ) $.

  $( binomial_tree equation. $)
  ntp4vc-binomial-tree-def $e |- A. e e. U
    A. c e. Word T A. r e. ZZ
      (
        ( NTP4VCTreeMk e c r ) e. B
        <->
        (
          r = ( # ` c )
          /\
          <. r , c >. e. R
        )
      ) $.

  $( inv equations. $)
  ntp4vc-inv-empty $e |- A. m e. ZZ
    <. m , (/) >. e. I $.

  ntp4vc-inv-cons $e |- A. m e. ZZ A. e e. U
    A. c e. Word T A. r e. ZZ A. q e. Word T
      (
        <.
          m ,
          (
            <" ( NTP4VCTreeMk e c r ) ">
            ++
            q
          )
        >. e. I
        <->
        (
          m <_ r
          /\
          (
            ( NTP4VCTreeMk e c r ) e. B
            /\
            <. ( r + 1 ) , q >. e. I
          )
        )
      ) $.

  $( Source theorem parameters A=h1, K=k, J=h2, followed by fact0--fact3. $)
  ntp4vc-h1-word $e |- A e. Word T $.
  ntp4vc-k-integer $e |- K e. ZZ $.
  ntp4vc-h2-word $e |- J e. Word T $.
  ntp4vc-fact0 $e |- A e. H $.
  ntp4vc-fact1 $e |- <. K , A >. e. I $.
  ntp4vc-fact2 $e |- J e. H $.
  ntp4vc-fact3 $e |- <. K , J >. e. I $.

  ntp4vc-pearl-binomial-heap-merge-vc $a |- (
    ( NTP4VCMergeEntry A J T U D H O B I )
    /\
    A. o e. Word T
      (
        (
          NTP4VCMergeResultAntecedent
            o A J T U D H O B I
        )
        ->
        (
          o e. H
          /\
          (
            <. K , o >. e. I
            /\
            A. x e. U
              (
                O ` <. x , o >.
              )
              =
              (
                ( O ` <. x , A >. )
                +
                ( O ` <. x , J >. )
              )
          )
        )
      )
  ) $.
$}
