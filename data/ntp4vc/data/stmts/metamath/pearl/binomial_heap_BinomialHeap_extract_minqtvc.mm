$(
  Statement-only formalization of the NTP4VC corpus artifact
  pearl/binomial_heap_BinomialHeap_extract_minqtvc: the binomial-heap
  extract-min verification condition preserves the heap and rank invariants
  while removing one occurrence of a selected minimum root and preserving all
  other element occurrences. This file contains no proof.
$)

$[ lib/set.mm $]

$(
  U is the arbitrary inhabited source carrier elt, D is its total preorder,
  and T is the source inductive tree carrier. NTP4VCTreeMk is an injective
  tagged encoding of tree.mk; NTP4VCElem, NTP4VCChildren, and NTP4VCRank are
  its three projections. Closure, exhaustiveness, and structural induction
  give T exactly the finite well-founded trees whose children are arbitrary
  finite words over T, rather than a finite approximation or an uninterpreted
  collection of tags.

  L, H, O, R, B, and I represent le_roots, heaps, occ, has_order,
  binomial_tree, and inv. Their base and constructor equations below are the
  complete source recursive definitions over SetMM words and the full integer
  domain ZZ. Thus the externally named recursive operations are uniquely
  determined by structural recursion and do not add mathematical premises.

  NTP4VCReverse is the exact reversal of a finite zero-based SetMM word. The
  final assertion repeats the three source hypotheses and retains the selected
  tree, residual heap, merged heap, and element quantifiers at their original
  internal scopes. The final $a declaration is Metamath's native unproved
  statement encoding; this database contains no $p proof declaration.
$)

$c
  NTP4VCTreeMk NTP4VCElem NTP4VCChildren NTP4VCRank NTP4VCReverse
$.

ntp4vc-tree-mk-syntax
  $a class ( NTP4VCTreeMk A B C ) $.
ntp4vc-elem-syntax
  $a class ( NTP4VCElem A ) $.
ntp4vc-children-syntax
  $a class ( NTP4VCChildren A ) $.
ntp4vc-rank-syntax
  $a class ( NTP4VCRank A ) $.
ntp4vc-reverse-syntax
  $a class ( NTP4VCReverse A ) $.

ntp4vc-tree-mk-def $a |- (
  NTP4VCTreeMk A B C
) = <. 1 , <. A , <. B , C >. >. >. $.

ntp4vc-elem-def $a |- ( NTP4VCElem A ) =
  ( 1st ` ( 2nd ` A ) ) $.

ntp4vc-children-def $a |- ( NTP4VCChildren A ) =
  ( 1st ` ( 2nd ` ( 2nd ` A ) ) ) $.

ntp4vc-rank-def $a |- ( NTP4VCRank A ) =
  ( 2nd ` ( 2nd ` ( 2nd ` A ) ) ) $.

${
  $d i A $.

  ntp4vc-reverse-def $a |- ( NTP4VCReverse A ) =
    (
      i e. ( 0 ..^ ( # ` A ) ) |->
      (
        A `
        ( ( ( # ` A ) - 1 ) - i )
      )
    ) $.
$}

${
  $d c e g h i j k m q r s t u v x y z
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

  $( Source theorem parameter A=h, followed by fact0--fact2. $)
  ntp4vc-h-word $e |- A e. Word T $.
  ntp4vc-fact0 $e |- A e. H $.
  ntp4vc-fact1 $e |- <. 0 , A >. e. I $.
  ntp4vc-fact2 $e |- A =/= (/) $.

  ntp4vc-pearl-binomial-heap-extract-min-vc $a |- (
    A e. H
    /\
    (
      <. 0 , A >. e. I
      /\
      (
        A =/= (/)
        /\
        A. t e. T A. q e. Word T
          (
            (
              <" t "> e. H
              /\
              (
                q e. H
                /\
                (
                  <. 0 , q >. e. I
                  /\
                  (
                    <. ( NTP4VCElem t ) , A >. e. L
                    /\
                    (
                      t e. B
                      /\
                      A. x e. U
                        (
                          O ` <. x , A >.
                        )
                        =
                        (
                          (
                            O ` <. x , <" t "> >.
                          )
                          +
                          ( O ` <. x , q >. )
                        )
                    )
                  )
                )
              )
            )
            ->
            (
              (
                ( NTP4VCReverse ( NTP4VCChildren t ) ) e. H
                /\
                (
                  <.
                    0 ,
                    ( NTP4VCReverse ( NTP4VCChildren t ) )
                  >. e. I
                  /\
                  (
                    q e. H
                    /\
                    <. 0 , q >. e. I
                  )
                )
              )
              /\
              A. s e. Word T
                (
                  (
                    s e. H
                    /\
                    (
                      <. 0 , s >. e. I
                      /\
                      A. x e. U
                        (
                          O ` <. x , s >.
                        )
                        =
                        (
                          (
                            O ` <.
                              x ,
                              (
                                NTP4VCReverse
                                  ( NTP4VCChildren t )
                              )
                            >.
                          )
                          +
                          ( O ` <. x , q >. )
                        )
                    )
                  )
                  ->
                  (
                    s e. H
                    /\
                    (
                      <. 0 , s >. e. I
                      /\
                      (
                        (
                          O ` <. ( NTP4VCElem t ) , s >.
                        )
                        =
                        (
                          (
                            O ` <. ( NTP4VCElem t ) , A >.
                          )
                          -
                          1
                        )
                        /\
                        A. x e. U
                          (
                            x =/= ( NTP4VCElem t )
                            ->
                            (
                              O ` <. x , s >.
                            )
                            =
                            (
                              O ` <. x , A >.
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
